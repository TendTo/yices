/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */
#include "external_simplex.h"

#include "../egraph/egraph_base_types.h"
#include "frontend/smt2/smt2_commands.h"
#include "matrices.h"
#include "simplex.h"
#include "simplex_printer.h"
#include "simplex_types.h"
#include "solvers/simplex/external_qsoptex.h"
#include "solvers/simplex/simplex_utils.h"
#include "terms/rationals.h"

#include <inttypes.h>

#include "io/tracer.h"
#include "solvers/egraph/theory_explanations.h"
#include "solvers/simplex/integrality_constraints.h"
#include "solvers/simplex/simplex.h"
#include "terms/mpq_stores.h"
#include "terms/rational_hash_maps.h"
#include "utils/assert_utils.h"
#include "utils/bitvectors.h"
#include "utils/dep_tables.h"
#include "utils/dprng.h"
#include "utils/hash_functions.h"
#include "utils/int_hash_classes.h"

#include <assert.h>
#include <qsopt_ex/QSopt_ex.h>

static mpq_t epsilon;

external_solution_t new_external_solution(const uint32_t nvars) {
  external_solution_t sol;
  external_solution_init(&sol, nvars);
  return sol;
}

void external_solution_init(external_solution_t *sol, const uint32_t nvars) {
  sol->status = EXTERNAL_SIMPLEX_ERROR;
  sol->nvars = nvars;
  sol->x = (xrational_t *)safe_malloc(nvars * sizeof(xrational_t));
  sol->bounds =
      (var_bound_state_t *)safe_malloc(nvars * sizeof(var_bound_state_t));

  init_int_bvset(&sol->b_vars, nvars);
  init_int_bvset(&sol->nb_vars, nvars);
  for (uint32_t i = 0; i < nvars; i++) {
    xq_init(sol->x + i);
    sol->bounds[i] = VAR_BOUND_UNKNOWN;
  }
}

void external_solution_clear(external_solution_t *sol) {
  for (uint32_t i = 0; i < sol->nvars; i++) {
    xq_clear(sol->x + i);
  }
  sol->nvars = 0;
  delete_int_bvset(&sol->b_vars);
  delete_int_bvset(&sol->nb_vars);
  free(sol->x);
  sol->x = NULL;
  free(sol->bounds);
  sol->bounds = NULL;
}

void copy_to_gmp(mpq_t dest, const rational_t *const src) {
  if (is_ratgmp(src)) {
    mpq_set(dest, get_gmp(src));
  } else {
    mpq_set_int32(dest, get_num(src), get_den(src));
  }
}

void init_and_copy_to_gmp(mpq_t dest, const rational_t *const src) {
  mpq_init(dest);
  copy_to_gmp(dest, src);
}

void mpq_q_sub(mpq_t dest, mpq_t a, const rational_t *const b) {
  if (is_ratgmp(b)) {
    mpq_sub(dest, a, get_gmp(b));
  } else {
    mpq_set(dest, a);
    mpq_sub_si(dest, get_num(b), get_den(b));
  }
}

void mpq_q_mul(mpq_t dest, mpq_t a, const rational_t *const b) {
  if (is_ratgmp(b)) {
    mpq_mul(dest, a, get_gmp(b));
  } else {
    mpq_set(dest, a);
    mpq_mul_si(dest, get_num(b), get_den(b));
  }
}

void get_bound(const simplex_solver_t *const solver, const thvar_t v,
               const bool is_lower_bound, bound_type_t *bound) {
  const int32_t bound_idx = is_lower_bound ? solver->vtbl.lower_index[v]
                                           : solver->vtbl.upper_index[v];
  xrational_t *const bounds = solver->bstack.bound;
  assert(bound); // Bound must be non-null

  bound->free = false;
  bound->is_finite = bound_idx > -1;
  bound->is_strict =
      __smt2_globals.delta < 0 &&
      (bound->is_finite ? !xq_is_rational(&bounds[bound_idx]) : false);

  if (!bound->is_finite)
    return;

  assert(bound_idx >= 0 && bound_idx < solver->bstack.size);
  const rational_t *val = &bounds[bound_idx].main;

  if (is_rat32(val)) { // Need to convert to GMP
    bound->free = true;
    mpq_init(bound->val);
    mpq_set_int32(bound->val, get_num(val), get_den(val));
  } else if (__smt2_globals.epsilon_mode && bound->is_strict) {
    bound->free = true;
    mpq_init(bound->val);
    mpq_set(bound->val, get_gmp(val));
  } else {
    printf("Using existing GMP value for bound of variable %d\n", v);
    memcpy(bound->val, get_gmp(val), sizeof(mpq_t));
  }

  if (__smt2_globals.epsilon_mode && bound->is_strict) {
    // Adjust the bounds with epsilon
    if (is_lower_bound) {
      mpq_add(bound->val, bound->val, epsilon);
    } else {
      mpq_sub(bound->val, bound->val, epsilon);
    }
  }
}

static void update_nb_value(simplex_solver_t *const solver,
                            const external_solution_t *const sol,
                            const thvar_t v) {
  assert(matrix_is_nonbasic_var(&solver->matrix, v));
  switch (sol->bounds[v]) {
  case VAR_BOUND_AT_LOWER:
    if (!variable_at_lower_bound(solver, v)) {
      update_to_lower_bound(solver, v);
    }
    break;
  case VAR_BOUND_AT_UPPER:
    if (!variable_at_upper_bound(solver, v)) {
      update_to_upper_bound(solver, v);
    }
    break;
  default:
    if (!xq_eq(sol->x + v, arith_var_value(&solver->vtbl, v))) {
      // TODO: explore the possibility of breaking the invariant
      //  that non-basic variables are at a bound
      printf("ERROR: Variable %d has unknown bound\n", v);
      exit(1);
    }
  }
}

static void sync_infeasible_vars(simplex_solver_t *const solver) {
  // print_int_heap(&solver->infeasible_vars);
  reset_int_heap(&solver->infeasible_vars);

  for (uint32_t i = 0; i < solver->matrix.nrows; i++) {
    const thvar_t x = matrix_basic_var(&solver->matrix, i);
    if (!value_satisfies_bounds(solver, x)) {
      assert(matrix_is_basic_var(&solver->matrix, x));
      int_heap_add(&solver->infeasible_vars, x);
    }
  }
  // printf("Synced infeasible vars: ");
  // print_int_heap(&solver->infeasible_vars);
}

/*
 * Make the currently basic variable v with a non basic variable in its row,
 * making v non-basic and the new variable basic.
 * - v must be a basic variable
 */
static bool alignment_pivot(simplex_solver_t *const solver,
                            external_solution_t *const sol, const thvar_t v) {
  matrix_t *const matrix = &solver->matrix;
  const uint32_t r = matrix_basic_row(matrix, v);
  const row_t *const row0 = matrix->row[r];
  assert(matrix->row[r] == row0);
  assert(matrix_is_basic_var(matrix, v));

  uint32_t best_i = -1;
  uint32_t best_c = UINT32_MAX;

  // find the lower-cost variable to pivot
  for (uint32_t i = 0; i < row0->size; i++) {
    const int32_t x = row0->data[i].c_idx;
    if (x >= 0 && x != const_idx && int_bvset_member(&sol->b_vars, x)) {
      assert(matrix_is_nonbasic_var(matrix, x));
      const uint32_t c = matrix->column[x]->nelems;
      if (c < best_c) {
        best_c = c;
        best_i = i;
      }
    }
  }

  if (best_i == -1) {
    printf("No valid pivot found in row %d\n", r);
    return false;
  }

  // make the variable of index best_i the basic variable for r
  matrix_pivot(matrix, r, best_i);

  // Remove variables that have now been satisfied by the pivot
  // from the infeasible heap.
  // Adding infeasible ones is handled by the matrix_pivot method.
  const row_t *const row = matrix_row(matrix, r);
  for (uint32_t i = 0; i < row->size; i++) {
    const int32_t x = row->data[i].c_idx;
    if (x >= 0 && x != const_idx &&
        int_heap_member(&solver->infeasible_vars, x)) {
      if (value_satisfies_bounds(solver, x)) {
        int_heap_remove(&solver->infeasible_vars, x);
      }
    }
  }
  // Also, ensure that v is not in the infeasible heap,
  // since it is now non-basic and at a bound
  int_heap_remove(&solver->infeasible_vars, v);

  switch (sol->bounds[v]) {
  case VAR_BOUND_AT_LOWER:
    update_to_lower_bound(solver, v);
    assert(value_satisfies_bounds(solver, v));
    return true;
  case VAR_BOUND_AT_UPPER:
    update_to_upper_bound(solver, v);
    assert(value_satisfies_bounds(solver, v));
    return true;
  case VAR_BOUND_UNKNOWN:
    // If we are dealing with a free variable, just assign it the value from sol
    assert(!has_any_bound(solver, v));
    update_non_basic_var_value(solver, v, sol->x + v);
    assert(value_satisfies_bounds(solver, v));
    return true;
  }
  return false;
}

external_import_status_t
import_external_solution(simplex_solver_t *const solver,
                         external_solution_t *const sol) {
  assert(solver);
  assert(sol);

  int_bvset_t *const new_nb = &sol->nb_vars;
  matrix_t *const matrix = &solver->matrix;
  arith_vartable_t *const vtbl = &solver->vtbl;

  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    // Only update non-basic variables,
    // hoping to get a feasible solution immediately
    if (matrix_is_nonbasic_var(matrix, v) && int_bvset_member(new_nb, v)) {
      // TODO: should we violate the invariant that non-basic variables are at a
      // bound?
      update_nb_value(solver, sol, v);
      assert(value_satisfies_bounds(solver, v));
    }
  }

  sync_infeasible_vars(solver);

#ifndef NDEBUG
  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    if (matrix_is_nonbasic_var(matrix, v)) {
      assert(value_satisfies_bounds(solver, v));
      assert(variable_at_lower_bound(solver, v) ||
             variable_at_upper_bound(solver, v) || !has_any_bound(solver, v));
    } else if (matrix_is_basic_var(matrix, v)) {
      if (!value_satisfies_bounds(solver, v)) {
        assert(int_heap_member(&solver->infeasible_vars, v));
      } else {
        assert(!int_heap_member(&solver->infeasible_vars, v));
      }
    }
  }
#endif

  if (int_heap_is_empty(&solver->infeasible_vars)) {
    return EXTERNAL_IMPORT_FEASIBLE;
  }

  // The simple assignment was not enough, extended search is needed
  solver->stats.external_extended_search_count++;

  uint32_t n_missing_nb_vars = 0;
  int_bvset_t missing_nb_vars;
  init_int_bvset(&missing_nb_vars, vtbl->nvars);
  for (thvar_t v = 0; v < vtbl->nvars; v++) {
    // Add the values that are basic but must become non-basic to the set
    if (!matrix_is_nonbasic_var(matrix, v) && int_bvset_member(new_nb, v)) {
      int_bvset_add(&missing_nb_vars, v);
      n_missing_nb_vars++;
    }
  }

  while (n_missing_nb_vars > 0 &&
         !int_heap_is_empty(&solver->infeasible_vars)) {

    // Go over all variables that we need to add to the basis
    thvar_t v = 0;
    for (; v < solver->vtbl.nvars; v++) {
      if (!int_bvset_member(&missing_nb_vars, v)) {
        continue;
      }
      assert(matrix_is_basic_var(matrix, v));

      // Get the basic row
      if (alignment_pivot(solver, sol, v)) {
        // TODO: do we need to sync the infeasible vars here?
        sync_infeasible_vars(solver);
        // A pivot has been performed.
        // v is now non-basic and can be removed from the set
        // int_heap_remove(&solver->infeasible_vars, v);

        n_missing_nb_vars--;
        int_bvset_remove(&missing_nb_vars, v);
        break;
      }
    }

#ifndef NDEBUG
    int_heap_t infeasible_vars_check;
    init_int_heap(&infeasible_vars_check, solver->vtbl.nvars,
                  solver->vtbl.nvars);

    for (uint32_t i = 0; i < solver->matrix.nrows; i++) {
      const thvar_t x = matrix_basic_var(&solver->matrix, i);
      if (!value_satisfies_bounds(solver, x)) {
        int_heap_add(&infeasible_vars_check, x);
      }
    }

    for (uint32_t i = 0; i < solver->vtbl.nvars; i++) {
      assert(int_heap_member(&infeasible_vars_check, i) ==
             int_heap_member(&solver->infeasible_vars, i));
    }

    delete_int_heap(&infeasible_vars_check);
#endif

    for (uint32_t i = 0; i < solver->matrix.nrows; i++) {
      const thvar_t x = matrix_basic_var(&solver->matrix, i);
      if (!value_satisfies_bounds(solver, x)) {
        int_heap_add(&solver->infeasible_vars, x);
      }
    }

    if (int_heap_is_empty(&solver->infeasible_vars)) {
      delete_int_bvset(&missing_nb_vars);
      return EXTERNAL_IMPORT_FEASIBLE;
    }
  }

  delete_int_bvset(&missing_nb_vars);
  return EXTERNAL_IMPORT_UNKNOWN;
}

bool has_lb(const simplex_solver_t *const solver, const thvar_t v) {
  return solver->vtbl.lower_index[v] > -1;
}

bool has_ub(const simplex_solver_t *const solver, const thvar_t v) {
  return solver->vtbl.upper_index[v] > -1;
}

bool has_any_bound(const simplex_solver_t *const solver, const thvar_t v) {
  return has_lb(solver, v) || has_ub(solver, v);
}

bool has_strict_lb(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  return lb_idx > -1 && !xq_is_rational(&solver->bstack.bound[lb_idx]);
}

bool has_strict_ub(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  return ub_idx > -1 && !xq_is_rational(&solver->bstack.bound[ub_idx]);
}

bool is_below_lb(simplex_solver_t *const solver, const thvar_t x,
                 xrational_t *const value) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && xq_gt(solver->bstack.bound + k, value);
}

bool is_above_ub(simplex_solver_t *const solver, const thvar_t x,
                 xrational_t *const value) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && xq_lt(solver->bstack.bound + k, value);
}

xrational_t *get_lb(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

xrational_t *get_ub(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

void mpq_vector_clear(mpq_t v[], const int n) {
  for (int i = 0; i < n; i++) {
    mpq_clear(v[i]);
  }
}

bool is_strict_var_zero(mpq_t x) {
  return __smt2_globals.delta < 0 && __smt2_globals.epsilon_mode &&
         mpq_cmp_ui(x, 0, 1) == 0;
}

external_import_status_t
simplex_check_feasibility_external(simplex_solver_t *solver) {
  if (!solver->tableau_ready)
    return EXTERNAL_IMPORT_UNKNOWN;

  solver->stats.external_calls++;

  // printf("\n\n*** SIMPLEX START ***\n");
  // print_simplex_vars_summary(stdout, solver);
  // printf("==== Pivots ====\n");
  // printf("%d", solver->stats.num_pivots);
  // printf("\n==== Simplex variables ====\n");
  // print_simplex_vars(stdout, solver);
  // printf("\n==== Tableau ====\n");
  // print_simplex_matrix(stdout, solver);
  // printf("\n==== Bounds  ====\n");
  // print_simplex_bounds(stdout, solver);
  // printf("\n");

  external_solution_t solution = new_external_solution(solver->vtbl.nvars);
  switch (__smt2_globals.external_lp_solver) {
  case EXTERNAL_LP_SOLVER_QSOPTEX:
    // solver->stats.external_lp_solver = EXTERNAL_LP_SOLVER_QSOPTEX;
    qsx_solve(solver, &solution);
    break;
  case EXTERNAL_LP_SOLVER_SOPLEX:
    // solver->stats.external_lp_solver = EXTERNAL_LP_SOLVER_SOPLEX;
    printf("SoPlex is not yet implemented, using QSopt_ex instead\n");
    break;
  default:
    printf("Unknown external solver: %d\n", __smt2_globals.external_lp_solver);
    break;
  }

  // printf("\n==== Solution ====\n");
  // print_external_solution(&solution);
  const external_import_status_t status =
      import_external_solution(solver, &solution);
  external_solution_clear(&solution);

  return status;
}
