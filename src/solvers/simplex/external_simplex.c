/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */
#include "external_simplex.h"

#include "frontend/smt2/smt2_commands.h"
#include "solvers/egraph/egraph_base_types.h"
#include "solvers/simplex/external_qsoptex.h"
#include "solvers/simplex/external_soplex.h"
#include "solvers/simplex/matrices.h"
#include "solvers/simplex/simplex.h"
#include "solvers/simplex/simplex_printer.h"
#include "solvers/simplex/simplex_types.h"
#include "solvers/simplex/simplex_utils.h"
#include "terms/rationals.h"

#include <inttypes.h>

#include "io/tracer.h"
#include "terms/mpq_stores.h"
#include "utils/bitvectors.h"

#include <assert.h>

external_solution_t new_external_solution(const uint32_t nvars) {
  external_solution_t sol;
  external_solution_init(&sol, nvars);
  return sol;
}

void external_solution_init(external_solution_t *sol, const uint32_t nvars) {
  sol->status = EXTERNAL_SIMPLEX_ERROR;
  sol->infeasible_var = null_thvar;
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

void mpq_set_q(mpq_t dest, const rational_t *const src) {
  if (is_ratgmp(src)) {
    mpq_set(dest, get_gmp(src));
  } else {
    mpq_set_int32(dest, get_num(src), get_den(src));
  }
}

void mpq_sub_q(mpq_t dest, mpq_t a, const rational_t *const b) {
  if (is_ratgmp(b)) {
    mpq_sub(dest, a, get_gmp(b));
  } else {
    mpq_set(dest, a);
    mpq_sub_si(dest, get_num(b), get_den(b));
  }
}

void mpq_mul_q(mpq_t dest, mpq_t a, const rational_t *const b) {
  if (is_ratgmp(b)) {
    mpq_mul(dest, a, get_gmp(b));
  } else {
    mpq_set(dest, a);
    mpq_mul_si(dest, get_num(b), get_den(b));
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
      // We are dealing with a free variable.
      // Just assign it the value from the solution.
      // In SoPlex, a variable made free by moving its strict bounds
      // to the constraints may be set to Zero
      // assert(!has_any_bound(solver, v));
      update_non_basic_var_value(solver, v, sol->x + v);
    }
  }
}

static void sync_infeasible_vars(simplex_solver_t *const solver) {
  reset_int_heap(&solver->infeasible_vars);

  for (uint32_t i = 0; i < solver->matrix.nrows; i++) {
    const thvar_t x = matrix_basic_var(&solver->matrix, i);
    if (!value_satisfies_bounds(solver, x)) {
      assert(matrix_is_basic_var(&solver->matrix, x));
      int_heap_add(&solver->infeasible_vars, x);
    }
  }
}

static void sync_infeasible_vars_non_basic(simplex_solver_t *const solver,
                                           const thvar_t v) {
  assert(v > const_idx);
  assert(matrix_is_nonbasic_var(&solver->matrix, v));
  // Remove variables that have now been satisfied by the pivot
  // from the infeasible heap.
  // Adding infeasible ones is handled by the matrix_pivot method.
  const column_t *const col = matrix_column(&solver->matrix, v);
  for (uint32_t i = 0; i < col->size; i++) {
    const thvar_t b = matrix_basic_var(&solver->matrix, col->data[i].r_idx);
    assert(b != null_thvar);
    if (b > const_idx && value_satisfies_bounds(solver, b)) {
      int_heap_remove(&solver->infeasible_vars, b);
    }
  }
  // Also, ensure that v is not in the infeasible heap,
  // since it is now non-basic and at a bound
  assert(value_satisfies_bounds(solver, v));
  int_heap_remove(&solver->infeasible_vars, v);
}

static void simplex_clear_bound_flags(simplex_solver_t *solver, thvar_t x) {
  uint8_t t;

  assert(!variable_at_lower_bound(solver, x) &&
         !variable_at_upper_bound(solver, x));

  t = arith_var_tag(&solver->vtbl, x);
  t &= ~(AVARTAG_ATLB_MASK | AVARTAG_ATUB_MASK); // clear both bits
  set_arith_var_tag(&solver->vtbl, x, t);
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
    trace_printf(solver->core->trace, 10, "No valid pivot found in row %d\n",
                 r);
    return false;
  }

  // make the variable of index best_i the basic variable for r
  matrix_pivot(matrix, r, best_i);

  switch (sol->bounds[v]) {
  case VAR_BOUND_AT_LOWER:
    update_to_lower_bound(solver, v);
    assert(value_satisfies_bounds(solver, v));
    assert(variable_at_lower_bound(solver, v));
    return true;
  case VAR_BOUND_AT_UPPER:
    update_to_upper_bound(solver, v);
    assert(value_satisfies_bounds(solver, v));
    assert(variable_at_upper_bound(solver, v));
    return true;
  case VAR_BOUND_UNKNOWN:
    // If we are dealing with a free variable, just assign it the value from sol
    assert(!has_any_bound(solver, v) || xq_is_zero(sol->x + v));
    update_non_basic_var_value(solver, v, sol->x + v);
    simplex_clear_bound_flags(solver, v);
    assert(value_satisfies_bounds(solver, v));
    return true;
  }
  return false;
}

static inline bool is_conflict(simplex_solver_t *const solver,
                               const thvar_t v) {
  assert(!value_satisfies_bounds(solver, v));
  assert(matrix_is_basic_var(&solver->matrix, v));

  matrix_t *const matrix = &solver->matrix;
  const int32_t r = matrix_basic_row(matrix, v);
  row_t *const row = matrix_row(matrix, r);
  assert(row);

  if (variable_below_lower_bound(solver, v)) {
    // find an entering variable that allows x to increase
    return find_entering_var_for_increase(solver, row, v) < 0;
  }

  assert(variable_above_upper_bound(solver, v));
  // find an entering variable that allows x to decrease
  return find_entering_var_for_decrease(solver, row, v) < 0;
}

static inline thvar_t check_infeasible(simplex_solver_t *const solver) {
  int_heap_t *const infeas_vars = &solver->infeasible_vars;
  if (int_heap_is_empty(infeas_vars))
    return null_thvar;

  // There is no specific set of variables to check,
  // so we will check all the infeasible ones
  for (uint32_t i = 1; i <= infeas_vars->nelems; i++) {
    const thvar_t v = infeas_vars->heap[i];
    if (is_conflict(solver, v)) {
      return v;
    }
  }

  return null_thvar;
}

static inline thvar_t
check_infeasible_non_basic(simplex_solver_t *const solver,
                           const column_t *const non_basic_col) {
  int_heap_t *const infeas_vars = &solver->infeasible_vars;
  if (int_heap_is_empty(infeas_vars))
    return null_thvar;

  assert(non_basic_col);
  // Instead of checking all the infeasible variables,
  // we will check only the ones in the basic row
  for (uint32_t i = 0; i < non_basic_col->size; i++) {
    const int32_t r = non_basic_col->data[i].r_idx;
    const thvar_t v = matrix_basic_var(&solver->matrix, r);
    assert(v != null_thvar);
    assert(matrix_is_basic_var(&solver->matrix, v));
    if (int_heap_member(infeas_vars, v) && is_conflict(solver, v)) {
      assert(!value_satisfies_bounds(solver, v));
      return v;
    }
  }

  return null_thvar;
}

static inline external_import_status_t
import_external_solution(simplex_solver_t *const solver,
                         external_solution_t *const sol) {
  assert(solver);
  assert(sol);

  int_bvset_t *const new_nb = &sol->nb_vars;
  matrix_t *const matrix = &solver->matrix;
  const arith_vartable_t *const vtbl = &solver->vtbl;

  // printf("\n\n*** INITIAL ***\n");
  // print_simplex_vars_summary(stdout, solver);

  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    // Only update non-basic variables,
    // hoping to get a feasible solution immediately
    if (matrix_is_nonbasic_var(matrix, v) && int_bvset_member(new_nb, v)) {
      update_nb_value(solver, sol, v);
      assert(value_satisfies_bounds(solver, v));
    }
  }

  sync_infeasible_vars(solver);
  if (sol->status == EXTERNAL_SIMPLEX_INFEASIBLE) {
    sol->infeasible_var = check_infeasible(solver);
    if (sol->infeasible_var != null_thvar) {
      return EXTERNAL_IMPORT_INFEASIBLE;
    }
  }

#ifndef NDEBUG
  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    if (matrix_is_nonbasic_var(matrix, v) && int_bvset_member(new_nb, v)) {
      assert(value_satisfies_bounds(solver, v));
      assert(variable_at_lower_bound(solver, v) ||
             variable_at_upper_bound(solver, v) || !has_any_bound(solver, v) ||
             xq_is_zero(arith_var_value(&solver->vtbl, v)));
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

  bool performed_pivot = true;
  while (n_missing_nb_vars > 0 &&
         !int_heap_is_empty(&solver->infeasible_vars) && performed_pivot) {
    performed_pivot = false;

    // Go over all variables that we need to add to the basis
    for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
      if (!int_bvset_member(&missing_nb_vars, v)) {
        continue;
      }
      assert(matrix_is_basic_var(matrix, v));

      // Get the basic row
      if (alignment_pivot(solver, sol, v)) {
        // A pivot has been performed.
        // v is now non-basic and can be removed from the set
        assert(matrix_is_nonbasic_var(matrix, v));
        sync_infeasible_vars_non_basic(solver, v);
        if (sol->status == EXTERNAL_SIMPLEX_INFEASIBLE) {
          sol->infeasible_var =
              check_infeasible_non_basic(solver, matrix_column(matrix, v));
          if (sol->infeasible_var != null_thvar) {
            delete_int_bvset(&missing_nb_vars);
            return EXTERNAL_IMPORT_INFEASIBLE;
          }
        }
        int_bvset_remove(&missing_nb_vars, v);
        n_missing_nb_vars--;
        performed_pivot = true;
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

    if (int_heap_is_empty(&solver->infeasible_vars)) {
      delete_int_bvset(&missing_nb_vars);
      return EXTERNAL_IMPORT_FEASIBLE;
    }
  }

  delete_int_bvset(&missing_nb_vars);
  return EXTERNAL_IMPORT_INFEASIBLE;
}

static inline void
override_external_solution(simplex_solver_t *const solver,
                           const external_solution_t *const sol) {
  assert(solver);
  assert(sol->status == EXTERNAL_SIMPLEX_FEASIBLE);
  assert(__smt2_globals.delta >= 0.0);

  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    xq_set(arith_var_value(&solver->vtbl, v), sol->x + v);
  }
}

bool has_strict_lb(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  return lb_idx > -1 && !xq_is_rational(&solver->bstack.bound[lb_idx]);
}

bool has_strict_ub(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  return ub_idx > -1 && !xq_is_rational(&solver->bstack.bound[ub_idx]);
}

bool has_eq_bounds(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  if (lb_idx > -1 && ub_idx > -1) {
    return xq_eq(&solver->bstack.bound[lb_idx], &solver->bstack.bound[ub_idx]);
  }
  return false;
}

bool is_below_or_eq_lb(simplex_solver_t *const solver, const thvar_t x,
                       xrational_t *const value) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && xq_lt(value, solver->bstack.bound + k);
}

bool is_above_or_eq_ub(simplex_solver_t *const solver, const thvar_t x,
                       xrational_t *const value) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && xq_gt(value, solver->bstack.bound + k);
}

xrational_t *get_lb(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

xrational_t *get_ub(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

rational_t *get_lb_main(simplex_solver_t *const solver, const thvar_t x) {
  return has_lb(solver, x)
             ? &solver->bstack.bound[solver->vtbl.lower_index[x]].main
             : NULL;
}
rational_t *get_ub_main(simplex_solver_t *const solver, const thvar_t x) {
  return has_ub(solver, x)
             ? &solver->bstack.bound[solver->vtbl.upper_index[x]].main
             : NULL;
}

uint32_t matrix_get_n_nz(const matrix_t *const matrix) {
  uint32_t nnz = 0;
  for (uint32_t i = 0; i < matrix->nrows; i++) {
    const row_t *const row = matrix->row[i];
    if (row) {
      nnz += row->nelems;
    }
  }
  return nnz;
}

void mpq_vector_clear(mpq_t v[], const int n) {
  for (int i = 0; i < n; i++) {
    mpq_clear(v[i]);
  }
}

#if 0 && !defined(NDEBUG)
static void print_ctx_parameters() {
  const ctx_param_t *const params = &__smt2_globals.ctx_parameters;
  printf("CTX parameters:\n");
  printf("  arith_elim: %d\n", params->arith_elim);
  printf("  bvarith_elim: %d\n", params->bvarith_elim);
  printf("  eq_abstraction: %d\n", params->eq_abstraction);
  printf("  keep_ite: %d\n", params->keep_ite);
  printf("  splx_eager_lemmas: %d\n", params->splx_eager_lemmas);
  printf("  splx_periodic_icheck: %d\n", params->splx_periodic_icheck);
  printf("  flatten_or: %d\n", params->flatten_or);
  printf("  var_elim: %d\n", params->var_elim);
}
#endif

external_simplex_status_t
simplex_check_feasibility_external(simplex_solver_t *solver,
                                   thvar_t *const infeasible_var) {
  if (!solver->tableau_ready)
    return EXTERNAL_SIMPLEX_UNKNOWN;

  solver->stats.external_calls++;

#if 0 && !defined(NDEBUG)
  printf("\n\n*** SIMPLEX START ***\n");
  print_simplex_vars_summary(stdout, solver);
  printf("==== Pivots ====\n");
  printf("%d", solver->stats.num_pivots);
  printf("\n==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n");
#endif

  external_solution_t solution = new_external_solution(solver->vtbl.nvars);
  switch (__smt2_globals.external_lp_solver) {
  case EXTERNAL_LP_SOLVER_QSOPTEX:
    qsx_solve(solver, &solution);
    break;
  case EXTERNAL_LP_SOLVER_SOPLEX:
    spx_solve(solver, &solution);
    break;
  default:
    printf("Unknown external solver: %d\n", __smt2_globals.external_lp_solver);
    abort();
    break;
  }

#if 0 && !defined(NDEBUG)
  printf("\n==== Solution ====\n");
  print_external_solution(&solution);
#endif

  const external_simplex_status_t status = solution.status;
  if (status == EXTERNAL_SIMPLEX_FEASIBLE && __smt2_globals.delta >= 0) {
    override_external_solution(solver, &solution);
    external_solution_clear(&solution);
    return EXTERNAL_SIMPLEX_FEASIBLE;
  }

  switch (status) {
  case EXTERNAL_SIMPLEX_INFEASIBLE:
  case EXTERNAL_SIMPLEX_FEASIBLE:
    import_external_solution(solver, &solution);
    break;
  default:
    break;
  }

  if (infeasible_var) {
    *infeasible_var = solution.infeasible_var;
#if 1 && !defined(NDEBUG)
    printf("Infeasible variable: %d\n", solution.infeasible_var);
#endif
  }
#if 0 && !defined(NDEBUG)
  printf("\n\n*** SIMPLEX FINISHED ***\n");
  print_simplex_vars_summary(stdout, solver);
#endif
  external_solution_clear(&solution);
  return status;
}
