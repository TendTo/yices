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
  sol->basic_vars = (thvar_t *)safe_malloc(nvars * sizeof(thvar_t));
  sol->nb_vars = 0;
  for (uint32_t i = 0; i < nvars; i++) {
    xq_init(sol->x + i);
  }
}

void external_solution_clear(external_solution_t *sol) {
  for (uint32_t i = 0; i < sol->nvars; i++) {
    xq_clear(sol->x + i);
  }
  sol->nvars = 0;
  sol->nb_vars = 0;
  free(sol->basic_vars);
  free(sol->x);
  sol->basic_vars = NULL;
  sol->x = NULL;
}

static void inplace_convert_to_gmp(rational_t *const r, mpq_t *const loc) {
  assert(loc);
  assert(!is_ratgmp(r));

  mpq_init(*loc);
  mpq_set_int32(*loc, get_num(r), get_den(r));
  set_ratgmp(r, *loc);
}

void copy_to_gmp(const rational_t *const r, mpq_t val) {
  if (is_ratgmp(r)) {
    mpq_set(val, get_gmp(r));
  } else {
    mpq_set_int32(val, get_num(r), get_den(r));
  }
}

void init_and_copy_to_gmp(const rational_t *const r, mpq_t uninitialized_val) {
  mpq_init(uninitialized_val);
  copy_to_gmp(r, uninitialized_val);
}

void get_bound(const simplex_solver_t *const solver, const thvar_t v,
               const bool is_lower_bound, bound_type_t *bound) {
  const int32_t bound_idx = is_lower_bound ? solver->vtbl.lower_index[v]
                                           : solver->vtbl.upper_index[v];
  xrational_t *bounds = solver->bstack.bound;
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
    mpq_init(bound->gmp_val);
    mpq_set_int32(bound->gmp_val, val->s.num, val->s.den);
  } else if (__smt2_globals.epsilon_mode && bound->is_strict) {
    // Need to use temp to adjust value with epsilon
    bound->free = true;
    mpq_init(bound->gmp_val);
    mpq_set(bound->gmp_val, get_gmp(val));
  }

  if (__smt2_globals.epsilon_mode && bound->is_strict) {
    // Adjust the bounds with epsilon
    if (is_lower_bound) {
      mpq_add(bound->gmp_val, bound->gmp_val, epsilon);
    } else {
      mpq_sub(bound->gmp_val, bound->gmp_val, epsilon);
    }
  }
}

bool has_lb(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  return lb_idx > -1;
}

bool has_ub(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  return ub_idx > -1;
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

bool simplex_check_feasibility_external(simplex_solver_t *solver) {
  if (!solver->tableau_ready)
    return true;

  printf("\n\n*** SIMPLEX START ***\n");
  // print_simplex_vars_summary(stdout, solver);
  printf("==== Pivots ====\n");
  printf("%d", solver->stats.num_pivots);
  printf("\n==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n");

  external_solution_t solution = new_external_solution(solver->vtbl.nvars);
  switch (__smt2_globals.external_solver) {
  case EXTERNAL_SOLVER_AUTO:
  case EXTERNAL_SOLVER_QSOPTEX:
    printf("Using QSopt_ex as external solver\n");
    qsx_solve(solver, &solution);
    break;
  case EXTERNAL_SOLVER_SOPLEX:
    printf("Using SoPlex as external solver\n");
    printf("SoPlex is not yet implemented, using QSopt_ex instead\n");
    break;
  default:
    printf("Unknown external solver: %d\n", __smt2_globals.external_solver);
    break;
  }

  printf("\n==== Solution ====\n");
  print_external_solution(&solution);
  external_solution_clear(&solution);

  return true;
}
