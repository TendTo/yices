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
  init_int_bvset(&sol->b_vars, nvars);
  init_int_bvset(&sol->nb_vars, nvars);
  for (uint32_t i = 0; i < nvars; i++) {
    xq_init(sol->x + i);
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
}

static void inplace_convert_to_gmp(rational_t *const r, mpq_t *const loc) {
  assert(loc);
  assert(!is_ratgmp(r));

  mpq_init(*loc);
  mpq_set_int32(*loc, get_num(r), get_den(r));
  set_ratgmp(r, *loc);
}

void copy_to_gmp(mpq_t dest, const rational_t *const src) {
  if (is_ratgmp(src)) {
    mpq_set(dest, get_gmp(src));
  } else {
    mpq_set_int32(dest, get_num(src), get_den(src));
  }
}

void sub_to_gmp(mpq_t dest, mpq_t src, const rational_t *const subtrahend) {
  if (is_ratgmp(subtrahend)) {
    mpq_sub(dest, src, get_gmp(subtrahend));
  } else {
    mpq_t temp;
    mpq_init(temp);
    mpq_set_int32(temp, get_num(subtrahend), get_den(subtrahend));
    mpq_sub(dest, src, temp);
    mpq_clear(temp);
  }
}

void init_and_copy_to_gmp(mpq_t dest, const rational_t *const src) {
  mpq_init(dest);
  copy_to_gmp(dest, src);
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

void import_external_solution(simplex_solver_t *solver,
                              external_solution_t *sol) {
  assert(solver);
  assert(sol);

  const int_bvset_t *const new_basis = &sol->b_vars;
  xrational_t *const new_values = sol->x;
  matrix_t *const matrix = &solver->matrix;
  arith_vartable_t *const vtbl = &solver->vtbl;

#if 0 // For debug
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(d_tableau.isBasic(b)){
      std::cout << "Variable " << b << " => ";
      if (d_variables.isAuxiliary(b))
        std::cout << d_variables.asNode(b).getName();
      else
        d_variables.printModel(b, std::cout);
      std::cout << " is basic" << std::endl;
    }
  }
#endif

  int_bvset_t missing_nb_vars;
  init_int_bvset(&missing_nb_vars, solver->vtbl.nvars);
  for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
    if (matrix_is_nonbasic_var(matrix, v)) {
      int_bvset_add(&missing_nb_vars, v);
    }
  }
  //
  // for (thvar_t v = 0; v < solver->vtbl.nvars; v++) {
  //   thvar_t currentlyNb = v;
  //   if (matrix_is_nonbasic_var(matrix, v)) {
  //     xrational_t *old_value = arith_var_value(vtbl, v);
  //     xrational_t *new_value = new_values + v;
  //     if (!xq_eq(new_value, old_value)) {
  //       printf("Updating variable %d from ", v);
  //       if (variable_at_upper_bound(solver, v)) {
  //         update_to_lower_bound(solver, v);
  //       } else if (variable_at_lower_bound(solver, v)) {
  //         update_to_upper_bound(solver, v);
  //       } else {
  //         printf("unknown bound\n");
  //         exit(1);
  //       }
  //     }
  //   }
  // }
  // d_errorSet.reduceToSignals();
  // d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);
  //
  // if (processSignals()) {
  //   Trace("arith::findModel") << "attemptSolution() early conflict" << endl;
  //   d_conflictVariables.purge();
  //   return Result::UNSAT;
  // } else if (d_errorSet.errorEmpty()) {
  //   Trace("arith::findModel") << "attemptSolution() fixed itself" << endl;
  //   return Result::SAT;
  // }
  //
  // // The simple assignment was not enough, extended search is needed
  // ++d_statistics.d_extendedSearch;
  //
  // while (!needsToBeAdded.empty() && !d_errorSet.errorEmpty()) {
  //   ArithVar toRemove = ARITHVAR_SENTINEL;
  //   ArithVar toAdd = ARITHVAR_SENTINEL;
  //   DenseSet::const_iterator i = needsToBeAdded.begin(),
  //                            i_end = needsToBeAdded.end();
  //   for (; toAdd == ARITHVAR_SENTINEL && i != i_end; ++i) {
  //     ArithVar v = *i;
  //
  //     Tableau::ColIterator colIter = d_tableau.colIterator(v);
  //     for (; !colIter.atEnd(); ++colIter) {
  //       const Tableau::Entry &entry = *colIter;
  //       Assert(entry.getColVar() == v);
  //       ArithVar b = d_tableau.rowIndexToBasic(entry.getRowIndex());
  //       if (!newBasis.isMember(b)) {
  //         toAdd = v;
  //
  //         bool favorBOverToRemove = (toRemove == ARITHVAR_SENTINEL) ||
  //                                   (matchesNewValue(newValues, toRemove) &&
  //                                    !matchesNewValue(newValues, b)) ||
  //                                   (d_tableau.basicRowLength(toRemove) >
  //                                    d_tableau.basicRowLength(b));
  //
  //         if (favorBOverToRemove) {
  //           toRemove = b;
  //         }
  //       }
  //     }
  //   }
  //   Assert(toRemove != ARITHVAR_SENTINEL);
  //   Assert(toAdd != ARITHVAR_SENTINEL);
  //
  //   Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;
  //
  //   d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);
  //
  //   Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" <<
  //   endl; needsToBeAdded.remove(toAdd);
  //
  //   bool conflict = processSignals();
  //   if (conflict) {
  //     d_errorSet.reduceToSignals();
  //     d_conflictVariables.purge();
  //
  //     return Result::UNSAT;
  //   }
  // }
  // Assert(d_conflictVariables.empty());
  //
  // if (d_errorSet.errorEmpty()) {
  //   return Result::SAT;
  // } else {
  //   d_errorSet.reduceToSignals();
  //   return Result::UNKNOWN;
  // }
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
