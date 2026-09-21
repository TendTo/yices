/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * simplex_utils class.
 */
#ifndef __SIMPLEX_UTILS_TYPES_H
#define __SIMPLEX_UTILS_TYPES_H

#include "solvers/egraph/egraph_types.h"
#include "solvers/simplex/simplex_types.h"

/*
 * Check whether value v is between the bounds on x
 */
static inline bool value_ge_lower_bound(simplex_solver_t *solver, thvar_t x,
                                        xrational_t *v) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k < 0 || xq_ge(v, solver->bstack.bound + k);
}

static inline bool value_le_upper_bound(simplex_solver_t *solver, thvar_t x,
                                        xrational_t *v) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k < 0 || xq_le(v, solver->bstack.bound + k);
}

static inline bool value_within_bounds(simplex_solver_t *solver, thvar_t x,
                                       xrational_t *v) {
  return value_ge_lower_bound(solver, x, v) &&
         value_le_upper_bound(solver, x, v);
}

/*
 * Check whether x is at its lower or upper bound
 */
static inline bool variable_at_lower_bound(simplex_solver_t *solver,
                                           thvar_t x) {
  int32_t k;

  k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 &&
         xq_eq(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

static inline bool variable_at_upper_bound(simplex_solver_t *solver,
                                           thvar_t x) {
  int32_t k;

  k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 &&
         xq_eq(solver->bstack.bound + k, arith_var_value(&solver->vtbl, x));
}

/*
 * Update the value of a non-basic variable x and propagate
 * to all basic variables that depend on x
 * - q = new value of x
 * - if a basic variable becomes infeasible, it's added to the heap
 */
static inline void update_non_basic_var_value(simplex_solver_t *solver,
                                              thvar_t x, xrational_t *q) {
  arith_vartable_t *vtbl;
  matrix_t *matrix;
  xrational_t *v, *delta;
  column_t *col;
  uint32_t i, n;
  int32_t r, k;
  thvar_t y;

  vtbl = &solver->vtbl;
  delta = &solver->delta;
  v = arith_var_value(vtbl, x); // current value of x

  assert(delta != q);

  xq_set(delta, q);
  xq_sub(delta, v); // delta = new value - old value
  xq_set(v, q);     // value[x] := q

  matrix = &solver->matrix;
  col = matrix->column[x];

  if (col != NULL) {
    n = col->size;
    for (i = 0; i < n; i++) {
      r = col->data[i].r_idx;
      if (r >= 0) {
        y = matrix_basic_var(matrix, r);
        v = arith_var_value(vtbl, y);
        k = col->data[i].r_ptr;
        xq_submul(v, delta, matrix_coeff(matrix, r, k));

        // add y to the heap if the new value is not within its bounds
        if (!value_within_bounds(solver, y, v)) {
          int_heap_add(&solver->infeasible_vars, y);
        }
      }
    }
  }
}

/*
 * Update the value of non-basic var x to its lower or upper bound
 */
static inline void update_to_lower_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  assert(matrix_is_nonbasic_var(&solver->matrix, x));
  k = arith_var_lower_index(&solver->vtbl, x);
  assert(k >= 0);
  update_non_basic_var_value(solver, x, solver->bstack.bound + k);
  set_arith_var_lb(&solver->vtbl, x);
  if (variable_at_upper_bound(solver, x)) {
    set_arith_var_ub(&solver->vtbl, x);
  } else {
    clear_arith_var_ub(&solver->vtbl, x);
  }
}

static inline void update_to_upper_bound(simplex_solver_t *solver, thvar_t x) {
  int32_t k;

  assert(matrix_is_nonbasic_var(&solver->matrix, x));
  k = arith_var_upper_index(&solver->vtbl, x);
  assert(k >= 0);
  update_non_basic_var_value(solver, x, solver->bstack.bound + k);
  set_arith_var_ub(&solver->vtbl, x);
  if (variable_at_lower_bound(solver, x)) {
    set_arith_var_lb(&solver->vtbl, x);
  } else {
    clear_arith_var_lb(&solver->vtbl, x);
  }
}

#endif // __SIMPLEX_UTILS_TYPES_H
