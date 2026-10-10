/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */

#ifndef __EXTERNAL_SIMPLEX_H
#define __EXTERNAL_SIMPLEX_H

#include "solvers/simplex/external_simplex_types.h"
#include "solvers/simplex/simplex_types.h"
#include "terms/extended_rationals.h"
#include "terms/rationals.h"
#include <gmp.h>
#include <stdbool.h>

external_solution_t new_external_solution(uint32_t nvars);
void external_solution_init(external_solution_t *sol, uint32_t nvars);
void external_solution_clear(external_solution_t *sol);

static inline bool has_lb(const simplex_solver_t *const solver,
                          const thvar_t v) {
  return solver->vtbl.lower_index[v] > -1;
}

static inline bool has_ub(const simplex_solver_t *const solver,
                          const thvar_t v) {
  return solver->vtbl.upper_index[v] > -1;
}

static inline bool has_any_bound(const simplex_solver_t *const solver,
                                 const thvar_t v) {
  return has_lb(solver, v) || has_ub(solver, v);
}

static inline bool has_both_bounds(const simplex_solver_t *const solver,
                                   const thvar_t v) {
  return has_lb(solver, v) && has_ub(solver, v);
}

bool has_eq_bounds(const simplex_solver_t *solver, thvar_t v);
bool has_strict_lb(const simplex_solver_t *solver, thvar_t v);
bool has_strict_ub(const simplex_solver_t *solver, thvar_t v);

bool is_below_or_eq_lb(simplex_solver_t *solver, thvar_t x, xrational_t *value);
bool is_above_or_eq_ub(simplex_solver_t *solver, thvar_t x, xrational_t *value);

xrational_t *get_lb(simplex_solver_t *solver, thvar_t x);
xrational_t *get_ub(simplex_solver_t *solver, thvar_t x);
rational_t *get_lb_main(simplex_solver_t *solver, thvar_t x);
rational_t *get_ub_main(simplex_solver_t *solver, thvar_t x);
uint32_t matrix_get_n_nz(const matrix_t *matrix);

static inline int num_strict_all_vars(const simplex_solver_t *const solver) {
  int count = 0;
  for (thvar_t v = 1; v < solver->vtbl.nvars; v++) {
    count += has_strict_lb(solver, v) + has_strict_ub(solver, v);
  }
  return count;
}

void mpq_set_q(mpq_t dest, const rational_t *src);
void mpq_sub_q(mpq_t dest, mpq_t a, const rational_t *b);
void mpq_mul_q(mpq_t dest, mpq_t a, const rational_t *b);

void mpq_vector_clear(mpq_t v[], int n);

/**
 * Determines whether a theory variable should be encoded as an auxiliary row in
 * the LP model.
 * We only care about polynomials that are not constants.
 * E.g., p := a.x or p := a.x + c, but not p := c, where c is a constant.
 * @param solver The simplex solver containing the variable table and bounds.
 * @param v The theory variable to inspect.
 * @return true if the variable is a polynomial-defined non-constant row; false
 * otherwise.
 */
static inline bool var_is_valid_row(simplex_solver_t *const solver,
                                    const thvar_t v) {
  if (!arith_var_def_is_poly(&solver->vtbl, v))
    return false;
  const polynomial_t *const p = arith_var_poly_def(&solver->vtbl, v);
  assert(p);
  return !(p->nterms == 1 && p->mono[0].var == const_idx) &&
         has_any_bound(solver, v);
}

/**
 * Determines whether a theory variable may be encoded as a structural column in
 * the LP model.
 * We only care about free variables, i.e., those that appear
 * in the SMT definition.
 * @param solver The simplex solver containing the variable table and bounds.
 * @param v The theory variable to inspect.
 * @return true if the variable is free; otherwise false.
 */
static inline bool var_is_valid_strict_column(simplex_solver_t *const solver,
                                              const thvar_t v) {
  if (arith_var_is_free(&solver->vtbl, v) &&
      (has_strict_lb(solver, v) || has_strict_ub(solver, v)))
    return true;
  return false;
}

external_simplex_status_t
simplex_check_feasibility_external(simplex_solver_t *solver,
                                   thvar_t *infeasible_var);

// TODO: REMOVE ALL DEBUG PRINTS
static inline void print_int_vector(const int32_t v[], const int n,
                                    const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    printf("%d", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static inline void print_mpq_vector(const mpq_t v[], const int n,
                                    const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    gmp_printf("%Qd", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static inline void print_rational_vector(const rational_t v[], const int n,
                                         const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    q_print(stdout, &v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static inline void print_xrational_vector(xrational_t v[], const int n,
                                          const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    xq_print(stdout, &v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static inline void print_char_vector(const char v[], const int n,
                                     const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    printf("%c", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static inline void print_external_solution(external_solution_t *sol) {
  printf("external_solution_t {\n");
  switch (sol->status) {
  case EXTERNAL_SIMPLEX_FEASIBLE:
    printf("  status: OPTIMAL\n");
    break;
  case EXTERNAL_SIMPLEX_INFEASIBLE:
    printf("  status: INFEASIBLE\n");
    break;
  case EXTERNAL_SIMPLEX_EXHAUSTED:
    printf("  status: EXHAUSTED\n");
    break;
  default:
    printf("  status: UNKNOWN\n");
    break;
  }
  printf("  nvars: %d\n", sol->nvars);
  print_xrational_vector(sol->x, (int)sol->nvars, "  x");
  int n = 0;
  for (uint32_t i = 0; i < sol->nvars; i++) {
    if (int_bvset_member(&sol->b_vars, i)) {
      printf("%d ", i);
      n++;
    }
  }
  printf("\nbasic vars: %d\n", n);
  n = 0;
  for (uint32_t i = 0; i < sol->nvars; i++) {
    if (int_bvset_member(&sol->nb_vars, i)) {
      printf("%d ", i);
      n++;
    }
  }
  printf("\nnon-basic vars: %d\n", n);
  printf("}\n");
  printf("  infeasible_var: %d\n", sol->infeasible_var);
}

static inline void print_int_heap(const int_heap_t *heap) {
  if (heap == NULL) {
    printf("int_heap: NULL\n");
    return;
  }
  printf("int_heap: [");
  for (uint32_t i = 0; i < heap->idx_size; i++) {
    if (int_heap_member(heap, i)) {
      printf(" x_%d", heap->heap[heap->idx[i]]);
    }
  }
  printf("]\n");
}

#endif
