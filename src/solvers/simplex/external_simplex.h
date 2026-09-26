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

bool has_lb(const simplex_solver_t *solver, thvar_t v);
bool has_ub(const simplex_solver_t *solver, thvar_t v);

bool has_any_bound(const simplex_solver_t *solver, thvar_t v);
bool has_strict_lb(const simplex_solver_t *solver, thvar_t v);
bool has_strict_ub(const simplex_solver_t *solver, thvar_t v);

bool is_below_or_eq_lb(simplex_solver_t *solver, thvar_t x, xrational_t *value);
bool is_above_or_eq_ub(simplex_solver_t *solver, thvar_t x, xrational_t *value);

xrational_t *get_lb(simplex_solver_t *solver, thvar_t x);
xrational_t *get_ub(simplex_solver_t *solver, thvar_t x);

void init_and_copy_to_gmp(mpq_t dest, const rational_t *src);
void copy_to_gmp(mpq_t dest, const rational_t *src);
void mpq_q_sub(mpq_t dest, mpq_t a, const rational_t *b);
void mpq_q_mul(mpq_t dest, mpq_t a, const rational_t *b);

void mpq_vector_clear(mpq_t v[], int n);

external_simplex_status_t
simplex_check_feasibility_external(simplex_solver_t *solver);

bool is_strict_var_zero(mpq_t x);

/**
 * Obtain a pointer to a bound in terms of mpq_t.
 * The value returned depends on some parameters:
 * - If has_bound is false, the bound is either +infinity or -infinity,
 *   based on the is_lb parameter.
 *   Its value is a pointer to either mpq_INFTY or mpq_NINFTY.
 * - If has_bound is true, the bound is the value of val, possibly adjusted
 *   based on the is_strict parameter.
 *   Since val is a rational_t, it may be stored in a temporary mpq_t if it is
 *   not already a GMP rational. The used_temp parameter indicates whether a
 *   temporary allocation was used.
 * @param bound the value of bound,
 * including whether it is a lower or upper bound, and whether it is strict.
 * @param ninf a pointer to the negative infinity mpq_t.
 * Its value is external-lp-solver-dependent.
 * @param inf a pointer to the positive infinity mpq_t.
 * Its value is external-lp-solver-dependent.
 * @param[out] used_temp whether a temporary allocation was used.
 * If true, the caller is responsible for clearing the temporary mpq_t after
 * use.
 * @param[out] temp a temporary mpq_t.
 * It may be initialized and be pointed by the returned mpq_ptr.
 * If that happens, the caller is responsible for clearing it after use.
 * @return a pointer to the bound
 */
void get_bound(const simplex_solver_t *solver, thvar_t v, bool is_lower_bound,
               bound_type_t *bound);
void get_bound_copy(const simplex_solver_t *solver, thvar_t v,
                    bool is_lower_bound, bound_type_t *bound);

external_import_status_t import_external_solution(simplex_solver_t *solver,
                                                  external_solution_t *sol);

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
}

static inline void print_int_heap(const int_heap_t *heap) {
  if (heap == NULL) {
    printf("int_heap: NULL\n");
    return;
  }
  printf("int_heap: [");
  for (uint32_t i = 1; i < heap->size; i++) {
    printf("%d", heap->heap[i]);
    if (i < heap->size - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

#endif
