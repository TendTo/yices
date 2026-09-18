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

bool is_below_lb(simplex_solver_t *solver, thvar_t x, xrational_t *value);
bool is_above_ub(simplex_solver_t *solver, thvar_t x, xrational_t *value);

xrational_t *get_lb(simplex_solver_t *solver, thvar_t x);
xrational_t *get_ub(simplex_solver_t *solver, thvar_t x);

void copy_to_gmp(const rational_t *r, mpq_t val);
void init_and_copy_to_gmp(const rational_t *r, mpq_t uninitialized_val);

void mpq_vector_clear(mpq_t v[], int n);

bool simplex_check_feasibility_external(simplex_solver_t *solver);

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
 * Its value is external-solver-dependent.
 * @param inf a pointer to the positive infinity mpq_t.
 * Its value is external-solver-dependent.
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

// TODO: REMOVE ALL DEBUG PRINTS
inline void print_int_vector(const int32_t v[], const int n, const char *name) {
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

inline void print_mpq_vector(const mpq_t v[], const int n, const char *name) {
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

inline void print_rational_vector(const rational_t v[], const int n,
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

inline void print_xrational_vector(xrational_t v[], const int n,
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

inline void print_char_vector(const char v[], const int n, const char *name) {
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

inline void print_external_solution(const external_solution_t *sol) {
  printf("external_solution_t {\n");
  switch (sol->status) {
  case EXTERNAL_SIMPLEX_FEASIBLE:
    printf("  status: OPTIMAL\n");
    break;
  case EXTERNAL_SIMPLEX_UNBOUNDED:
    printf("  status: UNBOUNDED\n");
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
  printf("}\n");
  printf("basic vars: %d\n", sol->nb_vars);
  for (uint32_t i = 0; i < sol->nb_vars; i++) {
    printf("%d ", sol->basic_vars[i]);
  }
  printf("\n");
}

#endif
