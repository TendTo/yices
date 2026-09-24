/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex_types class.
 */
#ifndef __EXTERNAL_SIMPLEX_TYPES_H
#define __EXTERNAL_SIMPLEX_TYPES_H

#include "solvers/egraph/egraph_base_types.h"
#include "terms/extended_rationals.h"
#include "terms/rationals.h"
#include "utils/int_bv_sets.h"

#include <stdbool.h>

typedef struct {
  bool free;      ///< If true, the mpq_t val needs to be cleared
  bool is_finite; ///< If true, the bound is finite
  bool is_strict; ///< If true, the bound is strict
  bool is_lb; ///< Whether the bound is a lower bound (1) or an upper bound (0)
  mpq_t val;  ///< The value of the bound, if it is finite.
  ///< If free is true, this needs to be cleared after use.
} bound_type_t;

typedef enum {
  EXTERNAL_SIMPLEX_FEASIBLE,
  EXTERNAL_SIMPLEX_ERROR,
  EXTERNAL_SIMPLEX_INFEASIBLE,
  EXTERNAL_SIMPLEX_EXHAUSTED,
  EXTERNAL_SIMPLEX_UNKNOWN,
} external_simplex_status_t;

typedef enum {
  EXTERNAL_IMPORT_FEASIBLE,
  EXTERNAL_IMPORT_INFEASIBLE,
  EXTERNAL_IMPORT_UNKNOWN,
} external_import_status_t;

typedef enum {
  VAR_BOUND_UNKNOWN = 0,
  VAR_BOUND_AT_LOWER,
  VAR_BOUND_AT_UPPER
} var_bound_state_t;

typedef struct {
  external_simplex_status_t status;
  xrational_t *x;
  var_bound_state_t *bounds;
  uint32_t nvars;
  int_bvset_t b_vars;
  int_bvset_t nb_vars;
} external_solution_t;

static inline void bound_type_clear(bound_type_t *bound) {
  if (bound->free) {
    mpq_clear(bound->val);
    bound->free = false;
  }
}

#endif // __EXTERNAL_SIMPLEX_TYPES_H
