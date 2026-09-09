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
#include <stdbool.h>

typedef struct {
  bool is_finite;
  bool is_strict;
  bool is_lb;
  rational_t val;
} bound_type_t;

typedef enum {
  EXTERNAL_SIMPLEX_FEASIBLE,
  EXTERNAL_SIMPLEX_ERROR,
  EXTERNAL_SIMPLEX_UNBOUNDED,
  EXTERNAL_SIMPLEX_INFEASIBLE,
  EXTERNAL_SIMPLEX_EXHAUSTED,
} external_simplex_status_t;

typedef struct {
  external_simplex_status_t status;
  xrational_t *x;
  uint32_t nvars;
  thvar_t *basic_vars;
  uint32_t nb_vars;
} external_solution_t;

#endif // __EXTERNAL_SIMPLEX_TYPES_H
