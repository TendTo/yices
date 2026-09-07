/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */

#ifndef __EXTERNAL_SIMPLEX_H
#define __EXTERNAL_SIMPLEX_H

#include <stdbool.h>

static const int pivot_threshold = 10000;

typedef struct simplex_solver_s simplex_solver_t;

bool simplex_check_feasibility_external(simplex_solver_t *solver);

#endif
