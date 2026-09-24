/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_qsoptex class.
 */
#ifndef __EXTERNAL_QSOPTEX_H
#define __EXTERNAL_QSOPTEX_H
#ifndef HAVE_QSOPTEX
#error                                                                         \
    "QSopt_ex library is not available. Please install it to use this feature."
#endif

#include "solvers/simplex/external_simplex_types.h"
#include "solvers/simplex/simplex_types.h"

typedef char VarStatus;
typedef int SolverStatus;

void qsx_solve(simplex_solver_t *solver, external_solution_t *sol);
/**
 * Performs any necessary cleanup for the QSopt_ex library.
 * This function should be called from the `yices_exit` function
 * to ensure that all resources allocated by the QSopt_ex library
 * are properly released.
 * The function is idempotent,
 * meaning that it can be called multiple times without adverse effects.
 */
void global_qsx_clear();

#endif // __EXTERNAL_QSOPTEX_H
