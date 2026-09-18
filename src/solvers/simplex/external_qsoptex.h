/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_qsoptex class.
 */
#ifndef __EXTERNAL_QSOPTEX_H
#define __EXTERNAL_QSOPTEX_H

#include "solvers/simplex/external_simplex_types.h"
#include "solvers/simplex/simplex_types.h"
#include "terms/rationals.h"
#include <gmp.h>

#include "qsopt_ex/QSopt_ex.h"

typedef char VarStatus;
typedef int SolverStatus;

typedef struct {
  mpq_QSprob prob;       ///< The QSopt_ex LP problem
  SolverStatus d_status; ///< Status of the LP problem after solving

  thvar_t *col_to_var; ///< Map from column index in the LP to theory var
  thvar_t *row_to_var; ///< Map from row index in the LP to theory var

  int32_t *var_to_col; ///< Map from theory var to column index in the LP
  int32_t *var_to_row; ///< Map from theory var to row index in the LP

  int32_t n_aux; ///< Number of auxiliary variables

  mpq_t *rhs;    ///< Right-hand side of the constraints
  mpq_t *range;  ///< Range of the constraints
  char *sense;   ///< Sense of the constraints ('E', 'G', 'L', or 'R')
  rational_t x;  ///< Temporary rational for storing the solution
  QSbasis basis; ///< Basis information for the solution
} qsx_t;

void qsx_solve(simplex_solver_t *solver, external_solution_t *solution);

#endif // __EXTERNAL_QSOPTEX_H
