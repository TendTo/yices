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
  mpq_QSprob prob;
  SolverStatus d_status;

  // DenseMap<std::size_t> d_colIndices;
  // std::vector<ArithVar> d_rowToArithVar;
  // std::vector<ArithVar> d_colToArithVar;

  mpq_t *rhs;
  mpq_t *range;
  char *sense;
  rational_t x;
  QSbasis basis;
} qsx_t;

void qsx_solve(simplex_solver_t *solver, external_solution_t *solution);

#endif // __EXTERNAL_QSOPTEX_H
