/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_qsoptex class.
 */
#include "external_qsoptex.h"

#include "external_simplex.h"
#include "frontend/smt2/smt2_commands.h"
#include "simplex_types.h"
#include "utils/memalloc.h"
#include <stdbool.h>

static const int pivot_threshold = 10000;
static bool qsx_started = false;
static mpq_t epsilon;

static void global_qsx_start() {
  if (qsx_started)
    return;
  qsx_started = true;
  QSexactStart();
  mpq_init(epsilon);
  mpq_set_ui(epsilon, 1, 1000000);
}

static void global_qsx_clear() {
  if (!qsx_started)
    return;
  QSexactClear();
  mpq_clear(epsilon);
  qsx_started = false;
}

static void basis_clear(QSbasis *const basis) {
  if (basis->cstat != NULL)
    safe_free(basis->cstat);
  if (basis->rstat != NULL)
    safe_free(basis->rstat);
  basis->cstat = NULL;
  basis->rstat = NULL;
  basis->nstruct = 0;
  basis->nrows = 0;
}

void qsx_init(qsx_t *qsx) {
  global_qsx_start();
  qsx->prob = mpq_QScreate_prob(NULL, QS_MIN);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_DISPLAY,
                  __smt2_globals.verbosity);
}

void qsx_clear(qsx_t *qsx) {
  mpq_QSfree_prob(qsx->prob);
  global_qsx_clear();
}

static mpq_ptr qsx_get_bound(bound_type_t bound, bool *const used_temp,
                             mpq_t *temp) {
  return get_bound(bound, mpq_NINFTY, mpq_INFTY, used_temp, temp);
}

static mpq_ptr qsx_get_y(mpq_QSprob prob, const int rowIdx) {
  assert(prob && prob->lp && prob->lp->pIpiz);
  return prob->lp->pIpiz[rowIdx];
}

/**
 * Loop over all the theory variables in the solver and add them as columns to
 * the LP problem in QSopt_ex, having care of setting the appropriate lower and
 * upper bounds for each variable.
 * The bounds, if finite, are listed in the solver's bstack, and are converted
 * to mpq_t as needed.
 * @param solver the simplex solver containing the variables and their bounds
 * @param[out] qsx the QSopt_ex LP problem to which the columns will be
 * added
 */
static void add_cols(const simplex_solver_t *const solver,
                     const qsx_t *const qsx) {
  static mpq_t tmp_lb, tmp_ub;
  mpq_QSprob prob = qsx->prob;
  xrational_t *bounds = solver->bstack.bound;

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  for (uint32_t v = 0; v < solver->vtbl.nvars; v++) {
    bool used_temp_lb = false, used_tmp_ub = false;
    const int32_t lb_idx = solver->vtbl.lower_index[v];
    const int32_t ub_idx = solver->vtbl.upper_index[v];
    const bool has_lb = lb_idx > -1;
    const bool has_ub = ub_idx > -1;
    const bool strict_lb = has_lb ? !xq_is_rational(&bounds[lb_idx]) : false;
    const bool strict_ub = has_ub ? !xq_is_rational(&bounds[ub_idx]) : false;

    mpq_ptr lb = qsx_get_bound(
        ((bound_type_t){.is_finite = has_lb,
                        .is_strict = __smt2_globals.delta < 0 && strict_lb,
                        .is_lb = true,
                        .val = has_lb ? bounds[lb_idx].main : (rational_t){0}}),
        &used_temp_lb, &tmp_lb);
    mpq_ptr ub = qsx_get_bound(
        ((bound_type_t){.is_finite = has_ub,
                        .is_strict = __smt2_globals.delta < 0 && strict_ub,
                        .is_lb = false,
                        .val = has_ub ? bounds[ub_idx].main : (rational_t){0}}),
        &used_tmp_ub, &tmp_ub);

    mpq_QSnew_col(prob, mpq_oneLpNum, lb, ub, NULL);

    if (used_temp_lb) {
      mpq_clear(tmp_lb);
      used_temp_lb = false;
    }
    if (used_tmp_ub) {
      mpq_clear(tmp_ub);
      used_tmp_ub = false;
    }
  }
}

/**
 * Loop over all the rows in the solver and add them as rows to the LP problem
 * in QSopt_ex, having care of setting the appropriate right-hand side and range
 * for each row.
 * @param solver the simplex solver containing the rows
 * @param[out] qsx the QSopt_ex LP problem to which the rows will be added
 */
static void add_rows(const simplex_solver_t *const solver,
                     const qsx_t *const qsx) {
  mpq_QSprob prob = qsx->prob;
  const matrix_t *matrix = &solver->matrix;
  mpq_t d_rhs[matrix->nrows];
  [[maybe_unused]] mpq_t d_range[matrix->nrows];
  int non_zero_per_row[matrix->nrows];
  int begin_row_idx[matrix->nrows];
  int col_idxs[(matrix->ncolumns + matrix->nrows) * 2];
  mpq_t values[(matrix->ncolumns + matrix->nrows) * 2];
  char d_sense[matrix->nrows];

  int d_range_idx = 0, d_rhs_idx = 0, non_zero_per_row_idx = 0,
      begin_row_idx_idx = 0, col_idxs_idx = 0, values_idx = 0, d_sense_idx = 0;

  // Add rows to the LP problem
  for (uint32_t i = 0; i < matrix->nrows; i++) {
    row_t *row = matrix->row[i];
    if (row->size == 0) {
      continue;
    }

    int num_non_zeros = 0;
    // where the non-zero columns of the row are stored
    begin_row_idx[begin_row_idx_idx++] = col_idxs_idx;
    // the sense of the row ('E', 'G', 'L', or 'R' for range)
    d_sense[d_sense_idx++] = 'E'; // TODO: use the correct sense
    // and a placeholder rhs value for the row = 0, which can be updated later.
    mpq_init(d_rhs[d_rhs_idx]);
    mpq_set(d_rhs[d_rhs_idx++], mpq_zeroLpNum);

    for (uint32_t j = 0; j < row->size; j++) {
      const thvar_t x = row->data[j].c_idx;
      if (x < 0) {
        continue;
      }
      const rational_t *coeff = &row->data[j].coeff;
      if (x == const_idx) {
        // Update the placeholder rhs value for the row
        copy_to_gmp(coeff, d_rhs[d_rhs_idx - 1]);
      } else {
        num_non_zeros++;
        col_idxs[col_idxs_idx++] = (int)x;
        init_and_copy_to_gmp(coeff, values[values_idx++]);
      }
    }

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[non_zero_per_row_idx++] = num_non_zeros;
  }

  printf(
      "Indeces: d_rhs_idx=%d, non_zero_per_row_idx=%d, begin_row_idx_idx=%d, "
      "d_sense_idx=%d, col_idxs_idx=%d, values_idx=%d\n",
      d_rhs_idx, non_zero_per_row_idx, begin_row_idx_idx, d_sense_idx,
      col_idxs_idx, values_idx);
  print_int_vector(col_idxs, col_idxs_idx, "col_idxs");
  print_int_vector(non_zero_per_row, non_zero_per_row_idx, "non_zero_per_row");
  print_int_vector(begin_row_idx, begin_row_idx_idx, "begin_row_idx");
  print_mpq_vector(d_range, d_range_idx, "d_range");
  print_mpq_vector(values, values_idx, "values");
  print_mpq_vector(d_rhs, d_rhs_idx, "d_rhs");
  print_char_vector(d_sense, d_sense_idx, "d_sense");

  // TODO: Use ranged rows when possible
  // mpq_QSadd_ranged_rows(qsx_prob, non_zero_per_row_idx + 1, non_zero_per_row,
  //                       begin_row_idx, col_idxs, values, d_rhs, d_sense,
  //                       d_range, NULL);

  mpq_QSadd_rows(prob, non_zero_per_row_idx, non_zero_per_row, begin_row_idx,
                 col_idxs, values, d_rhs, d_sense, NULL);

  mpq_vector_clear(values, values_idx);
  mpq_vector_clear(d_rhs, d_rhs_idx);
  mpq_vector_clear(d_range, d_range_idx);
}

static void extract_col_value(simplex_solver_t *solver,
                              external_solution_t *sol, const thvar_t v,
                              const QSbasis *const basis,
                              int_bvset_t *basic_vars_set,
                              int_bvset_t *non_basic_vars_set) {
  xrational_t *x = sol->x;
  const char varStatus = basis->cstat[v]; // TODO: i think needs to be converted
  // from thvar to col index

  if (varStatus == QS_COL_BSTAT_BASIC)
    int_bvset_add(basic_vars_set, v);
  else if (varStatus != QS_COL_BSTAT_BASIC)
    int_bvset_add(non_basic_vars_set, v);

  switch (varStatus) {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    if (is_below_lb(solver, v, x + v)) {
      xq_set(x + v, get_lb(solver, v));
    } else if (is_above_ub(solver, v, x + v)) {
      xq_set(x + v, get_ub(solver, v));
    }
    assert(!is_above_ub(solver, v, x + v));
    assert(!is_below_lb(solver, v, x + v));
    break;
    // For non-basic variables we know the value is at a bound
    // and we can use the d_vars/proper LP bounds directly
  case QS_COL_BSTAT_LOWER:
    if (!has_any_bound(solver, v)) {
      // Free rows are set to lower bound, so we leave the value as is
      // (there is no lower bound to set them to)
    } else {
      xq_set(x + v, get_lb(solver, v));
    }
    break;
  case QS_COL_BSTAT_UPPER:
    xq_set(x + v, get_ub(solver, v));
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, varStatus);
    exit(1);
  }
}

#if 0
static void extract_row_value(simplex_solver_t *solver,
                              external_solution_t *sol, const thvar_t v,
                              const QSbasis *const basis,
                              int_bvset_t *basic_vars_set,
                              int_bvset_t *non_basic_vars_set) {
  xrational_t *x = sol->x;
  const int row_idx = v; // TODO: convert from thvar to row index
  const char varStatus = basis->rstat[row_idx];

  if (varStatus == QS_COL_BSTAT_BASIC)
    int_bvset_add(basic_vars_set, v);
  else if (varStatus != QS_COL_BSTAT_BASIC)
    int_bvset_add(non_basic_vars_set, v);

  switch (varStatus) {
  // If we are dealing with a basic variable, we necessarily need to get its
  // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    mpq_t rhs;
    rhs = d_rhs[idx] +
          (d_sense[idx] == 'L' ? -get_y(prob, row_idx) : get_y(prob, row_idx));
    value = &toMpq(rhs);

    if (is_below_lb(solver, v, x + v)) {
      xq_set(x + v, get_lb(solver, v));
    } else if (is_above_ub(solver, v, x + v)) {
      xq_set(x + v, get_ub(solver, v));
    }
    assert(!is_above_ub(solver, v, x + v));
    assert(!is_below_lb(solver, v, x + v));
    break;
  // For non-basic variables we know the value is at a bound
  // and we can use the d_vars/proper LP bounds directly
  case QS_COL_BSTAT_LOWER:
    Trace("approx-debug") << "non-basic lb" << std::endl;
    // Free rows are set to lower bound, handle them accordingly
    if (!d_vars.hasEitherBound(v)) {
      if (VarType == VariableType::ROW) {
        rhs = d_rhs[idx] + (d_sense[idx] == 'G' ? getY(idx) : -getY(idx));
        value = &toMpq(rhs);
      } else if (VarType == VariableType::COL) {
        value = &d_x[idx];
      }
      Assert(value != nullptr);
      newValues.set(v, DeltaRational(toMpqClass(*value)));
    } else if (VarType == VariableType::ROW) {
      if (d_sense[idx] == 'G' || d_sense[idx] == 'R') {
        Assert(d_vars.hasLowerBound(v));
        newValues.set(v, d_vars.getLowerBound(v));
      } else if (d_sense[idx] == 'L') {
        Assert(d_vars.hasUpperBound(v));
        newValues.set(v, d_vars.getUpperBound(v));
      } else {
        Unreachable();
      }
    } else if (VarType == VariableType::COL) {
      Assert(d_vars.hasLowerBound(v));
      newValues.set(v, d_vars.getLowerBound(v));
    } else {
      Unreachable();
    }
    break;
  case QS_COL_BSTAT_UPPER:
    Trace("approx-debug") << "non-basic ub" << std::endl;
    Assert(d_vars.hasUpperBound(v));
    newValues.set(v, d_vars.getUpperBound(v));
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, varStatus);
    exit(1);
  }
}

external::Solution ExactQsoptexEpsilon::extractSolution(bool mip) {
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);
  external::Solution sol;

  if (d_status == QS_LP_OPTIMAL || d_status == QS_LP_DELTA_OPTIMAL ||
      d_status == QS_LP_FEASIBLE || d_status == QS_LP_DELTA_FEASIBLE ||
      d_status == QS_LP_UNBOUNDED || d_status == QS_LP_INFEASIBLE) {
    for (int colIdx = 0; colIdx < numCols(); colIdx++) {
      extractVarValue<VariableType::COL>(colIdx, sol);
    }

    for (int rowIdx = 0; rowIdx < numRows(); rowIdx++) {
      extractVarValue<VariableType::ROW>(rowIdx, sol);
    }
  } else {
    // Infeasible solution.
    Unimplemented();
  }

  return sol;
}


external_solution_t import_result(simplex_solver_t *solver,
                                  external_solution_t *sol) {
  const int new_basis[] = {};
  const xrational_t *const new_values = sol->x;

#if 0 // For debug
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(d_tableau.isBasic(b)){
      std::cout << "Variable " << b << " => ";
      if (d_variables.isAuxiliary(b))
        std::cout << d_variables.asNode(b).getName();
      else
        d_variables.printModel(b, std::cout);
      std::cout << " is basic" << std::endl;
    }
  }
#endif

  int needs_to_be_added[solver->vtbl.nvars];
  int needs_to_be_added_idx = 0;
  for (int32_t i = 0; i < solver->vtbl.nvars; i++) {
    // TODO: if the basic variable is NOT in the basis, mark it
    if (matrix_is_nonbasic_var(&solver->matrix, i)) {
      needs_to_be_added[needs_to_be_added_idx++] = i;
    }
  }

  for (int i = 0; i < needs_to_be_added_idx; i++) {
    const mpq_t *const val = &new_values[i];
    if (!d_tableau.isBasic(currentlyNb)) {
      if (!matchesNewValue(newValues, currentlyNb)) {
        const DeltaRational &newValue = newValues[currentlyNb];
        printf("Updating variable %d from %s to %s\n", currentlyNb,
               d_variables.getAssignment(currentlyNb).toString().c_str(),
               newValue.toString().c_str());
        d_linEq.update(currentlyNb, newValue);
        Assert(d_variables.assignmentIsConsistent(currentlyNb));
      }
    }
  }
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if (processSignals()) {
    Trace("arith::findModel") << "attemptSolution() early conflict" << endl;
    d_conflictVariables.purge();
    return Result::UNSAT;
  } else if (d_errorSet.errorEmpty()) {
    Trace("arith::findModel") << "attemptSolution() fixed itself" << endl;
    return Result::SAT;
  }

  // The simple assignment was not enough, extended search is needed
  ++d_statistics.d_extendedSearch;

  while (!needs_to_be_added.empty() && !d_errorSet.errorEmpty()) {
    ArithVar toRemove = ARITHVAR_SENTINEL;
    ArithVar toAdd = ARITHVAR_SENTINEL;
    DenseSet::const_iterator i = needs_to_be_added.begin(),
                             i_end = needs_to_be_added.end();
    for (; toAdd == ARITHVAR_SENTINEL && i != i_end; ++i) {
      ArithVar v = *i;

      Tableau::ColIterator colIter = d_tableau.colIterator(v);
      for (; !colIter.atEnd(); ++colIter) {
        const Tableau::Entry &entry = *colIter;
        Assert(entry.getColVar() == v);
        ArithVar b = d_tableau.rowIndexToBasic(entry.getRowIndex());
        if (!newBasis.isMember(b)) {
          toAdd = v;

          bool favorBOverToRemove = (toRemove == ARITHVAR_SENTINEL) ||
                                    (matchesNewValue(newValues, toRemove) &&
                                     !matchesNewValue(newValues, b)) ||
                                    (d_tableau.basicRowLength(toRemove) >
                                     d_tableau.basicRowLength(b));

          if (favorBOverToRemove) {
            toRemove = b;
          }
        }
      }
    }
    Assert(toRemove != ARITHVAR_SENTINEL);
    Assert(toAdd != ARITHVAR_SENTINEL);

    Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;

    d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);

    Trace("arith::forceNewBasis")
        << needs_to_be_added.size() << "to go" << endl;
    needs_to_be_added.remove(toAdd);

    bool conflict = processSignals();
    if (conflict) {
      d_errorSet.reduceToSignals();
      d_conflictVariables.purge();

      return Result::UNSAT;
    }
  }
  Assert(d_conflictVariables.empty());

  if (d_errorSet.errorEmpty()) {
    return Result::SAT;
  } else {
    d_errorSet.reduceToSignals();
    return Result::UNKNOWN;
  }
}
#endif

static void qsx_build_problem(simplex_solver_t *solver, qsx_t *qsx) {
  add_cols(solver, qsx);
  add_rows(solver, qsx);
  // mpq_QSdump_prob(qsx_prob);
}

static void qsx_solve_lp(simplex_solver_t *const solver, qsx_t *const qsx,
                         external_solution_t *const solution) {
#ifndef NDEBUG
  mpq_QSwrite_prob(
      d_qsx, "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/qsfile.lp",
      "LP");
#endif
  mpq_QSprob prob = qsx->prob;

  // Should have room for the (rowcount) "logical" variables, which come after
  // the (colcount) "structural" variables.
  unsigned int precision = 0;
  mpq_t delta;
  mpq_init(delta);
  mpq_set_d(delta, __smt2_globals.delta);
  int status = 0;
  mpq_t x[solver->vtbl.nvars];
  for (uint32_t i = 0; i < solver->vtbl.nvars; i++) {
    mpq_init(x[i]);
  }
  QSbasis basis = {.nrows = solver->matrix.nrows,
                   .nstruct = 0,
                   .cstat = NULL,
                   .rstat = NULL};

  [[maybe_unused]] const int res =
      QSdelta_solver(prob, delta, x, NULL, &basis, &precision, PRIMAL_SIMPLEX,
                     &status, NULL, NULL);
  assert(res == 0);

  // Update the statistics
  if (precision > solver->stats.max_precision)
    solver->stats.max_precision = precision;
  const double new_delta = mpq_get_d(delta);
  if (new_delta > solver->stats.max_delta)
    solver->stats.max_delta = new_delta;

  // Transfer the solution to the external_solution_t structure
  // It will take the ownership of the mpq_t values in x.
  for (uint32_t i = 0; i < solver->vtbl.nvars; i++) {
    q_set_mpq_prenormalize(&solution->x[i].main, x[i]);
  }

#ifndef NDEBUG
  std::cout << "The total infeas is " << delta << std::endl;
#endif

  switch (status) {
  case QS_LP_OPTIMAL:
  case QS_LP_FEASIBLE:
  case QS_LP_DELTA_OPTIMAL:
  case QS_LP_DELTA_FEASIBLE:
  case QS_LP_UNBOUNDED:
    solution->nvars = solver->vtbl.nvars;
    solution->status = is_strict_var_zero(x[solver->vtbl.nvars - 1])
                           ? EXTERNAL_SIMPLEX_INFEASIBLE
                           : EXTERNAL_SIMPLEX_FEASIBLE;
    break;
  case QS_LP_INFEASIBLE:
    solution->status = EXTERNAL_SIMPLEX_INFEASIBLE;
    break;
  case QS_LP_ITER_LIMIT:
  case QS_LP_TIME_LIMIT:
    solution->status = EXTERNAL_SIMPLEX_EXHAUSTED;
    break;
  default:
    printf("QSopt_ex returned an unexpected status: %d\n", status);
    solution->status = EXTERNAL_SIMPLEX_ERROR;
    break;
  }

  basis_clear(&basis);
  mpq_vector_clear(x, solver->vtbl.nvars);
  mpq_clear(delta);
}

void qsx_solve(simplex_solver_t *solver, external_solution_t *solution) {
  qsx_t qsx;
  qsx_init(&qsx);
  qsx_build_problem(solver, &qsx);
  qsx_solve_lp(solver, &qsx, solution);
  qsx_clear(&qsx);
}
