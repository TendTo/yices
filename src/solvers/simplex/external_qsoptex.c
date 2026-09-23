/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_qsoptex class.
 */
#include "external_qsoptex.h"

#include "frontend/smt2/smt2_commands.h"
#include "io/term_printer.h"
#include "solvers/simplex/external_simplex.h"
#include "solvers/simplex/simplex_types.h"
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
  safe_free(basis->cstat);
  safe_free(basis->rstat);
  basis->cstat = NULL;
  basis->rstat = NULL;
  basis->nstruct = 0;
  basis->nrows = 0;
}

static void qsx_init(qsx_t *qsx) {
  global_qsx_start();
  memset(qsx, 0, sizeof(qsx_t));
  qsx->prob = mpq_QScreate_prob(NULL, QS_MIN);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_DISPLAY,
                  __smt2_globals.verbosity);
}

static void qsx_init_vars(simplex_solver_t *const solver, qsx_t *qsx) {
  const uint32_t nvars = solver->vtbl.nvars;

  // Set the number of auxiliary variables in the QSopt_ex problem,
  // which is equal to the rows of the LP problem,
  // and the number of structural variables,
  // which is equal to the columns of the LP problem.
  for (thvar_t v = 0; v < nvars; v++) {
    if (arith_var_def_is_poly(&solver->vtbl, v)) {
      qsx->n_aux++;
    } else if (arith_var_is_free(&solver->vtbl, v)) {
      qsx->n_struct++;
    }
  }

  qsx->col_to_var = safe_malloc(qsx->n_struct * sizeof(thvar_t));
  qsx->row_to_var = safe_malloc(qsx->n_aux * sizeof(thvar_t));
  qsx->var_to_col = safe_malloc(nvars * sizeof(uint32_t));
  qsx->var_to_row = safe_malloc(nvars * sizeof(uint32_t));
  qsx->x = safe_malloc(qsx->n_struct * sizeof(mpq_t));
  qsx->y = safe_malloc(qsx->n_aux * sizeof(mpq_t));
  qsx->range = safe_malloc(qsx->n_aux * sizeof(mpq_t));
  qsx->rhs = safe_malloc(qsx->n_aux * sizeof(mpq_t));
  qsx->sense = safe_malloc(qsx->n_aux * sizeof(char));

  for (uint32_t i = 0; i < qsx->n_struct; i++) {
    qsx->col_to_var[i] = -1;
    mpq_init(qsx->x[i]);
  }
  for (uint32_t i = 0; i < qsx->n_aux; i++) {
    qsx->row_to_var[i] = -1;
    mpq_init(qsx->y[i]);
    mpq_init(qsx->range[i]);
    mpq_init(qsx->rhs[i]);
  }
  for (uint32_t i = 0; i < nvars; i++) {
    qsx->var_to_col[i] = -1;
    qsx->var_to_row[i] = -1;
  }
}

static void qsx_clear(qsx_t *const qsx) {
  basis_clear(&qsx->basis);
  mpq_QSfree_prob(qsx->prob);
  mpq_vector_clear(qsx->x, qsx->n_struct);
  mpq_vector_clear(qsx->y, qsx->n_aux);
  mpq_vector_clear(qsx->range, qsx->n_aux);
  mpq_vector_clear(qsx->rhs, qsx->n_aux);
  safe_free(qsx->col_to_var);
  safe_free(qsx->row_to_var);
  safe_free(qsx->var_to_col);
  safe_free(qsx->var_to_row);
  safe_free(qsx->x);
  safe_free(qsx->y);
  safe_free(qsx->range);
  safe_free(qsx->rhs);
  safe_free(qsx->sense);
  global_qsx_clear();
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
static void add_cols(simplex_solver_t *const solver, const qsx_t *const qsx) {
  static bound_type_t lb, ub;
  mpq_QSprob prob = qsx->prob;

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  int free_vars = 0;
  int aux_vars = 0;
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {
    if (!arith_var_is_free(&solver->vtbl, v)) {
      // If the variable is not free, it is because it is an auxiliary variable.
      // We will encode those as rows later.
      // printf("Skipping variable %d because it is not free\n", v);
      // print_simplex_var(stdout, solver, v);
      aux_vars++;
      continue;
    }
    // printf("Adding variable %d to QSopt_ex LP problem\n", v);
    // print_simplex_var(stdout, solver, v);
    free_vars++;

    get_bound(solver, v, true, &lb);
    get_bound(solver, v, false, &ub);

    qsx->col_to_var[mpq_QSget_colcount(prob)] = v;
    qsx->var_to_col[v] = mpq_QSget_colcount(prob);
    mpq_QSnew_col(prob, mpq_oneLpNum, lb.is_finite ? lb.val : mpq_NINFTY,
                  ub.is_finite ? ub.val : mpq_INFTY, NULL);

    bound_type_clear(&lb);
    bound_type_clear(&ub);
  }
}

/**
 * Loop over all the rows in the solver and add them as rows to the LP problem
 * in QSopt_ex, having care of setting the appropriate right-hand side and range
 * for each row.
 * @param solver the simplex solver containing the rows
 * @param[out] qsx the QSopt_ex LP problem to which the rows will be added
 */
static void add_rows(simplex_solver_t *const solver, const qsx_t *const qsx) {
  static bound_type_t lb, ub;

  mpq_QSprob prob = qsx->prob;
  int non_zero_per_row[qsx->n_aux];
  int begin_row_idx[qsx->n_aux];
  int col_idxs[(solver->vtbl.nvars - qsx->n_aux - 1) * qsx->n_aux];
  mpq_t values[(solver->vtbl.nvars - qsx->n_aux - 1) * qsx->n_aux];

  int32_t row_idx = 0, non_zero_per_row_idx = 0, col_idxs_idx = 0,
          values_idx = 0;

  // Add rows to the LP problem
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < n_vars; v++) {
    // Skip structural variables and constants
    if (!arith_var_def_is_poly(&solver->vtbl, v)) {
      continue;
    }

    const polynomial_t *const p = arith_var_poly_def(&solver->vtbl, v);
    assert(p != NULL);

    // where the non-zero columns of the row are stored
    begin_row_idx[row_idx] = col_idxs_idx;

    // TODO: may be unnecessary if 'R' sense is not used
    mpq_set(qsx->range[row_idx], mpq_zeroLpNum);

    // Add row range
    get_bound(solver, v, true, &lb);
    get_bound(solver, v, false, &ub);

    if (lb.is_finite && ub.is_finite) // Bounded
    {
      mpq_set(qsx->rhs[row_idx], lb.val);
      mpq_set(qsx->range[row_idx], ub.val);
      mpq_sub(qsx->range[row_idx], qsx->range[row_idx], qsx->rhs[row_idx]);
      if (__smt2_globals.epsilon_mode && lb.is_strict) {
        mpq_sub(qsx->range[row_idx], qsx->range[row_idx], epsilon);
      }
      qsx->sense[row_idx] = 'R';
      // printf("Adding bounded row %d with lower bound %s and upper bound
      // %s\n", row_idx, mpq_get_str(NULL, 10, d_rhs[row_idx]),
      // mpq_get_str(NULL, 10, d_range[row_idx]));
    } else if (lb.is_finite) // Only lower bound
    {
      // printf("Adding lower bounded row %d with lower bound %s\n", row_idx,
      // mpq_get_str(NULL, 10, lb.val));
      mpq_set(qsx->rhs[row_idx], lb.val);
      qsx->sense[row_idx] = 'G';
    } else if (ub.is_finite) // Only upper bound
    {
      // printf("Adding upper bounded row %d with upper bound %s\n", row_idx,
      //        mpq_get_str(NULL, 10, ub.val));
      mpq_set(qsx->rhs[row_idx], ub.val);
      qsx->sense[row_idx] = 'L';
    } else // Unbounded
    {
      // printf("Adding unbounded row %d\n", row_idx);
      mpq_set(qsx->rhs[row_idx], mpq_NINFTY);
      qsx->sense[row_idx] = 'G';
      // printf("Unbounded variable %d\n", v);
    }

    bound_type_clear(&lb);
    bound_type_clear(&ub);

    int num_non_zeros = 0;
    for (uint32_t i = 0; i < p->nterms; i++) {
      const monomial_t *const mono = &p->mono[i];
      const thvar_t x = mono->var;
      const rational_t *coeff = &mono->coeff;

      if (x == const_idx) {
        // printf("Adding constant term to row %d\n", row_idx);
        sub_to_gmp(qsx->rhs[row_idx], qsx->rhs[row_idx], coeff);
#ifndef NDEBUG
        get_bound(solver, v, true, &lb);
        get_bound(solver, v, false, &ub);
        assert(lb.is_finite || ub.is_finite);
        bound_type_clear(&lb);
        bound_type_clear(&ub);
#endif
      } else {
        assert(arith_var_is_free(&solver->vtbl, x));
        // Add var coefficient
        num_non_zeros++;
        col_idxs[col_idxs_idx++] = qsx->var_to_col[x];
        init_and_copy_to_gmp(values[values_idx++], coeff);
      }
    }

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[non_zero_per_row_idx++] = num_non_zeros;

    // Add the new row to the map
    qsx->row_to_var[row_idx] = v;
    qsx->var_to_row[v] = row_idx++;
  }

  // print_int_vector(col_idxs, col_idxs_idx, "col_idxs");
  // print_int_vector(non_zero_per_row, non_zero_per_row_idx,
  // "non_zero_per_row"); print_int_vector(begin_row_idx, row_idx,
  // "begin_row_idx"); print_mpq_vector(d_range, row_idx, "d_range");
  // print_mpq_vector(values, values_idx, "values");
  // print_mpq_vector(d_rhs, row_idx, "d_rhs");
  // print_char_vector(d_sense, row_idx, "d_sense");

  mpq_QSadd_ranged_rows(prob, non_zero_per_row_idx, non_zero_per_row,
                        begin_row_idx, col_idxs, values, qsx->rhs, qsx->sense,
                        qsx->range, NULL);

  mpq_vector_clear(values, values_idx);
}

static void extract_col_value(simplex_solver_t *const solver, qsx_t *const qsx,
                              external_solution_t *const sol, const int c) {
  xrational_t *x = sol->x;
  const thvar_t v = qsx->col_to_var[c];
  const char var_status = qsx->basis.cstat[c];
  // from thvar to col index

  if (var_status == QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->b_vars, v);
  else if (var_status != QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->nb_vars, v);

  switch (var_status) {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    // Start by setting the current basic result
    xq_set_mpq_prenormalize(sol->x + v, qsx->x[c]);
    // Ensure the result is within the bounds of the variable, if any
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
      xq_set_mpq_prenormalize(sol->x + v, qsx->x[c]);
    } else {
      assert(has_lb(solver, v));
      xq_set(x + v, get_lb(solver, v));
    }
    break;
  case QS_COL_BSTAT_UPPER:
    assert(has_ub(solver, v));
    xq_set(x + v, get_ub(solver, v));
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, var_status);
    exit(1);
  }
}

static void extract_row_value(simplex_solver_t *const solver, qsx_t *const qsx,
                              external_solution_t *const sol, const int r) {
  xrational_t *x = sol->x;
  var_bound_state_t *bounds = sol->bounds;
  const thvar_t v = qsx->row_to_var[r];
  const char var_status = qsx->basis.rstat[r];

  if (var_status == QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->b_vars, v);
  else if (var_status != QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->nb_vars, v);

  mpq_t rhs;
  switch (var_status) {
  // If we are dealing with a basic variable, we necessarily need to get its
  // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    mpq_init(rhs);
    mpq_set(rhs, qsx->rhs[r]);
    if (qsx->sense[r] == 'L') {
      mpq_sub(rhs, rhs, qsx->y[r]);
    } else {
      mpq_add(rhs, rhs, qsx->y[r]);
    }
    xq_set_mpq_prenormalize(sol->x + v, rhs);
    mpq_clear(rhs);

    if (is_below_lb(solver, v, x + v)) {
      bounds[v] = VAR_BOUND_AT_LOWER;
    } else if (is_above_ub(solver, v, x + v)) {
      bounds[v] = VAR_BOUND_AT_UPPER;
    }
    break;
  // For non-basic variables we know the value is at a bound
  // and we can use the d_vars/proper LP bounds directly
  case QS_COL_BSTAT_LOWER:
    // Free rows are set to lower bound, handle them accordingly
    if (!has_any_bound(solver, v)) {
      // Free rows are set to lower bound, so we leave the value as is
      // (there is no lower bound to set them to)
      mpq_init(rhs);
      mpq_set(rhs, qsx->rhs[r]);
      if (qsx->sense[r] == 'L') {
        mpq_sub(rhs, rhs, qsx->y[r]);
      } else {
        mpq_add(rhs, rhs, qsx->y[r]);
      }
      xq_set_mpq_prenormalize(sol->x + v, rhs);
      mpq_clear(rhs);
    } else {
      if (qsx->sense[r] == 'G' || qsx->sense[r] == 'R') {
        assert(has_lb(solver, v));
        bounds[v] = VAR_BOUND_AT_LOWER;
      } else if (qsx->sense[r] == 'L') {
        assert(has_ub(solver, v));
        bounds[v] = VAR_BOUND_AT_UPPER;
      } else {
        printf("Unknown sense for row %d: %c\n", r, qsx->sense[r]);
        exit(1);
      }
    }
    break;
  case QS_COL_BSTAT_UPPER:
    assert(has_ub(solver, v));
    bounds[v] = VAR_BOUND_AT_UPPER;
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, var_status);
    exit(1);
  }
}

static void extract_solution(simplex_solver_t *solver, qsx_t *qsx,
                             external_solution_t *sol) {
  const SolverStatus status = qsx->status;
  const mpq_QSprob *prob = &qsx->prob;

  assert(status == QS_LP_OPTIMAL || status == QS_LP_DELTA_OPTIMAL ||
         status == QS_LP_FEASIBLE || status == QS_LP_DELTA_FEASIBLE ||
         status == QS_LP_UNBOUNDED || status == QS_LP_INFEASIBLE);

  for (int col_idx = 0; col_idx < mpq_QSget_colcount(*prob); col_idx++) {
    extract_col_value(solver, qsx, sol, col_idx);
  }
  for (int row_idx = 0; row_idx < mpq_QSget_rowcount(*prob); row_idx++) {
    extract_row_value(solver, qsx, sol, row_idx);
  }
}

static void qsx_build_problem(simplex_solver_t *const solver,
                              qsx_t *const qsx) {
  add_cols(solver, qsx);
  add_rows(solver, qsx);
  // mpq_QSdump_prob(qsx->prob);
  // static int i = '0';
  // char filename[256];
  // snprintf(
  //     filename, sizeof(filename),
  //     "/home/campus.ncl.ac.uk/c3054737/Programming/phd/yices2/qsproblem_%c.lp",
  //     i);
  // mpq_QSwrite_prob(qsx->prob, filename, "LP");
  // i++;
}

static void qsx_solve_lp(simplex_solver_t *const solver, qsx_t *const qsx,
                         external_solution_t *const solution) {
  const mpq_QSprob *const prob = &qsx->prob;

  unsigned int precision = 0;
  mpq_t delta;
  mpq_init(delta);
  mpq_set_d(delta, __smt2_globals.delta);

  [[maybe_unused]] const int res =
      QSdelta_solver(*prob, delta, qsx->x, qsx->y, &qsx->basis, &precision,
                     PRIMAL_SIMPLEX, &qsx->status, NULL, NULL);
  assert(res == 0);

  // Update the statistics
  if (precision > solver->stats.max_precision)
    solver->stats.max_precision = precision;
  const double new_delta = mpq_get_d(delta);
  if (new_delta > solver->stats.max_delta)
    solver->stats.max_delta = new_delta;

  switch (qsx->status) {
  case QS_LP_OPTIMAL:
  case QS_LP_FEASIBLE:
  case QS_LP_DELTA_OPTIMAL:
  case QS_LP_DELTA_FEASIBLE:
  case QS_LP_UNBOUNDED:
    solution->nvars = solver->vtbl.nvars;
    solution->status = is_strict_var_zero(qsx->x[mpq_QSget_colcount(*prob) - 1])
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
    printf("QSopt_ex returned an unexpected status: %d\n", qsx->status);
    solution->status = EXTERNAL_SIMPLEX_ERROR;
    break;
  }

  mpq_clear(delta);
}

void qsx_solve(simplex_solver_t *solver, external_solution_t *solution) {
  qsx_t qsx;
  qsx_init(&qsx);
  qsx_init_vars(solver, &qsx);
  qsx_build_problem(solver, &qsx);
  qsx_solve_lp(solver, &qsx, solution);
  extract_solution(solver, &qsx, solution);
  qsx_clear(&qsx);
}
