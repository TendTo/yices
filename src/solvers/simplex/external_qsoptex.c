/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_qsoptex class.
 */
#include "external_qsoptex.h"

#ifndef HAVE_QSOPTEX
#error                                                                         \
    "QSopt_ex library is not available. Please install it to use this feature."
#endif

#include "frontend/smt2/smt2_commands.h"
#include "io/term_printer.h"
#include "qsopt_ex/QSopt_ex.h"
#include "solvers/simplex/external_simplex.h"
#include "solvers/simplex/simplex_types.h"
#include "utils/memalloc.h"
#include <stdbool.h>

typedef struct {
  mpq_QSprob prob;     ///< The QSopt_ex LP problem
  SolverStatus status; ///< Status of the LP problem after solving

  thvar_t *col_to_var; ///< Map from column index in the LP to theory var
  thvar_t *row_to_var; ///< Map from row index in the LP to theory var

  int32_t *var_to_col; ///< Map from theory var to column index in the LP
  int32_t *var_to_row; ///< Map from theory var to row index in the LP

  int32_t n_struct; ///< Number of structural variables
  int32_t n_aux;    ///< Number of auxiliary variables

  mpq_t *rhs;    ///< Right-hand side of the constraints
  mpq_t *range;  ///< Range of the constraints
  char *sense;   ///< Sense of the constraints ('E', 'G', 'L', or 'R')
  mpq_t *x;      ///< Temporary rational for storing the solution
  mpq_t *y;      ///< Temporary rational for storing the dual solution
  QSbasis basis; ///< Basis information for the solution
} qsx_t;

static const int pivot_threshold = 10000;
static bool qsx_started = false;

/**
 * Checks whether a theory variable is already represented as a column in the
 * QSopt_ex problem.
 * @param qsx The QSopt_ex problem wrapper containing column-to-variable maps.
 * @param v The theory variable to inspect.
 * @return true if the variable has a mapped column index; otherwise false.
 */
static bool var_in_columns(const qsx_t *const qsx, const thvar_t v) {
  return qsx->var_to_col[v] != -1;
}

/**
 * Determines whether a theory variable may be encoded as a structural column in
 * the LP model.
 * We only care about free variables, i.e., those that appear
 * in the SMT definition.
 * @param vtbl The arithmetic variable table containing the variable definition.
 * @param v The theory variable to inspect.
 * @return true if the variable is free; otherwise false.
 */
static bool var_is_valid_column(arith_vartable_t *const vtbl, const thvar_t v) {
  if (arith_var_is_free(vtbl, v))
    return true;
  return false;
}

/**
 * Determines whether a theory variable should be encoded as an auxiliary row in
 * the LP model.
 * We only care about polynomials that are not constants.
 * E.g., p := a.x or p := a.x + c, but not p := c, where c is a constant.
 * @param vtbl The arithmetic variable table containing the variable definition.
 * @param v The theory variable to inspect.
 * @return true if the variable is a polynomial-defined non-constant row; false
 * otherwise.
 */
static bool var_is_valid_row(arith_vartable_t *const vtbl, const thvar_t v) {
  if (!arith_var_def_is_poly(vtbl, v))
    return false;
  const polynomial_t *const p = arith_var_poly_def(vtbl, v);
  assert(p);
  return !(p->nterms == 1 && p->mono[0].var == const_idx);
}

/**
 * Initializes the global QSopt_ex runtime if it has not already been started.
 * This function is idempotent and ensures the underlying QSopt_ex exact solver
 * is initialized before building or solving LP problems.
 */
static void global_qsx_start() {
  if (qsx_started)
    return;
  qsx_started = true;
  QSexactStart();
}

void global_qsx_clear() {
  if (!qsx_started)
    return;
  QSexactClear();
  qsx_started = false;
}

/**
 * Releases any previously allocated basis metadata for a QSopt_ex LP instance.
 * @param basis The basis structure whose internal arrays should be freed and
 * reset.
 */
static void basis_clear(QSbasis *const basis) {
  safe_free(basis->cstat);
  safe_free(basis->rstat);
  basis->cstat = NULL;
  basis->rstat = NULL;
  basis->nstruct = 0;
  basis->nrows = 0;
}

/**
 * Creates a new QSopt_ex LP problem wrapper and configures solver parameters.
 * @param qsx The wrapper to initialize.
 */
static void qsx_init(qsx_t *qsx) {
  global_qsx_start();
  memset(qsx, 0, sizeof(qsx_t));
  qsx->prob = mpq_QScreate_prob(NULL, QS_MIN);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  mpq_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_DISPLAY,
                  __smt2_globals.verbosity);
}

/**
 * Allocates the QSopt_ex column/row mappings and temporary numeric arrays for a
 * simplex solver.
 * @param solver The simplex solver whose arithmetic variables will be
 * translated to LP variables.
 * @param qsx The QSopt_ex wrapper that receives the allocated arrays and
 * indexes.
 */
static void qsx_init_vars(simplex_solver_t *const solver, qsx_t *qsx) {
  const uint32_t nvars = solver->vtbl.nvars;

  // Set the number of auxiliary variables in the QSopt_ex problem,
  // which is equal to the rows of the LP problem,
  // and the number of structural variables,
  // which is equal to the columns of the LP problem.
  for (thvar_t v = 0; v < nvars; v++) {
    if (var_is_valid_row(&solver->vtbl, v)) {
      qsx->n_aux++;
    } else if (var_is_valid_column(&solver->vtbl, v)) {
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

/**
 * Frees all memory owned by a QSopt_ex wrapper and clears the stored basis.
 * @param qsx The QSopt_ex wrapper to destroy.
 */
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
}

/**
 * Adds all free arithmetic variables as structural columns in the QSopt_ex LP.
 * Each variable that is valid as a column is assigned the corresponding finite
 * or infinite lower/upper bounds from the simplex solver, and the mapping
 * arrays in @p qsx are updated so later row-building logic can refer back to
 * the original theory variable identifiers. In epsilon mode, any strict bound
 * is made stricter by using an hardcoded value @f \epsilon @f.
 * @param solver The simplex solver containing the variable bounds and
 * definitions.
 * @param qsx The QSopt_ex problem wrapper receiving the new columns.
 */
static void add_cols_epsilon(simplex_solver_t *const solver,
                             const qsx_t *const qsx) {
  mpq_QSprob prob = qsx->prob;

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {

    // Free variables. They come from the SMT input. Encode them as columns.
    if (var_is_valid_column(&solver->vtbl, v)) {
      bound_type_t lb, ub;
      get_bound(solver, v, true, &lb);
      get_bound(solver, v, false, &ub);

      qsx->col_to_var[mpq_QSget_colcount(prob)] = v;
      qsx->var_to_col[v] = mpq_QSget_colcount(prob);
      mpq_QSnew_col(prob, mpq_oneLpNum, lb.is_finite ? lb.val : mpq_NINFTY,
                    ub.is_finite ? ub.val : mpq_INFTY, NULL);

      bound_type_clear(&lb);
      bound_type_clear(&ub);
    }

    // If the variable is not free, it is an auxiliary variable.
    // We will encode those as rows later.
  }
}

typedef struct row_data_s {
  int *col_idxs;
  mpq_t *values;
  int row_idx;
  int col_idxs_idx;
  int values_idx;
} row_data_t;

/**
 * Expands a polynomial-defined arithmetic variable into the sparse row data
 * used by QSopt_ex. The function recursively walks the polynomial, adds any
 * coefficient with a structural variable to the current row, and folds
 * constants into the row RHS when the row is bounded. This allows an SMT
 * arithmetic relation to be converted into a single LP row.
 * @param solver The simplex solver containing the variable definitions.
 * @param qsx The QSopt_ex wrapper holding the column and row mappings.
 * @param v The theory variable whose polynomial contribution is being emitted.
 * @param row_data Aggregated row data that stores column indices and values.
 * @param p_coeff Optional parent coefficient to multiply into this polynomial.
 * @param bounded Indicates whether the row is bounded and therefore should
 * subtract constant terms from the matching RHS entry.
 * @return The number of non-zero coefficients added to the row.
 */
static int monomials_to_row(simplex_solver_t *const solver,
                            const qsx_t *const qsx, const thvar_t v,
                            row_data_t *const row_data,
                            const rational_t *const p_coeff,
                            const bool bounded) {

  const int row_idx = row_data->row_idx;
  int num_non_zeros = 0;
  const polynomial_t *const p = arith_var_poly_def(&solver->vtbl, v);
  assert(p);

  for (uint32_t i = 0; i < p->nterms; i++) {
    const monomial_t *const mono = &p->mono[i];
    const thvar_t x = mono->var;

    rational_t temp_coeff;
    q_init(&temp_coeff);
    if (p_coeff != NULL) {
      q_set(&temp_coeff, &mono->coeff);
      q_mul(&temp_coeff, p_coeff);
    }
    const rational_t *const coeff =
        p_coeff == NULL ? &mono->coeff : &temp_coeff;
    assert(!q_is_zero(coeff));

    if (x == const_idx) {
      // Use the constant to update the right-hand side of the row
      assert(p->nterms > 1); // Constant with only one term are fixed columns
      if (bounded)
        mpq_q_sub(qsx->rhs[row_idx], qsx->rhs[row_idx], coeff);
    } else if (var_in_columns(qsx, x)) {
      assert(var_is_valid_column(&solver->vtbl, x));
      // Add var coefficient
      num_non_zeros++;
      row_data->col_idxs[row_data->col_idxs_idx++] = qsx->var_to_col[x];
      init_and_copy_to_gmp(row_data->values[row_data->values_idx++], coeff);
    } else {
      assert(arith_var_def_is_poly(&solver->vtbl, x));
      num_non_zeros +=
          monomials_to_row(solver, qsx, x, row_data, coeff, bounded);
    }

    q_clear(&temp_coeff);
  }

  return num_non_zeros;
}

#pragma region Epsilon mode

/**
 * Adds all valid arithmetic row definitions from the simplex solver to the
 * QSopt_ex LP as ranged rows.
 * For each accepted auxiliary variable, the function translates the bound state
 * into the row RHS, sense and range, then fills in the sparse coefficient
 * matrix produced by @ref monomials_to_row.
 * We ignore constant rows (e.g., p := c)
 * and unbounded rows (e.g., p: ... with -inf < p < inf).
 * In epsilon mode, any strict constraint is made stricter
 * by using an hardcoded value @f \epsilon @f.
 * @param solver The simplex solver containing the row definitions and bounds.
 * @param qsx The QSopt_ex LP wrapper receiving the encoded rows.
 */
static void add_rows_epsilon(simplex_solver_t *const solver,
                             const qsx_t *const qsx) {
  mpq_QSprob prob = qsx->prob;
  int non_zero_per_row[qsx->n_aux];
  int begin_row_idx[qsx->n_aux];
  int *const col_idxs = safe_malloc(sizeof(int) * qsx->n_struct * qsx->n_aux);
  mpq_t *const values = safe_malloc(sizeof(mpq_t) * qsx->n_struct * qsx->n_aux);

  int32_t non_zero_per_row_idx = 0;

  row_data_t row_data = {.col_idxs = col_idxs,
                         .values = values,
                         .row_idx = 0,
                         .col_idxs_idx = 0,
                         .values_idx = 0};

  // Add rows to the LP problem
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < n_vars; v++) {
    const int r = row_data.row_idx;
    // Skip structural variables and constants
    if (!var_is_valid_row(&solver->vtbl, v)) {
      continue;
    }

    // where the non-zero columns of the row are stored
    begin_row_idx[r] = row_data.col_idxs_idx;

    // TODO: may be unnecessary if 'R' sense is not used
    mpq_set(qsx->range[r], mpq_zeroLpNum);

    // Add row range
    bound_type_t lb, ub;
    get_bound(solver, v, true, &lb);
    get_bound(solver, v, false, &ub);

    if (lb.is_finite && ub.is_finite) // Bounded
    {
      if (mpq_equal(lb.val, ub.val)) {
        mpq_set(qsx->rhs[r], lb.val);
        qsx->sense[r] = 'E';
      } else {
        mpq_set(qsx->rhs[r], lb.val);
        mpq_set(qsx->range[r], ub.val);
        mpq_sub(qsx->range[r], qsx->range[r], qsx->rhs[r]);
        if (__smt2_globals.epsilon_mode && lb.is_strict) {
          mpq_sub_si(qsx->range[r], epsilon_num, epsilon_den);
        }
        qsx->sense[r] = 'R';
      }
      // printf("Adding bounded row %d with lower bound %s and upper bound
      // %s\n", row_idx, mpq_get_str(NULL, 10, d_rhs[row_idx]),
      // mpq_get_str(NULL, 10, d_range[row_idx]));
    } else if (lb.is_finite) // Only lower bound
    {
      // printf("Adding lower bounded row %d with lower bound %s\n", row_idx,
      // mpq_get_str(NULL, 10, lb.val));
      mpq_set(qsx->rhs[r], lb.val);
      qsx->sense[r] = 'G';
    } else if (ub.is_finite) // Only upper bound
    {
      // printf("Adding upper bounded row %d with upper bound %s\n", r,
      //        mpq_get_str(NULL, 10, ub.val));
      mpq_set(qsx->rhs[r], ub.val);
      qsx->sense[r] = 'L';
    } else // Unbounded row
    {
#if 1
      bound_type_clear(&lb);
      bound_type_clear(&ub);
      continue;
#else
      mpq_set(qsx->rhs[r], mpq_NINFTY);
      qsx->sense[r] = 'G';
#endif
    }

    bound_type_clear(&lb);
    bound_type_clear(&ub);

    const int num_non_zeros = monomials_to_row(solver, qsx, v, &row_data, NULL,
                                               lb.is_finite || ub.is_finite);

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[non_zero_per_row_idx++] = num_non_zeros;

    // Add the new row to the map
    qsx->row_to_var[r] = v;
    qsx->var_to_row[v] = r;
    row_data.row_idx++;
  }

  mpq_QSadd_ranged_rows(prob, non_zero_per_row_idx, non_zero_per_row,
                        begin_row_idx, col_idxs, values, qsx->rhs, qsx->sense,
                        qsx->range, NULL);

  mpq_vector_clear(values, row_data.values_idx);
  safe_free(col_idxs);
  safe_free(values);
}

/**
 * Extracts the value of a structural variable from the solved QSopt_ex LP and
 * stores it in the external solution object.
 * @param solver The simplex solver used to interpret the variable bounds.
 * @param qsx The solved QSopt_ex problem containing the LP basis and values.
 * @param sol The destination solution record to update.
 * @param c The LP column index to extract.
 */
static void extract_col_value_epsilon(simplex_solver_t *const solver,
                                      qsx_t *const qsx,
                                      external_solution_t *const sol,
                                      const int c) {
  xrational_t *x = sol->x;
  const thvar_t v = qsx->col_to_var[c];
  const char var_status = qsx->basis.cstat[c];
  // from thvar to col index

  if (var_status == QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->b_vars, v);
  else
    int_bvset_add(&sol->nb_vars, v);

  switch (var_status) {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    // Start by setting the current basic result
    xq_set_mpq_prenormalize(sol->x + v, qsx->x[c]);
    // Ensure the result is within the bounds of the variable, if any
    if (is_below_or_eq_lb(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_LOWER;
    } else if (is_above_or_eq_ub(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_UPPER;
    }
    break;
    // For non-basic variables we know the value is at a bound
    // and we can use the d_vars/proper LP bounds directly
  case QS_COL_BSTAT_LOWER:
    if (!has_any_bound(solver, v)) {
      // Free rows are set to lower bound, so we leave the value as is
      // (there is no lower bound to set them to)
      xq_set_mpq_prenormalize(sol->x + v, qsx->x[c]);
      assert(xq_is_zero(sol->x + v));
    } else {
      assert(has_lb(solver, v));
      sol->bounds[v] = VAR_BOUND_AT_LOWER;
    }
    break;
  case QS_COL_BSTAT_UPPER:
    assert(has_ub(solver, v));
    sol->bounds[v] = VAR_BOUND_AT_UPPER;
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, var_status);
    exit(1);
  }
}

/**
 * Computes the value of an auxiliary row variable from the solved QSopt_ex row
 * data and stores it in the output solution.
 * @param qsx The solved QSopt_ex problem that stores the row RHS and dual
 * values.
 * @param sol The destination solution object.
 * @param r The row index to convert back to a theory variable value.
 */
static void row_value_to_solution(const qsx_t *const qsx,
                                  const external_solution_t *const sol,
                                  const int r) {
  const thvar_t v = qsx->row_to_var[r];
  mpq_t rhs;
  mpq_init(rhs);
  mpq_set(rhs, qsx->rhs[r]);
  if (qsx->sense[r] == 'L') {
    mpq_sub(rhs, rhs, qsx->y[r]);
  } else {
    mpq_add(rhs, rhs, qsx->y[r]);
  }
  xq_set_mpq_prenormalize(sol->x + v, rhs);
  mpq_clear(rhs);
}

/**
 * Extracts the value of an auxiliary row variable from the solved LP and
 * updates the bound state in the external solution.
 * @param solver The simplex solver that defines the row bounds.
 * @param qsx The solved QSopt_ex problem containing the basis and row data.
 * @param sol The solution object to populate.
 * @param r The row index to extract.
 */
static void extract_row_value_epsilon(simplex_solver_t *const solver,
                                      qsx_t *const qsx,
                                      external_solution_t *const sol,
                                      const int r) {
  xrational_t *x = sol->x;
  var_bound_state_t *bounds = sol->bounds;
  const thvar_t v = qsx->row_to_var[r];
  const char var_status = qsx->basis.rstat[r];

  if (var_status == QS_COL_BSTAT_BASIC)
    int_bvset_add(&sol->b_vars, v);
  else
    int_bvset_add(&sol->nb_vars, v);

  switch (var_status) {
  // If we are dealing with a basic variable, we necessarily need to get its
  // value from the solved problem.
  case QS_COL_BSTAT_BASIC:
  case QS_COL_BSTAT_FREE: // Shared with basic
    row_value_to_solution(qsx, sol, r);
    if (is_below_or_eq_lb(solver, v, x + v)) {
      bounds[v] = VAR_BOUND_AT_LOWER;
    } else if (is_above_or_eq_ub(solver, v, x + v)) {
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
      row_value_to_solution(qsx, sol, r);
    } else {
      if (qsx->sense[r] == 'G' || qsx->sense[r] == 'R') {
        assert(has_lb(solver, v));
        bounds[v] = VAR_BOUND_AT_LOWER;
      } else if (qsx->sense[r] == 'L') {
        assert(has_ub(solver, v));
        bounds[v] = VAR_BOUND_AT_UPPER;
      } else {
        assert(qsx->sense[r] == 'E');
        bounds[v] = VAR_BOUND_AT_LOWER;
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

/**
 * Extracts every solved value from the epsilon-mode QSopt_ex LP into the
 * external solution record.
 * @param solver The simplex solver whose bounds are used to validate each
 * value.
 * @param qsx The solved QSopt_ex LP instance to read from.
 * @param sol The output solution object to populate.
 */
static void extract_solution_epsilon(simplex_solver_t *solver, qsx_t *qsx,
                                     external_solution_t *sol) {
  const mpq_QSprob *prob = &qsx->prob;

  for (int col_idx = 0; col_idx < mpq_QSget_colcount(*prob); col_idx++) {
    extract_col_value_epsilon(solver, qsx, sol, col_idx);
  }
  for (int row_idx = 0; row_idx < mpq_QSget_rowcount(*prob); row_idx++) {
    extract_row_value_epsilon(solver, qsx, sol, row_idx);
  }
}

/**
 * Builds the LP encoding for the epsilon-mode simplex problem.
 * @param solver The simplex solver whose structural variables and constraints
 * define the LP.
 * @param qsx The QSopt_ex wrapper to populate with columns and rows.
 */
static void qsx_build_problem_epsilon(simplex_solver_t *const solver,
                                      qsx_t *const qsx) {
  add_cols_epsilon(solver, qsx);
  add_rows_epsilon(solver, qsx);
}

#pragma endregion

#pragma region Strict mode

/**
 * Reserved placeholder for strict-mode column construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the variable definitions.
 * @param qsx The QSopt_ex wrapper that would receive the strict-mode columns.
 */
static void add_cols_strict(simplex_solver_t *const solver, qsx_t *const qsx) {}

/**
 * Reserved placeholder for strict-mode row construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the row definitions.
 * @param qsx The QSopt_ex wrapper that would receive the strict-mode rows.
 */
static void add_rows_strict(simplex_solver_t *const solver, qsx_t *const qsx) {}

/**
 * Builds the strict-mode LP representation used when strict mode is enabled.
 * @param solver The simplex solver whose constraints define the problem.
 * @param qsx The QSopt_ex wrapper to populate.
 */
static void qsx_build_problem_strict(simplex_solver_t *const solver,
                                     qsx_t *const qsx) {
  add_cols_strict(solver, qsx);
  add_rows_strict(solver, qsx);
}

/**
 * Placeholder extractor for strict-mode structural variable values.
 * @param solver The simplex solver corresponding to the variable bounds.
 * @param qsx The solved QSopt_ex problem.
 * @param sol The output solution to populate.
 * @param c The LP column index to extract.
 */
static void extract_col_value_strict(simplex_solver_t *const solver,
                                     qsx_t *const qsx,
                                     external_solution_t *const sol,
                                     const int c) {}

/**
 * Placeholder extractor for strict-mode auxiliary row values.
 * @param solver The simplex solver corresponding to the row bounds.
 * @param qsx The solved QSopt_ex problem.
 * @param sol The output solution to populate.
 * @param r The LP row index to extract.
 */
static void extract_row_value_strict(simplex_solver_t *const solver,
                                     qsx_t *const qsx,
                                     external_solution_t *const sol,
                                     const int r) {}

/**
 * Extracts every value from a strict-mode LP solution into the external result.
 * @param solver The simplex solver defining the model.
 * @param qsx The solved QSopt_ex problem.
 * @param sol The output solution to fill.
 */
static void extract_solution_strict(simplex_solver_t *solver, qsx_t *qsx,
                                    external_solution_t *sol) {
  const mpq_QSprob *prob = &qsx->prob;

  for (int col_idx = 0; col_idx < mpq_QSget_colcount(*prob); col_idx++) {
    extract_col_value_strict(solver, qsx, sol, col_idx);
  }
  for (int row_idx = 0; row_idx < mpq_QSget_rowcount(*prob); row_idx++) {
    extract_row_value_strict(solver, qsx, sol, row_idx);
  }
}

#pragma endregion

/**
 * Solves the current QSopt_ex LP with delta-simplex and records solver status.
 * The function updates the solver statistics with the precision and delta
 * values reached during the solve and sets the corresponding external status
 * code in @p solution.
 * @param solver The simplex solver collecting performance statistics.
 * @param qsx The QSopt_ex LP instance to solve.
 * @param solution The output structure receiving the solved status and variable
 * count.
 */
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
    trace_printf(solver->core->trace, 10,
                 "QSopt_ex returned an unexpected status: %d\n", qsx->status);
    solution->status = EXTERNAL_SIMPLEX_ERROR;
    break;
  }

  mpq_clear(delta);
}

/**
 * Solves the arithmetic simplex problem using the QSopt_ex backend.
 * The function initializes a QSopt_ex LP wrapper, encodes the current model in
 * either epsilon or strict mode, solves it, and, when a feasible or infeasible
 * result is reported, extracts the variable assignments into the provided
 * external solution object.
 * @param solver The simplex solver containing the current arithmetic model.
 * @param sol The output solution record to be filled with the solve result.
 */
void qsx_solve(simplex_solver_t *solver, external_solution_t *sol) {
  qsx_t qsx;
  qsx_init(&qsx);
  qsx_init_vars(solver, &qsx);
  if (__smt2_globals.epsilon_mode)
    qsx_build_problem_epsilon(solver, &qsx);
  else
    qsx_build_problem_strict(solver, &qsx);
#if 0
  mpq_QSdump_prob(qsx->prob);
  static int i = 0;
  char filename[256];
  snprintf(
      filename, sizeof(filename),
      "/home/campus.ncl.ac.uk/c3054737/Programming/phd/yices2/qsproblem_%d.lp",
      i);
  mpq_QSwrite_prob(qsx->prob, filename, "LP");
  i++;
#endif
  qsx_solve_lp(solver, &qsx, sol);
  // Only extract a solution if the external solver found a valid one
  if (sol->status == EXTERNAL_SIMPLEX_FEASIBLE ||
      sol->status == EXTERNAL_SIMPLEX_INFEASIBLE) {
    if (__smt2_globals.epsilon_mode)
      extract_solution_epsilon(solver, &qsx, sol);
    else
      extract_solution_strict(solver, &qsx, sol);
  }
  qsx_clear(&qsx);
}
