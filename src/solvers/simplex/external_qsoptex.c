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

#define USE_MATRIX 1

#include "frontend/smt2/smt2_commands.h"
#include "io/term_printer.h"
#include "qsopt_ex/QSopt_ex.h"
#include "solvers/simplex/external_simplex.h"
#include "solvers/simplex/simplex_types.h"
#include "utils/cputime.h"
#include "utils/memalloc.h"
#include <stdbool.h>

typedef struct {
  rat_QSprob prob;     ///< The QSopt_ex LP problem
  SolverStatus status; ///< Status of the LP problem after solving

  thvar_t *col_to_var; ///< Map from column index in the LP to theory var
  thvar_t *row_to_var; ///< Map from row index in the LP to theory var

  int32_t *var_to_col; ///< Map from theory var to column index in the LP
  int32_t *var_to_row; ///< Map from theory var to row index in the LP

  int32_t n_cols; ///< Number of estimated LP columns
  int32_t n_rows; ///< Number of estimated LP rows

  rat_t *rhs;    ///< Right-hand side of the constraints
  rat_t *range;  ///< Range of the constraints
  char *sense;   ///< Sense of the constraints ('E', 'G', 'L', or 'R')
  rat_t *x;      ///< Temporary rational for storing the solution
  rat_t *y;      ///< Temporary rational for storing the dual solution
  QSbasis basis; ///< Basis information for the solution
} qsx_t;

/** Maximum number of pivots before LP termination */
static const int pivot_threshold = 1000000;
/** Global flag indicating whether the QSopt_ex runtime has been initialized */
static bool qsx_started = false;
/** Global variable representing the rational number -1 for LP computations */
static rat_t rat_negoneLpNum;

static inline void rat_set_q(rat_t rat, const rational_t *const q) {
  if (is_rat32(q)) {
    rat_set_int32(rat, get_num(q), get_den(q));
  } else {
    rat_set_mpq(rat, get_gmp(q));
  }
}

static inline void q_set_rat(rational_t *const q, const rat_t rat) {
  if (rat_is_rat32(rat)) {
    q_set_int32(q, rat_get_num(rat), rat_get_den(rat));
  } else {
    q_set_mpq(q, rat_get_mpq(rat));
  }
}

static inline void xq_set_rat(xrational_t *r, const rat_t rat) {
  q_set_rat(&r->main, rat);
  q_clear(&r->delta);
}

static inline bool is_strict_var_zero(rat_t x) {
  return __smt2_globals.delta < 0 && !__smt2_globals.epsilon_mode &&
         rat_is_zero(x);
}

static inline void rat_add_q(rat_t rat, const rational_t *q) {
  if (is_rat32(q)) {
    rat_add_si(rat, get_num(q), get_den(q));
  } else if (rat_is_gmp(rat)) {
    mpq_sub(rat_get_mpq(rat), rat_get_mpq(rat), get_gmp(q));
  } else {
    rat_t temp;
    rat_init(temp);
    rat_set_mpq(temp, get_gmp(q));
    rat_add_self(rat, temp);
    rat_clear(temp);
  }
}
static inline void rat_sub_q(rat_t rat, const rational_t *q) {
  if (is_rat32(q)) {
    rat_sub_si(rat, get_num(q), get_den(q));
  } else if (rat_is_gmp(rat)) {
    mpq_sub(rat_get_mpq(rat), rat_get_mpq(rat), get_gmp(q));
  } else {
    rat_t temp;
    rat_init(temp);
    rat_set_mpq(temp, get_gmp(q));
    rat_sub_self(rat, temp);
    rat_clear(temp);
  }
}

static const bool LOWER_BOUND = true;
static const bool UPPER_BOUND = false;

// TODO: REMOVE
static inline void print_rat_vector(const rat_t v[], const int n,
                                    const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    rat_print(stdout, v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

static rat_ptr rat_get_bound(const simplex_solver_t *const solver,
                             const thvar_t v, const bool is_lower_bound,
                             rat_t bound) {
  const int32_t bound_idx = is_lower_bound ? solver->vtbl.lower_index[v]
                                           : solver->vtbl.upper_index[v];
  xrational_t *const bounds = solver->bstack.bound;
  assert(bound); // Bound must be non-null

  const bool is_finite = bound_idx > -1;
  if (!is_finite)
    return is_lower_bound ? rat_NINFTY : rat_INFTY;

  const bool is_strict =
      __smt2_globals.delta < 0 &&
      (is_finite ? !xq_is_rational(&bounds[bound_idx]) : false);

  assert(bound_idx >= 0 && bound_idx < solver->bstack.size);
  const rational_t *val = &bounds[bound_idx].main;
  rat_set_q(bound, val);

  if (__smt2_globals.epsilon_mode && is_strict) {
    // Adjust the bounds with epsilon
    if (is_lower_bound) {
      rat_add_si(bound, epsilon_num, epsilon_den);
    } else {
      rat_sub_si(bound, epsilon_num, epsilon_den);
    }
  }
  return bound;
}

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
 * @param solver The simplex solver containing the variable table and bounds.
 * @param v The theory variable to inspect.
 * @return true if the variable is free; otherwise false.
 */
static bool var_is_valid_column(simplex_solver_t *const solver,
                                const thvar_t v) {
  if (arith_var_is_free(&solver->vtbl, v))
    return true;
  return false;
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
  rat_init(rat_negoneLpNum);
  rat_set_int32(rat_negoneLpNum, -1, 1);
  QSexactStart();
}

void global_qsx_clear() {
  if (!qsx_started)
    return;
  QSexactClear();
  rat_clear(rat_negoneLpNum);
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

static external_simplex_status_t
qsx_status_to_sol_status(const qsx_t *const qsx) {
  switch (qsx->status) {
  case QS_LP_OPTIMAL:
  case QS_LP_FEASIBLE:
  case QS_LP_DELTA_OPTIMAL:
  case QS_LP_DELTA_FEASIBLE:
  case QS_LP_UNBOUNDED:
    return is_strict_var_zero(qsx->x[qsx->n_cols]) ? EXTERNAL_SIMPLEX_INFEASIBLE
                                                   : EXTERNAL_SIMPLEX_FEASIBLE;
    break;
  case QS_LP_INFEASIBLE:
    return EXTERNAL_SIMPLEX_INFEASIBLE;
  case QS_LP_ITER_LIMIT:
  case QS_LP_TIME_LIMIT:
    return EXTERNAL_SIMPLEX_EXHAUSTED;
    break;
  default:
    return EXTERNAL_SIMPLEX_ERROR;
  }
}

static bool should_update_max_delta(const qsx_t *const qsx) {
  if (__smt2_globals.delta < 0)
    return false;
  switch (qsx->status) {
  case QS_LP_OPTIMAL:
  case QS_LP_FEASIBLE:
  case QS_LP_DELTA_OPTIMAL:
  case QS_LP_DELTA_FEASIBLE:
  case QS_LP_UNBOUNDED:
    return !is_strict_var_zero(qsx->x[qsx->n_cols]);
    break;
  default:
    return false;
  }
}

/**
 * Creates a new QSopt_ex LP problem wrapper and configures solver parameters.
 * @param qsx The wrapper to initialize.
 */
static void qsx_init(qsx_t *qsx) {
  global_qsx_start();
  memset(qsx, 0, sizeof(qsx_t));
  qsx->prob = rat_QScreate_prob(NULL, QS_MIN);
  rat_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  rat_QSset_param(qsx->prob, QS_PARAM_SIMPLEX_DISPLAY,
                  __smt2_globals.verbosity);
}

static void qsx_estimate_n_cols_and_rows_epsilon(simplex_solver_t *const solver,
                                                 qsx_t *qsx) {
  assert(__smt2_globals.epsilon_mode);
  assert(qsx->n_cols == 0);
  assert(qsx->n_rows == 0);
  const uint32_t nvars = solver->vtbl.nvars;

  for (thvar_t v = 0; v < nvars; v++) {
    if (var_is_valid_row(solver, v)) {
      qsx->n_rows++;
    } else if (var_is_valid_column(solver, v)) {
      qsx->n_cols++;
    }
  }
}

static void qsx_estimate_n_cols_and_rows_strict(simplex_solver_t *const solver,
                                                qsx_t *qsx) {
  assert(!__smt2_globals.epsilon_mode);
  assert(qsx->n_cols == 0);
  assert(qsx->n_rows == 0);
  const uint32_t nvars = solver->vtbl.nvars;
  for (thvar_t v = 0; v < nvars; v++) {
    if (var_is_valid_row(solver, v)) {
      qsx->n_rows++;
      if ((has_strict_lb(solver, v) || has_strict_ub(solver, v)) &&
          has_lb(solver, v) && has_ub(solver, v)) {
        qsx->n_rows++;
      }
    } else if (var_is_valid_column(solver, v)) {
      qsx->n_cols++;
      // If epsilon mode is disables (i.e., we are using strict mode),
      // then we need to encode the strict bounds on the free var
      // by using some strict constraint
      if (has_strict_lb(solver, v)) {
        qsx->n_rows++;
      }
      if (has_strict_ub(solver, v)) {
        qsx->n_rows++;
      }
    }
  }
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
  qsx->n_cols = 0;
  qsx->n_rows = 0;
#if USE_MATRIX // Only estimate rows and cols if we are not using the matrix
  qsx->n_cols = (int)solver->matrix.ncolumns - 1; // Exclude the constant column
  qsx->n_rows = (int)solver->matrix.nrows +
                (__smt2_globals.epsilon_mode ? 0 : num_strict_all_vars(solver));
#else
  if (__smt2_globals.epsilon_mode) {
    qsx_estimate_n_cols_and_rows_epsilon(solver, qsx);
  } else {
    qsx_estimate_n_cols_and_rows_strict(solver, qsx);
  }
#endif

  qsx->col_to_var = safe_malloc(qsx->n_cols * sizeof(thvar_t));
  qsx->row_to_var = safe_malloc(qsx->n_rows * sizeof(thvar_t));
  qsx->var_to_col = safe_malloc(nvars * sizeof(uint32_t));
  qsx->var_to_row = safe_malloc(nvars * sizeof(uint32_t));
  // We are adding an additional variable to the LP problem
  // to collect the value of the strict var, if needed.
  // There is no need do add it anywhere else
  qsx->x = new_rat_array(qsx->n_cols + 1);
  qsx->y = new_rat_array(qsx->n_rows);
  qsx->range = new_rat_array(qsx->n_rows);
  qsx->rhs = new_rat_array(qsx->n_rows);
  qsx->sense = safe_malloc(qsx->n_rows * sizeof(char));

  for (uint32_t i = 0; i < qsx->n_cols; i++) {
    qsx->col_to_var[i] = null_idx;
  }
  rat_set(qsx->x[qsx->n_cols], rat_oneLpNum); // Initialize the strict var

  for (uint32_t i = 0; i < qsx->n_rows; i++) {
    qsx->row_to_var[i] = null_idx;
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
  rat_QSfree_prob(qsx->prob);
  safe_free(qsx->col_to_var);
  safe_free(qsx->row_to_var);
  safe_free(qsx->var_to_col);
  safe_free(qsx->var_to_row);
  safe_free(qsx->sense);
  free_rat_array(qsx->x, qsx->n_cols + 1);
  free_rat_array(qsx->y, qsx->n_rows);
  free_rat_array(qsx->range, qsx->n_rows);
  free_rat_array(qsx->rhs, qsx->n_rows);
}

typedef struct row_data_s {
  int *col_idxs;
  rat_t *values;
  int row_idx;
  int col_idxs_idx;
  int values_idx;
} row_data_t;

typedef struct row_accumulator_s {
  rat_t *values;
  int *values_idxs;
  int n_values;
} row_accumulator_t;

static void row_accumulator_init(row_accumulator_t *const accumulator,
                                 const int n_cols) {
  accumulator->values = safe_malloc(n_cols * sizeof(rat_t));
  memset(accumulator->values, 0, n_cols * sizeof(rat_t));
  accumulator->values_idxs = safe_malloc(n_cols * sizeof(int));
  accumulator->n_values = 0;
}

static void row_accumulator_clear(row_accumulator_t *const accumulator,
                                  const bool clear_mpqs) {
  if (clear_mpqs) {
    for (int i = 0; i < accumulator->n_values; i++) {
      rat_clear(accumulator->values[accumulator->values_idxs[i]]);
    }
  }
  safe_free(accumulator->values);
  safe_free(accumulator->values_idxs);
  accumulator->values = NULL;
  accumulator->values_idxs = NULL;
  accumulator->n_values = 0;
}

static void row_accumulator_add_mpq(row_accumulator_t *const accumulator,
                                    const int col_idx, const mpq_t value) {
  if (rat_is_uninitialized(accumulator->values[col_idx])) {
    rat_init(accumulator->values[col_idx]);
    rat_set_mpq(accumulator->values[col_idx], value);
    accumulator->values_idxs[accumulator->n_values++] = col_idx;
  } else {
    rat_add_mpq(accumulator->values[col_idx], value);
  }
}

static void row_accumulator_add_q(row_accumulator_t *const accumulator,
                                  const int col_idx, const rational_t *value) {
  if (is_ratgmp(value)) {
    row_accumulator_add_mpq(accumulator, col_idx, get_gmp(value));
  } else {
    if (rat_is_uninitialized(accumulator->values[col_idx])) {
      rat_init(accumulator->values[col_idx]);
      rat_set_int32(accumulator->values[col_idx], get_num(value),
                    get_den(value));
      accumulator->values_idxs[accumulator->n_values++] = col_idx;
    } else {
      rat_add_si(accumulator->values[col_idx], get_num(value), get_den(value));
    }
  }
}

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
 * @param accumulator Optional accumulator to collect non-zero coefficients for
 * the row.
 * @param p_coeff Optional parent coefficient to multiply into this polynomial.
 * @return The number of non-zero coefficients added to the row.
 */
static void monomials_to_row(simplex_solver_t *const solver,
                             const qsx_t *const qsx, const thvar_t v,
                             row_data_t *const row_data,
                             row_accumulator_t *const accumulator,
                             const rational_t *const p_coeff) {
  const int row_idx = row_data->row_idx;
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
      assert(p->nterms > 1); // Constant with only one term are ignored
      assert(has_any_bound(solver, v));
      rat_sub_q(qsx->rhs[row_idx], coeff);
    } else if (var_in_columns(qsx, x)) {
      assert(var_is_valid_column(solver, x));
      // Add var coefficient
      row_accumulator_add_q(accumulator, qsx->var_to_col[x], coeff);
    } else {
      assert(arith_var_def_is_poly(&solver->vtbl, x));
      monomials_to_row(solver, qsx, x, row_data, accumulator, coeff);
    }

    q_clear(&temp_coeff);
  }
}

static int polynomial_to_row(simplex_solver_t *const solver,
                             const qsx_t *const qsx, const thvar_t v,
                             row_data_t *const row_data) {
  row_accumulator_t accumulator;
  row_accumulator_init(&accumulator, qsx->n_cols);
  monomials_to_row(solver, qsx, v, row_data, &accumulator, NULL);
  const int num_non_zeros = accumulator.n_values;

  for (int i = 0; i < num_non_zeros; i++) {
    const int col_idx = accumulator.values_idxs[i];
    row_data->col_idxs[row_data->col_idxs_idx++] = col_idx;
    // Transfer ownership to the row_data values array
    memcpy(row_data->values[row_data->values_idx++],
           accumulator.values[col_idx], sizeof(rat_t));
  }

  // We do not need to clear the rat_t values in the accumulator
  // because they have been assigned to the row_data values array,
  // which will be cleared later.
  row_accumulator_clear(&accumulator, false);
  return num_non_zeros;
}

/**
 * Extracts the value of a structural variable from the solved QSopt_ex LP and
 * stores it in the external solution object.
 * @param solver The simplex solver used to interpret the variable bounds.
 * @param qsx The solved QSopt_ex problem containing the LP basis and values.
 * @param sol The destination solution record to update.
 * @param c The LP column index to extract.
 */
static void extract_col_value(simplex_solver_t *const solver, qsx_t *const qsx,
                              external_solution_t *const sol, const int c) {
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
    xq_set_rat(sol->x + v, qsx->x[c]);
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
      xq_set_rat(sol->x + v, qsx->x[c]);
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
  rat_t rhs;
  rat_init(rhs);
  rat_set(rhs, qsx->rhs[r]);
  if (qsx->sense[r] == 'L') {
    rat_sub_self(rhs, qsx->y[r]);
  } else {
    rat_add_self(rhs, qsx->y[r]);
  }
  xq_set_rat(sol->x + v, rhs);
  rat_clear(rhs);
}

/**
 * Extracts the value of an auxiliary row variable from the solved LP and
 * updates the bound state in the external solution.
 * @param solver The simplex solver that defines the row bounds.
 * @param qsx The solved QSopt_ex problem containing the basis and row data.
 * @param sol The solution object to populate.
 * @param r The row index to extract.
 */
static void extract_row_value(simplex_solver_t *const solver, qsx_t *const qsx,
                              external_solution_t *const sol, const int r) {
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

#pragma region Epsilon mode

#define GUESS_DIR 1
#if GUESS_DIR
static const rat_t *guess_dir(simplex_solver_t *const solver, const thvar_t v) {
  if (!has_any_bound(solver, v)) {
    return &rat_zeroLpNum;
  }
  if (has_lb(solver, v) && !has_ub(solver, v)) {
    return &rat_oneLpNum;
  }
  if (!has_lb(solver, v) && has_ub(solver, v)) {
    return &rat_negoneLpNum;
  }
  const int lb_sng = q_sgn(get_lb_main(solver, v));
  const int ub_sgn = q_sgn(get_ub_main(solver, v));

  if (ub_sgn != 0 && lb_sng == 0) {
    return &rat_oneLpNum;
  }
  if (ub_sgn == 0 && lb_sng != 0) {
    return &rat_negoneLpNum;
  }

  return &rat_zeroLpNum;
}
#else
static const rat_t *guess_dir(simplex_solver_t *const, const thvar_t) {
  return &rat_zeroLpNum;
}
#endif

#if USE_MATRIX

static void add_cols_epsilon(simplex_solver_t *const solver,
                             const qsx_t *const qsx) {
  assert(qsx->n_cols > 0);
  rat_QSprob prob = qsx->prob;
  rat_t temp_lb, temp_ub;
  rat_init_pair(temp_lb, temp_ub);

  // 0 is the constant column, which is not a variable
  for (thvar_t v = 1; v < solver->vtbl.nvars; v++) {
    rat_ptr lb = rat_get_bound(solver, v, LOWER_BOUND, temp_lb);
    rat_ptr ub = rat_get_bound(solver, v, UPPER_BOUND, temp_ub);
    assert(rat_is_gmp(lb) || rat_get_den(lb) > 0);
    assert(rat_is_gmp(ub) || rat_get_den(ub) > 0);

    const int n_cols = rat_QSget_colcount(prob);
    qsx->col_to_var[n_cols] = v;
    qsx->var_to_col[v] = n_cols;

#if 1 && !defined(NDEBUG)
    char buf[64];
    if (arith_var_is_int(&solver->vtbl, v)) {
      sprintf(buf, "i!%d", v);
    } else {
      sprintf(buf, "z!%d", v);
    }
    // sprintf(buf, "x%d", rat_QSget_colcount(prob));
#endif

    rat_QSnew_col(prob, *guess_dir(solver, v), lb, ub,
#if 1 && !defined(NDEBUG)
                  buf
#else
                  NULL
#endif
    );
  }
  rat_clear_pair(temp_lb, temp_ub);
}

static void add_rows_epsilon(simplex_solver_t *const solver,
                             const qsx_t *const qsx) {
  assert(qsx->n_cols > 0);
  matrix_t *const mat = &solver->matrix;
  rat_QSprob prob = qsx->prob;
#if 1 && !defined(NDEBUG)
  char **row_names = safe_malloc(sizeof(char *) * qsx->n_rows);
#endif

  int non_zero_per_row[mat->nrows];
  int begin_row_idx[mat->nrows];
  // TODO: it may be worth checking the number
  //  of non-zero elements in the matrix and allocating only that much
  int *col_idxs =
      safe_malloc(rat_QSget_colcount(prob) * mat->nrows * sizeof(int));
  rat_t *values =
      safe_malloc(rat_QSget_colcount(prob) * mat->nrows * sizeof(rat_t));

  int row_idx = 0, col_idxs_idx = 0, values_idx = 0;

  for (uint32_t r = 0; r < mat->nrows; r++) {
    // if (matrix_row_count(mat, r) == 0) // Skip empty rows
    //   continue;

    // where the non-zero columns of the row are stored
    begin_row_idx[row_idx] = col_idxs_idx;
    qsx->sense[row_idx] = 'E';

    const row_t *const row = matrix_row(mat, r);
    int n_non_zero = 0;
    for (uint32_t i = 0; i < row->size; i++) {
      const thvar_t v = row->data[i].c_idx;
      if (v < 0) // Ignore 0 coefficients (i.e., empty columns)
        continue;
      if (v == const_idx) // Ignore constant coefficients (i.e., RHS)
      {
        rat_sub_q(qsx->rhs[row_idx], &row->data[i].coeff);
        assert(qsx->rhs[row_idx] || rat_get_den(qsx->rhs[row_idx]) > 0);
        continue;
      }
      n_non_zero++;
      col_idxs[col_idxs_idx++] = qsx->var_to_col[row->data[i].c_idx];
      rat_init(values[values_idx]);
      rat_set_q(values[values_idx++], &row->data[i].coeff);
      assert(!rat_is_zero(values[values_idx - 1]));
      assert(rat_is_gmp(values[values_idx - 1]) ||
             rat_get_den(values[values_idx - 1]) > 0);
    }

#if 1 && !defined(NDEBUG)
    row_names[r] = safe_malloc(64 * sizeof(char));
    sprintf(row_names[r], "r%d", r);
#endif

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[row_idx] = n_non_zero;
    row_idx++;
  }

#if 0 && !defined(NDEBUG)
  printf("Strict-mode LP has %d/%d rows and %d columns\n", row_idx, mat->nrows,
         rat_QSget_colcount(prob));
  printf("Added %d rows to the strict-mode LP\n", row_idx);
  printf("Added %d/%d non-zero values to the strict-mode LP\n", col_idxs_idx,
         rat_QSget_colcount(prob) * mat->nrows);
  print_int_vector(non_zero_per_row, row_idx, "Non-zero per row");
  print_int_vector(begin_row_idx, row_idx, "Begin row index");
  print_int_vector(col_idxs, col_idxs_idx, "Col indices");
  print_rat_vector(values, values_idx, "Values");
  print_rat_vector(qsx->rhs, row_idx, "RHS");
  print_char_vector(qsx->sense, row_idx, "Sense");
  print_rat_vector(qsx->range, row_idx, "Range");
#endif

  // Since they are all equality constraints,
  // we can use the simpler rat_QSadd_rows function
  rat_QSadd_rows(prob, row_idx, non_zero_per_row, begin_row_idx, col_idxs,
                 values, qsx->rhs, qsx->sense,
#if 1 && !defined(NDEBUG)
                 row_names
#else
                 NULL
#endif
  );

  // rat_QSadd_ranged_rows(prob, row_idx, non_zero_per_row, begin_row_idx,
  //                       col_idxs, values, qsx->rhs, qsx->sense, qsx->range,
  //                       NULL);

#if 1 && !defined(NDEBUG)
  // Free the row names
  for (int i = 0; i < qsx->n_rows; i++) {
    safe_free(row_names[i]);
  }
  safe_free(row_names);

  for (int i = 0; i < values_idx; i++) {
    assert(rat_is_gmp(values[i]) || rat_get_den(values[i]) > 0);
  }
#endif

  rat_array_clear(values, values_idx);
  safe_free(col_idxs);
  safe_free(values);
}
#else

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
  assert(qsx->n_cols > 0);
  rat_QSprob prob = qsx->prob;
  rat_t temp_lb, temp_ub;
  rat_init_pair(temp_lb, temp_ub);

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {
    if (!var_is_valid_column(solver, v)) {
      continue;
    }
    // Free variables. They come from the SMT input. Encode them as columns.
    rat_ptr lb = rat_get_bound(solver, v, LOWER_BOUND, temp_lb);
    rat_ptr ub = rat_get_bound(solver, v, UPPER_BOUND, temp_ub);

    // bound_type_rat_t lb, ub;
    // get_bound(solver, v, true, &lb);
    // get_bound(solver, v, false, &ub);

    qsx->col_to_var[rat_QSget_colcount(prob)] = v;
    qsx->var_to_col[v] = rat_QSget_colcount(prob);

#if 1 && !defined(NDEBUG)
    char buf[64];
    if (arith_var_is_int(&solver->vtbl, v)) {
      sprintf(buf, "i!%d", v);
    } else {
      sprintf(buf, "z!%d", v);
    }
    // sprintf(buf, "x%d", rat_QSget_colcount(prob));
#endif

    rat_QSnew_col(prob, *guess_dir(solver, v), lb, ub,
#if 1 && !defined(NDEBUG)
                  buf
#else
                  NULL
#endif
    );

    // If the variable is not free, it is an auxiliary variable.
    // We will encode those as rows later.
  }
  rat_clear_pair(temp_lb, temp_ub);
}

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
  assert(qsx->n_rows > 0);
  rat_QSprob prob = qsx->prob;
  int non_zero_per_row[qsx->n_rows];
  int begin_row_idx[qsx->n_rows];
#if 1 && !defined(NDEBUG)
  char **row_names = safe_malloc(sizeof(char *) * qsx->n_rows);
#endif

  row_data_t rd = {.col_idxs = safe_malloc(
                       sizeof(int) * rat_QSget_colcount(prob) * qsx->n_rows),
                   .values = safe_malloc(
                       sizeof(rat_t) * rat_QSget_colcount(prob) * qsx->n_rows),
                   .row_idx = 0,
                   .col_idxs_idx = 0,
                   .values_idx = 0};

  // Add rows to the LP problem
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < n_vars; v++) {
    const int r = rd.row_idx;
    // Skip structural variables and constants
    if (!var_is_valid_row(solver, v)) {
      continue;
    }

    // where the non-zero columns of the row are stored
    begin_row_idx[r] = rd.col_idxs_idx;

    // Sense is always initialized to 0
    // rat_set(qsx->range[r], rat_zeroLpNum);

    if (has_both_bounds(solver, v)) // Bounded
    {
      if (has_eq_bounds(solver, v)) {
        rat_get_bound(solver, v, LOWER_BOUND, qsx->rhs[r]);
        qsx->sense[r] = 'E';
      } else {
        rat_get_bound(solver, v, LOWER_BOUND, qsx->rhs[r]);
        rat_get_bound(solver, v, UPPER_BOUND, qsx->range[r]);
        rat_sub_self(qsx->range[r], qsx->rhs[r]);
        if (has_strict_lb(solver, v)) {
          // Need to offset the lower bound by epsilon
          rat_sub_si(qsx->range[r], epsilon_num, epsilon_den);
        }
        qsx->sense[r] = 'R';
      }
    } else if (has_lb(solver, v)) // Only lower bound
    {
      rat_get_bound(solver, v, LOWER_BOUND, qsx->rhs[r]);
      qsx->sense[r] = 'G';
    } else if (has_ub(solver, v)) // Only upper bound
    {
      rat_get_bound(solver, v, UPPER_BOUND, qsx->rhs[r]);
      qsx->sense[r] = 'L';
    } else // Unbounded row, which should be filtered out
    {
      assert(false);
    }

    const int num_non_zeros = polynomial_to_row(solver, qsx, v, &rd);

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[r] = num_non_zeros;

#if 1 && !defined(NDEBUG)
    row_names[r] = safe_malloc(64 * sizeof(char));
    if (arith_var_is_int(&solver->vtbl, v)) {
      sprintf(row_names[r], "i!%d", v);
    } else {
      sprintf(row_names[r], "z!%d", v);
    }
    // sprintf(row_names[r], "C%d_1", r);
#endif

    // Add the new row to the map
    qsx->row_to_var[r] = v;
    qsx->var_to_row[v] = r;
    rd.row_idx++;
  }

  rat_QSadd_ranged_rows(prob, rd.row_idx, non_zero_per_row, begin_row_idx,
                        rd.col_idxs, rd.values, qsx->rhs, qsx->sense,
                        qsx->range,
#if 1 && !defined(NDEBUG)
                        row_names
#else
                        NULL
#endif
  );

#if 1 && !defined(NDEBUG)
  // Free the row names
  for (int i = 0; i < qsx->n_rows; i++) {
    safe_free(row_names[i]);
  }
  safe_free(row_names);
#endif

  rat_array_clear(rd.values, rd.values_idx);
  safe_free(rd.col_idxs);
  safe_free(rd.values);
}
#endif

/**
 * Builds the LP encoding for the epsilon-mode simplex problem.
 * @note `add_cols_epsilon` must be called before `add_rows_epsilon`, since
 * the latter depends on the column indices being populated first.
 * @param solver The simplex solver whose structural variables and constraints
 * define the LP.
 * @param qsx The QSopt_ex wrapper to populate with columns and rows.
 */
static void qsx_build_problem_epsilon(simplex_solver_t *const solver,
                                      qsx_t *const qsx) {
  add_cols_epsilon(solver, qsx);
  add_rows_epsilon(solver, qsx);
  assert(qsx->n_cols == rat_QSget_colcount(qsx->prob));
  assert(qsx->n_rows == rat_QSget_rowcount(qsx->prob));
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
  const rat_QSprob *prob = &qsx->prob;

  for (int col_idx = 0; col_idx < rat_QSget_colcount(*prob); col_idx++) {
    extract_col_value(solver, qsx, sol, col_idx);
  }
#if !(USE_MATRIX)
  for (int row_idx = 0; row_idx < rat_QSget_rowcount(*prob); row_idx++) {
    extract_row_value(solver, qsx, sol, row_idx);
  }
#endif
}

#pragma endregion

#pragma region Strict mode

#if USE_MATRIX
static void add_cols_strict(simplex_solver_t *const solver,
                            const qsx_t *const qsx) {
  assert(qsx->n_cols > 0);
  rat_QSprob prob = qsx->prob;
  rat_t temp_lb, temp_ub;
  rat_init_pair(temp_lb, temp_ub);

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 1; v < num_vars; v++) {
    rat_ptr lb = rat_get_bound(solver, v, LOWER_BOUND, temp_lb);
    rat_ptr ub = rat_get_bound(solver, v, UPPER_BOUND, temp_ub);

#if 1 && !defined(NDEBUG)
    char buf[64];
    if (arith_var_is_int(&solver->vtbl, v)) {
      sprintf(buf, "i!%d", v);
    } else {
      sprintf(buf, "z!%d", v);
    }
    // sprintf(buf, "x%d", rat_QSget_colcount(prob));
#endif

    const int n_cols = rat_QSget_colcount(prob);
    qsx->col_to_var[n_cols] = v;
    qsx->var_to_col[v] = n_cols;
    rat_QSnew_col(prob, rat_zeroLpNum,
                  !has_strict_lb(solver, v) ? lb : rat_NINFTY,
                  !has_strict_ub(solver, v) ? ub : rat_INFTY,
#if 1 && !defined(NDEBUG)
                  buf
#else
                  NULL
#endif
    );

    // If the variable is not free, it is an auxiliary variable.
    // We will encode those as rows later.
  }

  // At the end, add the strict variable column,
  // which is used to encode the strict bounds
  rat_QSnew_col(prob, rat_negoneLpNum, rat_zeroLpNum, rat_oneLpNum, NULL);
  rat_clear_pair(temp_lb, temp_ub);
}

static void add_rows_strict(simplex_solver_t *const solver,
                            const qsx_t *const qsx) {
  assert(qsx->n_cols > 0);

  assert(qsx->n_rows > 0);
  rat_QSprob prob = qsx->prob;
  matrix_t *const mat = &solver->matrix;
  int non_zero_per_row[qsx->n_rows];
  int begin_row_idx[qsx->n_rows];
  const int strict_var_idx = qsx->n_cols;
  int *const col_idxs = safe_malloc(sizeof(int) * qsx->n_cols * qsx->n_rows);
  rat_t *const values = safe_malloc(sizeof(rat_t) * qsx->n_cols * qsx->n_rows);
  int col_idxs_idx = 0;
  int values_idx = 0;
  int row_idx = 0;

  // Add rows to the LP problem
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 1; v < n_vars; v++) {
    if (!has_strict_lb(solver, v) && !has_strict_ub(solver, v)) {
      continue;
    }
    assert(has_any_bound(solver, v));
    // Add a strict constraint for each strict bound around a free variable
    assert(has_strict_lb(solver, v) || has_strict_ub(solver, v));
    if (has_strict_lb(solver, v)) {
      assert(has_lb(solver, v));
      non_zero_per_row[row_idx] = 2;
      begin_row_idx[row_idx] = col_idxs_idx;
      col_idxs[col_idxs_idx++] = qsx->var_to_col[v];
      col_idxs[col_idxs_idx++] = qsx->n_cols;
      // Add 1 coeff to the variable and -1 to the strict variable
      rat_init(values[values_idx]);
      rat_set(values[values_idx++], rat_oneLpNum);
      rat_init(values[values_idx]);
      rat_set(values[values_idx++], rat_negoneLpNum);
      // Set the sense 'Greater Than'
      qsx->sense[row_idx] = 'G';
      // Set the right-hand side to the lower bound of the variable
      rat_set_q(qsx->rhs[row_idx], &get_lb(solver, v)->main);
      // No need for range
      rat_set(qsx->range[row_idx], rat_zeroLpNum);
      // Update the mapping and increment the row index
      qsx->row_to_var[row_idx] = v;
      qsx->var_to_row[v] = row_idx;
      row_idx++;
    }
    if (has_strict_ub(solver, v)) {
      assert(has_ub(solver, v));
      non_zero_per_row[row_idx] = 2;
      begin_row_idx[row_idx] = col_idxs_idx;
      col_idxs[col_idxs_idx++] = qsx->var_to_col[v];
      col_idxs[col_idxs_idx++] = strict_var_idx;
      // Add 1 coeff to the variable and 1 to the strict variable
      rat_init(values[values_idx]);
      rat_set(values[values_idx++], rat_oneLpNum);
      rat_init(values[values_idx]);
      rat_set(values[values_idx++], rat_oneLpNum);
      // Set the sense 'Greater Than'
      qsx->sense[row_idx] = 'L';
      // Set the right-hand side to the lower bound of the variable
      rat_set_q(qsx->rhs[row_idx], &get_ub(solver, v)->main);
      // No need for range
      rat_set(qsx->range[row_idx], rat_zeroLpNum);
      // Update the mapping and increment the row index
      qsx->row_to_var[row_idx] = v;
      qsx->var_to_row[v] = row_idx;
      row_idx++;
    }
  }

  for (uint32_t r = 0; r < mat->nrows; r++) {
    // if (matrix_row_count(mat, r) == 0) // Skip empty rows
    //   continue;

    // where the non-zero columns of the row are stored
    begin_row_idx[row_idx] = col_idxs_idx;
    qsx->sense[row_idx] = 'E';

    int n_non_zero = 0;
    const row_t *const row = matrix_row(mat, r);
    for (uint32_t i = 0; i < row->size; i++) {
      const thvar_t v = row->data[i].c_idx;
      if (v < 0) // Ignore 0 coefficients (i.e., empty columns)
        continue;
      if (v == const_idx) // Ignore constant coefficients (i.e., RHS)
      {
        rat_sub_q(qsx->rhs[row_idx], &row->data[i].coeff);
        assert(qsx->rhs[row_idx] || rat_get_den(qsx->rhs[row_idx]) > 0);
        continue;
      }
      n_non_zero++;
      col_idxs[col_idxs_idx++] = qsx->var_to_col[v];
      rat_init(values[values_idx]);
      rat_set_q(values[values_idx++], &row->data[i].coeff);
      assert(!rat_is_zero(values[values_idx - 1]));
      assert(rat_is_gmp(values[values_idx - 1]) ||
             rat_get_den(values[values_idx - 1]) > 0);
    }

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[row_idx] = n_non_zero;
    row_idx++;
  }

#if 0 && !defined(NDEBUG)
  printf("Strict-mode LP has %d rows and %d columns\n", qsx->n_rows,
         qsx->n_cols);
  printf("Added %d rows to the strict-mode LP\n", row_idx);
  print_int_vector(non_zero_per_row, row_idx, "Non-zero per row");
  print_int_vector(begin_row_idx, row_idx, "Begin row index");
  print_int_vector(col_idxs, col_idxs_idx, "Col indices");
  print_rat_vector(values, values_idx, "Values");
  print_rat_vector(qsx->rhs, row_idx, "RHS");
  print_char_vector(qsx->sense, row_idx, "Sense");
  print_rat_vector(qsx->range, row_idx, "Range");
#endif

  rat_QSadd_ranged_rows(prob, row_idx, non_zero_per_row, begin_row_idx,
                        col_idxs, values, qsx->rhs, qsx->sense, qsx->range,
                        NULL);

  assert(row_idx == qsx->n_rows && row_idx == rat_QSget_rowcount(prob));
  rat_array_clear(values, values_idx);
  safe_free(col_idxs);
  safe_free(values);
}

#else

/**
 * Reserved placeholder for strict-mode column construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the variable definitions.
 * @param qsx The QSopt_ex wrapper that would receive the strict-mode columns.
 */
static void add_cols_strict(simplex_solver_t *const solver, qsx_t *const qsx) {
  assert(qsx->n_cols > 0);
  rat_QSprob prob = qsx->prob;
  rat_t temp_lb, temp_ub;
  rat_init_pair(temp_lb, temp_ub);

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {
    // Free variables. They come from the SMT input. Encode them as columns.
    if (var_is_valid_column(solver, v)) {
      rat_ptr lb = rat_get_bound(solver, v, LOWER_BOUND, temp_lb);
      rat_ptr ub = rat_get_bound(solver, v, UPPER_BOUND, temp_ub);

      qsx->col_to_var[rat_QSget_colcount(prob)] = v;
      qsx->var_to_col[v] = rat_QSget_colcount(prob);
      rat_QSnew_col(prob, rat_zeroLpNum,
                    !has_strict_lb(solver, v) ? lb : rat_NINFTY,
                    !has_strict_ub(solver, v) ? ub : rat_INFTY, NULL);
    }

    // If the variable is not free, it is an auxiliary variable.
    // We will encode those as rows later.
  }

  // At the end, add the strict variable column,
  // which is used to encode the strict bounds
  rat_QSnew_col(prob, rat_negoneLpNum, rat_zeroLpNum, rat_oneLpNum, NULL);
  rat_clear_pair(temp_lb, temp_ub);
}

/**
 * Reserved placeholder for strict-mode row construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the row definitions.
 * @param qsx The QSopt_ex wrapper that would receive the strict-mode rows.
 */
static void add_rows_strict(simplex_solver_t *const solver, qsx_t *const qsx) {
  assert(qsx->n_rows > 0);
  rat_QSprob prob = qsx->prob;
  int non_zero_per_row[qsx->n_rows];
  int begin_row_idx[qsx->n_rows];
  const int strict_var_idx = qsx->n_cols; // TODO: n_cols or QSget_n_cols ?

  row_data_t rd = {.col_idxs = safe_malloc(
                       sizeof(int) * rat_QSget_colcount(prob) * qsx->n_rows),
                   .values = safe_malloc(
                       sizeof(rat_t) * rat_QSget_colcount(prob) * qsx->n_rows),
                   .row_idx = 0,
                   .col_idxs_idx = 0,
                   .values_idx = 0};

  // Add rows to the LP problem
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < n_vars; v++) {
    // Skip structural variables and constants
    if (!var_is_valid_row(solver, v) &&
        !var_is_valid_strict_column(solver, v)) {
      continue;
    }
    assert(has_any_bound(solver, v));

    // Add a strict constraint for each strict bound around a free variable
    if (var_is_valid_strict_column(solver, v)) {
      assert(has_strict_lb(solver, v) || has_strict_ub(solver, v));
      if (has_strict_lb(solver, v)) {
        assert(has_lb(solver, v));
        non_zero_per_row[rd.row_idx] = 2;
        begin_row_idx[rd.row_idx] = rd.col_idxs_idx;
        rd.col_idxs[rd.col_idxs_idx++] = qsx->var_to_col[v];
        rd.col_idxs[rd.col_idxs_idx++] =
            qsx->n_cols; // TODO: n_cols or QSget_n_cols ?
        // Add 1 coeff to the variable and -1 to the strict variable
        rat_init(rd.values[rd.values_idx]);
        rat_set(rd.values[rd.values_idx++], rat_oneLpNum);
        rat_init(rd.values[rd.values_idx]);
        rat_set(rd.values[rd.values_idx++], rat_negoneLpNum);
        // Set the sense 'Greater Than'
        qsx->sense[rd.row_idx] = 'G';
        // Set the right-hand side to the lower bound of the variable
        rat_set_q(qsx->rhs[rd.row_idx], &get_lb(solver, v)->main);
        // No need for range
        rat_set(qsx->range[rd.row_idx], rat_zeroLpNum);
        // Update the mapping and increment the row index
        qsx->row_to_var[rd.row_idx] = v;
        qsx->var_to_row[v] = rd.row_idx;
        rd.row_idx++;
      }
      if (has_strict_ub(solver, v)) {
        assert(has_ub(solver, v));
        non_zero_per_row[rd.row_idx] = 2;
        begin_row_idx[rd.row_idx] = rd.col_idxs_idx;
        rd.col_idxs[rd.col_idxs_idx++] = qsx->var_to_col[v];
        rd.col_idxs[rd.col_idxs_idx++] = strict_var_idx;
        // Add 1 coeff to the variable and 1 to the strict variable
        rat_init(rd.values[rd.values_idx]);
        rat_set(rd.values[rd.values_idx++], rat_oneLpNum);
        rat_init(rd.values[rd.values_idx]);
        rat_set(rd.values[rd.values_idx++], rat_oneLpNum);
        // Set the sense 'Greater Than'
        qsx->sense[rd.row_idx] = 'L';
        // Set the right-hand side to the lower bound of the variable
        rat_set_q(qsx->rhs[rd.row_idx], &get_ub(solver, v)->main);
        // No need for range
        rat_set(qsx->range[rd.row_idx], rat_zeroLpNum);
        // Update the mapping and increment the row index
        qsx->row_to_var[rd.row_idx] = v;
        qsx->var_to_row[v] = rd.row_idx;
        rd.row_idx++;
      }
      continue;
    }

    // where the non-zero columns of the row are stored
    begin_row_idx[rd.row_idx] = rd.col_idxs_idx;

    // All rat_t numbers are initialized to 0
    // rat_set(qsx->rhs[rd.row_idx], rat_zeroLpNum);
    // rat_set(qsx->range[rd.row_idx], rat_zeroLpNum);

    // Add row range
    const int num_non_zeros = polynomial_to_row(solver, qsx, v, &rd);

    // For each row, we set the number of non-zero coefficients
    // (i.e., the size of the row)
    non_zero_per_row[rd.row_idx] = num_non_zeros;

    // There is at least a strict bound, they need to be handled by including
    // the strict variable in the row
    if (has_strict_lb(solver, v) || has_strict_ub(solver, v)) {
      const bool is_lb_strict = has_strict_lb(solver, v);

      if (has_lb(solver, v)) {
        if (is_lb_strict) {
          non_zero_per_row[rd.row_idx]++;
          rd.col_idxs[rd.col_idxs_idx++] = strict_var_idx;
          rat_init(rd.values[rd.values_idx]);
          rat_set(rd.values[rd.values_idx++], rat_negoneLpNum);
        }
        rat_add_q(qsx->rhs[rd.row_idx], get_lb_main(solver, v));
        qsx->sense[rd.row_idx] = 'G';
        // Add the new row to the map
        qsx->row_to_var[rd.row_idx] = v;
        qsx->var_to_row[v] = rd.row_idx;
        rd.row_idx++;
      }

      // Case II: we are dealing with a row with at least one bound. If both
      // bounds are set, we add the row twice, once for the lower bound and once
      // for the upper bound.
      if (has_lb(solver, v) && has_ub(solver, v)) {
        // Insert all cols (except strict col, if present)
        begin_row_idx[rd.row_idx] = rd.col_idxs_idx;
        // Go back and add the same values we already added for the lower-bound
        const int prev_row_non_zeros = non_zero_per_row[rd.row_idx - 1];
        const int max_idx_offset = rd.col_idxs_idx - (is_lb_strict ? 1 : 0);
        for (int i = rd.col_idxs_idx - prev_row_non_zeros; i < max_idx_offset;
             i++) {
          rd.col_idxs[rd.col_idxs_idx++] = rd.col_idxs[i];
          rat_init(rd.values[rd.values_idx]);
          rat_set(rd.values[rd.values_idx++], rd.values[i]);
        }
        non_zero_per_row[rd.row_idx] =
            prev_row_non_zeros - (is_lb_strict ? 1 : 0);
      }

      if (has_ub(solver, v)) {
        if (has_strict_ub(solver, v)) {
          non_zero_per_row[rd.row_idx]++;
          rd.col_idxs[rd.col_idxs_idx++] = strict_var_idx;
          rat_init(rd.values[rd.values_idx]);
          rat_set(rd.values[rd.values_idx++], rat_oneLpNum);
        }
        rat_add_q(qsx->rhs[rd.row_idx], get_ub_main(solver, v));
        qsx->sense[rd.row_idx] = 'L';
        // Add the new row to the map
        qsx->row_to_var[rd.row_idx] = v;
        qsx->var_to_row[v] = rd.row_idx;
        rd.row_idx++;
      }

      continue;
    }

    assert(!has_strict_lb(solver, v) && !has_strict_ub(solver, v));
    if (has_both_bounds(solver, v)) // Bounded
    {
      if (has_eq_bounds(solver, v)) {
        rat_add_q(qsx->rhs[rd.row_idx], get_lb_main(solver, v));
        qsx->sense[rd.row_idx] = 'E';
      } else {
        // First, we need to ensure that range too is affected by the constant
        // offest from the polynomial
        rat_set(qsx->range[rd.row_idx], qsx->rhs[rd.row_idx]);
        rat_add_q(qsx->rhs[rd.row_idx], get_lb_main(solver, v));
        rat_add_q(qsx->range[rd.row_idx], get_ub_main(solver, v));
        rat_sub_self(qsx->range[rd.row_idx], qsx->rhs[rd.row_idx]);
        qsx->sense[rd.row_idx] = 'R';
      }
      // printf("Adding bounded row %d with lower bound %s and upper bound
      // %s\n", row_idx, rat_get_str(NULL, 10, d_rhs[row_idx]),
      // rat_get_str(NULL, 10, d_range[row_idx]));
    } else if (has_lb(solver, v)) // Only lower bound
    {
      // printf("Adding lower bounded row %d with lower bound %s\n", row_idx,
      // rat_get_str(NULL, 10, lb.val));
      rat_add_q(qsx->rhs[rd.row_idx], get_lb_main(solver, v));
      qsx->sense[rd.row_idx] = 'G';
    } else if (has_ub(solver, v)) // Only upper bound
    {
      // printf("Adding upper bounded row %d with upper bound %s\n",
      // row_data.row_idx,
      //        rat_get_str(NULL, 10, ub.val));
      rat_add_q(qsx->rhs[rd.row_idx], get_ub_main(solver, v));
      qsx->sense[rd.row_idx] = 'L';
    } else // Unbounded row, handled above
    {
      assert(false);
    }

    // Add the new row to the map
    qsx->row_to_var[rd.row_idx] = v;
    qsx->var_to_row[v] = rd.row_idx;
    rd.row_idx++;
  }

#if 1 && !defined(NDEBUG)
  printf("Strict-mode LP has %d rows and %d columns\n", qsx->n_rows,
         qsx->n_cols);
  printf("Added %d rows to the strict-mode LP\n", rd.row_idx);
  print_int_vector(non_zero_per_row, rd.row_idx, "Non-zero per row");
  print_int_vector(begin_row_idx, rd.row_idx, "Begin row index");
  print_int_vector(rd.col_idxs, rd.col_idxs_idx, "Col indices");
  print_rat_vector(rd.values, rd.values_idx, "Values");
  print_rat_vector(qsx->rhs, rd.row_idx, "RHS");
  print_char_vector(qsx->sense, rd.row_idx, "Sense");
  print_rat_vector(qsx->range, rd.row_idx, "Range");
#endif

  rat_QSadd_ranged_rows(prob, rd.row_idx, non_zero_per_row, begin_row_idx,
                        rd.col_idxs, rd.values, qsx->rhs, qsx->sense,
                        qsx->range, NULL);

  assert(rd.row_idx == qsx->n_rows && rd.row_idx == rat_QSget_rowcount(prob));
  rat_array_clear(rd.values, rd.values_idx);
  safe_free(rd.col_idxs);
  safe_free(rd.values);
}
#endif

/**
 * Builds the strict-mode LP representation used when strict mode is enabled.
 * @param solver The simplex solver whose constraints define the problem.
 * @param qsx The QSopt_ex wrapper to populate.
 */
static void qsx_build_problem_strict(simplex_solver_t *const solver,
                                     qsx_t *const qsx) {
  add_cols_strict(solver, qsx);
  add_rows_strict(solver, qsx);
  assert(qsx->n_cols == rat_QSget_colcount(qsx->prob) - 1);
  assert(qsx->n_rows == rat_QSget_rowcount(qsx->prob));
}

/**
 * Extracts every value from a strict-mode LP solution into the external result.
 * @param solver The simplex solver defining the model.
 * @param qsx The solved QSopt_ex problem.
 * @param sol The output solution to fill.
 */
static void extract_solution_strict(simplex_solver_t *solver, qsx_t *qsx,
                                    external_solution_t *sol) {
  const int strict_var_idx = qsx->n_cols;
  bool is_strict_basic = qsx->basis.cstat[strict_var_idx] == QS_COL_BSTAT_BASIC;

  // TODO: we may skip ensuring that the strict variable is 0 entirely
#if 1
  if (is_strict_basic && rat_is_pos(qsx->x[strict_var_idx])) {
    [[maybe_unused]] int res =
        rat_QSchange_bound(qsx->prob, strict_var_idx, 'U', rat_zeroLpNum);
    assert(res == 0);

    rat_t delta, obj_lb, obj_ub;
    rat_init(delta);
    rat_init_pair(obj_lb, obj_ub);
    rat_set_double(delta, __smt2_globals.delta);

    res = QSdelta_full_solver_rat(qsx->prob, delta, qsx->x, qsx->y, obj_lb,
                                  obj_ub, &qsx->basis, PRIMAL_SIMPLEX,
                                  &qsx->status, NULL, NULL, NULL);
    assert(res == 0);
    rat_clear(delta);
    rat_clear_pair(obj_lb, obj_ub);

    const external_simplex_status_t status = qsx_status_to_sol_status(qsx);
    if (status != EXTERNAL_SIMPLEX_FEASIBLE &&
        status != EXTERNAL_SIMPLEX_INFEASIBLE) {
      // An error occurred, so we don't have a solution
      sol->status = status;
      return;
    }

    is_strict_basic = qsx->basis.cstat[strict_var_idx] == QS_COL_BSTAT_BASIC;
  }

  assert(qsx->status == QS_LP_OPTIMAL || qsx->status == QS_LP_DELTA_OPTIMAL ||
         qsx->status == QS_LP_FEASIBLE || qsx->status == QS_LP_DELTA_FEASIBLE ||
         qsx->status == QS_LP_UNBOUNDED || qsx->status == QS_LP_INFEASIBLE);

  // By this point, if we have a feasible solution,
  // the strict variable is either basic and at 0,
  // or it is non-basic and we don't care about its value.
  // If there is no feasible solution, all bets are off.
  assert(sol->status != EXTERNAL_SIMPLEX_FEASIBLE || !is_strict_basic ||
         rat_is_zero(qsx->x[strict_var_idx]));
#endif

  for (int col_idx = 0; col_idx < qsx->n_cols; col_idx++) {
    extract_col_value(solver, qsx, sol, col_idx);
  }
  for (int row_idx = 0; row_idx < qsx->n_rows; row_idx++) {
    // We already encountered the nonbasic version of this row, we can skip it
    if (int_bvset_member(&sol->nb_vars, qsx->row_to_var[row_idx]))
      continue;
#if USE_MATRIX
    if (qsx->row_to_var[row_idx] == null_idx)
      continue;
#endif
    extract_row_value(solver, qsx, sol, row_idx);
  }

  // Since we have to split range rows, we have to remove those that we
  // erroneously marked as basic and then discovered to be nonbasic
  for (thvar_t v = 0; v < (int32_t)solver->vtbl.nvars; v++) {
    if (int_bvset_member(&sol->nb_vars, v)) {
      int_bvset_remove(&sol->b_vars, v);
    }
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
  const rat_QSprob *const prob = &qsx->prob;

  unsigned int precision = 0;
  rat_t delta;
  rat_init(delta);
  rat_set_double(delta, __smt2_globals.delta);

  if (__smt2_globals.epsilon_mode) {
    [[maybe_unused]] const int res = QSdelta_solver_rat(
        *prob, delta, qsx->x, qsx->y, &qsx->basis, &precision, PRIMAL_SIMPLEX,
        &qsx->status, NULL, NULL);
    assert(res == 0);
  } else {
    rat_t obj_lb, obj_ub;
    rat_init_pair(obj_lb, obj_ub);
    [[maybe_unused]] const int res = QSdelta_full_solver_rat(
        qsx->prob, delta, qsx->x, qsx->y, obj_lb, obj_ub, &qsx->basis,
        PRIMAL_SIMPLEX, &qsx->status, NULL, NULL, NULL);
    assert(res == 0);
    rat_clear_pair(obj_lb, obj_ub);
  }

  // Update the statistics
  if (precision > solver->stats.max_precision)
    solver->stats.max_precision = precision;
  if (should_update_max_delta(qsx)) {
    const double new_delta = rat_to_d(delta);
    if (new_delta > solver->stats.max_delta)
      solver->stats.max_delta = new_delta;
  }

  solution->nvars = solver->vtbl.nvars;
  solution->status = qsx_status_to_sol_status(qsx);
  rat_clear(delta);
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
  const double start_setup = get_cpu_time();

  qsx_t qsx;
  qsx_init(&qsx);
  qsx_init_vars(solver, &qsx);

  // Edge case: empty problem, feasible by definition
  if (qsx.n_cols == 0 || qsx.n_rows == 0) {
    sol->status = EXTERNAL_SIMPLEX_FEASIBLE;
    qsx_clear(&qsx);
    return;
  }

  if (__smt2_globals.epsilon_mode)
    qsx_build_problem_epsilon(solver, &qsx);
  else
    qsx_build_problem_strict(solver, &qsx);
#if 1 && !defined(NDEBUG)
  static int i = 0;
  // rat_QSdump_prob(qsx.prob);
  fprintf(stderr, "Problem %d %s: n_cols = %d, n_rows = %d\n", i,
          __smt2_globals.epsilon_mode ? "epsilon" : "strict", qsx.n_cols,
          qsx.n_rows);
  char filename[256];
  snprintf(filename, sizeof(filename),
           "/home/campus.ncl.ac.uk/c3054737/Programming/phd/yices2/"
           "qsproblem_%d_%s.lp",
           i, __smt2_globals.epsilon_mode ? "epsilon" : "strict");
  rat_QSwrite_prob(qsx.prob, filename, "LP");
  i++;
#endif
  const double start_solve = get_cpu_time();

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

  const double end_solve = get_cpu_time();
  solver->stats.external_lp_setup_time += time_diff(start_solve, start_setup);
  solver->stats.external_lp_run_time += time_diff(end_solve, start_setup);
}
