/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */
#include "external_simplex.h"

#include "../egraph/egraph_base_types.h"
#include "frontend/smt2/smt2_commands.h"
#include "matrices.h"
#include "simplex.h"
#include "simplex_printer.h"
#include "simplex_types.h"
#include "solvers/simplex/external_qsoptex.h"
#include "terms/rationals.h"

#include <inttypes.h>

#include "io/tracer.h"
#include "solvers/egraph/theory_explanations.h"
#include "solvers/simplex/integrality_constraints.h"
#include "solvers/simplex/simplex.h"
#include "terms/mpq_stores.h"
#include "terms/rational_hash_maps.h"
#include "utils/assert_utils.h"
#include "utils/bitvectors.h"
#include "utils/dep_tables.h"
#include "utils/dprng.h"
#include "utils/hash_functions.h"
#include "utils/int_hash_classes.h"

#include <assert.h>
#include <qsopt_ex/QSopt_ex.h>

static mpq_t epsilon;
static bool qsx_started = false;

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

static void external_solution_init(external_solution_t *sol,
                                   const uint32_t nvars) {
  sol->status = EXTERNAL_SIMPLEX_ERROR;
  sol->nvars = nvars;
  sol->x = (xrational_t *)safe_malloc(nvars * sizeof(xrational_t));
  sol->basic_vars = (thvar_t *)safe_malloc(nvars * sizeof(thvar_t));
  sol->nb_vars = 0;
  for (uint32_t i = 0; i < nvars; i++) {
    xq_init(sol->x + i);
  }
}

static external_solution_t new_external_solution(const uint32_t nvars) {
  external_solution_t sol;
  external_solution_init(&sol, nvars);
  return sol;
}

static void external_solution_clear(external_solution_t *sol) {
  for (uint32_t i = 0; i < sol->nvars; i++) {
    xq_clear(sol->x + i);
  }
  sol->nvars = 0;
  sol->nb_vars = 0;
  free(sol->basic_vars);
  free(sol->x);
  sol->basic_vars = NULL;
  sol->x = NULL;
}

static void inplace_convert_to_gmp(rational_t *const r, mpq_t *const loc) {
  assert(loc);
  assert(!is_ratgmp(r));

  mpq_init(*loc);
  mpq_set_int32(*loc, get_num(r), get_den(r));
  set_ratgmp(r, *loc);
}

static void convert_to_gmp(const rational_t *const r, mpq_t val) {
  if (is_ratgmp(r)) {
    mpq_set(val, get_gmp(r));
  } else {
    mpq_set_int32(val, get_num(r), get_den(r));
  }
}

static void init_and_convert_to_gmp(const rational_t *const r,
                                    mpq_t uninitialized_val) {
  mpq_init(uninitialized_val);
  convert_to_gmp(r, uninitialized_val);
}

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

mpq_ptr get_bound(bound_type_t bound, mpq_ptr ninf, mpq_ptr inf,
                  bool *used_temp, mpq_t *temp) {
  assert(!*used_temp);
  // Infinity bound
  if (!bound.is_finite) {
    return bound.is_lb ? ninf : inf;
  }

  // Finite bound
  if (is_rat32(&bound.val)) { // Need to convert to GMP
    *used_temp = true;
    inplace_convert_to_gmp(&bound.val, temp);
  } else if (bound.is_strict) { // Need to use temp to adjust value with epsilon
    *used_temp = true;
    mpq_init(*temp);
    mpq_set(*temp, get_gmp(&bound.val));
    set_ratgmp(&bound.val, *temp);
  }
  if (bound.is_strict) { // Adjust the bounds with epsilon
    if (bound.is_lb) {
      mpq_add(get_gmp(&bound.val), get_gmp(&bound.val), epsilon);
    } else {
      mpq_sub(get_gmp(&bound.val), get_gmp(&bound.val), epsilon);
    }
  }
  return get_gmp(&bound.val);
}

static bool has_lb(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  return lb_idx > -1;
}

static bool has_ub(const simplex_solver_t *const solver, const thvar_t v) {
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  return ub_idx > -1;
}

static bool has_any_bound(const simplex_solver_t *const solver,
                          const thvar_t v) {
  return has_lb(solver, v) || has_ub(solver, v);
}

static bool has_strict_lb(const simplex_solver_t *const solver,
                          const thvar_t v) {
  const int32_t lb_idx = solver->vtbl.lower_index[v];
  return lb_idx > -1 && !xq_is_rational(&solver->bstack.bound[lb_idx]);
}

static bool has_strict_ub(const simplex_solver_t *const solver,
                          const thvar_t v) {
  const int32_t ub_idx = solver->vtbl.upper_index[v];
  return ub_idx > -1 && !xq_is_rational(&solver->bstack.bound[ub_idx]);
}

static bool is_below_lb(simplex_solver_t *const solver, const thvar_t x,
                        xrational_t *const value) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 && xq_gt(solver->bstack.bound + k, value);
}

static bool is_above_ub(simplex_solver_t *const solver, const thvar_t x,
                        xrational_t *const value) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 && xq_lt(solver->bstack.bound + k, value);
}

static xrational_t *get_lb(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_lower_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

static xrational_t *get_ub(simplex_solver_t *const solver, const thvar_t x) {
  const int32_t k = arith_var_upper_index(&solver->vtbl, x);
  return k >= 0 ? solver->bstack.bound + k : NULL;
}

/**
 * Loop over all the theory variables in the solver and add them as columns to
 * the LP problem in QSopt_ex, having care of setting the appropriate lower and
 * upper bounds for each variable.
 * The bounds, if finite, are listed in the solver's bstack, and are converted
 * to mpq_t as needed.
 * @param solver the simplex solver containing the variables and their bounds
 * @param[out] qsx_prob the QSopt_ex LP problem to which the columns will be
 * added
 */
static void add_cols(simplex_solver_t *solver, mpq_QSprob qsx_prob) {
  static mpq_t tmp_lb, tmp_ub;
  matrix_t *matrix = &solver->matrix;
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

    mpq_ptr lb = get_bound(
        ((bound_type_t){.is_finite = has_lb,
                        .is_strict = __smt2_globals.delta < 0 && strict_lb,
                        .is_lb = true,
                        .val = has_lb ? bounds[lb_idx].main : (rational_t){0}}),
        &used_temp_lb, &tmp_lb);
    mpq_ptr ub = get_bound(
        ((bound_type_t){.is_finite = has_ub,
                        .is_strict = __smt2_globals.delta < 0 && strict_ub,
                        .is_lb = false,
                        .val = has_ub ? bounds[ub_idx].main : (rational_t){0}}),
        &used_tmp_ub, &tmp_ub);

    mpq_QSnew_col(qsx_prob, mpq_oneLpNum, lb, ub, NULL);

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

static void mpq_vector_clear(mpq_t v[], const int n) {
  for (int i = 0; i < n; i++) {
    mpq_clear(v[i]);
  }
}

void print_int_vector(const int32_t v[], const int n, const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    printf("%d", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void print_mpq_vector(const mpq_t v[], const int n, const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    gmp_printf("%Qd", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void print_rational_vector(const rational_t v[], const int n,
                           const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    q_print(stdout, &v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void print_xrational_vector(const xrational_t v[], const int n,
                            const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    xq_print(stdout, &v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void print_char_vector(const char v[], const int n, const char *name) {
  if (v == NULL) {
    printf("%s: NULL\n", name);
    return;
  }
  printf("%s: [", name);
  for (int i = 0; i < n; i++) {
    printf("%c", v[i]);
    if (i < n - 1) {
      printf(", ");
    }
  }
  printf("]\n");
}

void print_external_solution(const external_solution_t *sol) {
  printf("external_solution_t {\n");
  switch (sol->status) {
  case EXTERNAL_SIMPLEX_FEASIBLE:
    printf("  status: OPTIMAL\n");
    break;
  case EXTERNAL_SIMPLEX_UNBOUNDED:
    printf("  status: UNBOUNDED\n");
    break;
  case EXTERNAL_SIMPLEX_INFEASIBLE:
    printf("  status: INFEASIBLE\n");
    break;
  case EXTERNAL_SIMPLEX_EXHAUSTED:
    printf("  status: EXHAUSTED\n");
    break;
  default:
    printf("  status: UNKNOWN\n");
    break;
  }
  printf("  nvars: %d\n", sol->nvars);
  print_xrational_vector(sol->x, sol->nvars, "  x");
  printf("}\n");
  printf("basic vars: %d\n", sol->nb_vars);
  for (uint32_t i = 0; i < sol->nb_vars; i++) {
    printf("%d ", sol->basic_vars[i]);
  }
  printf("\n");
}

static bool is_strict_var_zero(mpq_t x[], const uint32_t n) {
  return __smt2_globals.delta < 0 && __smt2_globals.strict_mode &&
         mpq_cmp_ui(x[n - 1], 0, 1) == 0;
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

static mpq_ptr get_y(mpq_QSprob prob, const int rowIdx) {
  assert(prob && prob->lp && prob->lp->pIpiz);
  return prob->lp->pIpiz[rowIdx];
}

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

/**
 * Loop over all the rows in the solver and add them as rows to the LP problem
 * in QSopt_ex, having care of setting the appropriate right-hand side and range
 * for each row.
 * @param solver the simplex solver containing the rows
 * @param[out] qsx_prob the QSopt_ex LP problem to which the rows will be added
 */
static void add_rows(const simplex_solver_t *const solver,
                     mpq_QSprob qsx_prob) {
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
        convert_to_gmp(coeff, d_rhs[d_rhs_idx - 1]);
      } else {
        num_non_zeros++;
        col_idxs[col_idxs_idx++] = (int)x;
        init_and_convert_to_gmp(coeff, values[values_idx++]);
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

  mpq_QSadd_rows(qsx_prob, non_zero_per_row_idx, non_zero_per_row,
                 begin_row_idx, col_idxs, values, d_rhs, d_sense, NULL);

  mpq_vector_clear(values, values_idx);
  mpq_vector_clear(d_rhs, d_rhs_idx);
  mpq_vector_clear(d_range, d_range_idx);
}

external_solution_t solve_lp(simplex_solver_t *const solver,
                             mpq_QSprob qsx_prob) {
#ifndef NDEBUG
  mpq_QSwrite_prob(
      d_qsx, "/home/campus.ncl.ac.uk/c3054737/Programming/phd/cvc5/qsfile.lp",
      "LP");
#endif
  external_solution_t solution = new_external_solution(solver->vtbl.nvars);

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

  const int res = QSdelta_solver(qsx_prob, delta, x, NULL, &basis, &precision,
                                 PRIMAL_SIMPLEX, &status, NULL, NULL);
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
    set_ratgmp(&solution.x[i].main, x[i]);
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
    solution.nvars = solver->vtbl.nvars;
    solution.status = is_strict_var_zero(x, solver->vtbl.nvars)
                          ? EXTERNAL_SIMPLEX_INFEASIBLE
                          : EXTERNAL_SIMPLEX_FEASIBLE;
    break;
  case QS_LP_INFEASIBLE:
    solution.status = EXTERNAL_SIMPLEX_INFEASIBLE;
    break;
  case QS_LP_ITER_LIMIT:
  case QS_LP_TIME_LIMIT:
    solution.status = EXTERNAL_SIMPLEX_EXHAUSTED;
    break;
  default:
    printf("QSopt_ex returned an unexpected status: %d\n", status);
    solution.status = EXTERNAL_SIMPLEX_ERROR;
    break;
  }

  basis_clear(&basis);
  mpq_clear(delta);
  return solution;
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

bool simplex_check_feasibility_external(simplex_solver_t *solver) {
  if (!solver->tableau_ready)
    return true;

  printf("\n\n*** SIMPLEX START ***\n");
  // print_simplex_vars_summary(stdout, solver);
  printf("==== Pivots ====\n");
  printf("%d", solver->stats.num_pivots);
  printf("\n==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n");

  global_qsx_start();
  mpq_QSprob qsx_prob = mpq_QScreate_prob(NULL, QS_MIN);

  mpq_QSset_param(qsx_prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  mpq_QSset_param(qsx_prob, QS_PARAM_SIMPLEX_DISPLAY, __smt2_globals.verbosity);

  add_cols(solver, qsx_prob);
  add_rows(solver, qsx_prob);
  external_solution_t solution = solve_lp(solver, qsx_prob);
  printf("\n==== QSopt_ex solution ====\n");
  print_external_solution(&solution);

  // mpq_QSdump_prob(qsx_prob);

  printf("External solver: %d, Strict: %d, Delta: %.2f - \n\n",
         __smt2_globals.external_solver, __smt2_globals.strict_mode,
         __smt2_globals.delta);

  external_solution_clear(&solution);
  mpq_QSfree_prob(qsx_prob);
  global_qsx_clear();

  return true;
}
