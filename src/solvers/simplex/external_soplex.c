/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_soplex class.
 */
#include "external_soplex.h"

#ifndef HAVE_SOPLEX
#error "SoPlex library is not available. Please install it to use this feature."
#endif

#define SOPLEX_WITH_GMP
#define SOPLEX_WITH_BOOST

#include "frontend/smt2/smt2_commands.h"
#include "io/term_printer.h"
#include "solvers/simplex/external_simplex.h"
#include "solvers/simplex/simplex_types.h"
#include "utils/cputime.h"
#include "utils/memalloc.h"
#include <soplex_interface.h>
#include <stdbool.h>

///@name Parameters
///@{
#pragma region Parameters
/// boolean parameters
typedef enum {
  /// should lifting be used to reduce range of nonzero matrix coefficients?
  LIFTING = 0,

  /// should LP be transformed to equality form before a rational solve?
  EQTRANS = 1,

  /// should dual infeasibility be tested in order to try to return a dual
  /// solution even if primal infeasible?
  TESTDUALINF = 2,

  /// should a rational factorization be performed after iterative refinement?
  RATFAC = 3,

  /// should cycling solutions be accepted during iterative refinement?
  ACCEPTCYCLING = 4,

  /// apply rational reconstruction after each iterative refinement?
  RATREC = 5,

  /// round scaling factors for iterative refinement to powers of two?
  POWERSCALING = 6,

  /// continue iterative refinement with exact basic solution if not optimal?
  RATFACJUMP = 7,

  /// use bound flipping also for row representation?
  ROWBOUNDFLIPS = 8,

  /// use persistent scaling?
  PERSISTENTSCALING = 9,

  /// perturb the entire problem or only the relevant bounds of s single pivot?
  FULLPERTURBATION = 10,

  /// re-optimize the original problem to get a proof (ray) of
  /// infeasibility/unboundedness?
  ENSURERAY = 11,

  /// try to enforce that the optimal solution is a basic solution
  FORCEBASIC = 12,

  // enable presolver SingletonCols in PaPILO?
  SIMPLIFIER_SINGLETONCOLS = 13,

  // enable presolver ConstraintPropagation in PaPILO?
  SIMPLIFIER_CONSTRAINTPROPAGATION = 14,

  // enable presolver ParallelRowDetection in PaPILO?
  SIMPLIFIER_PARALLELROWDETECTION = 15,

  // enable presolver ParallelColDetection in PaPILO?
  SIMPLIFIER_PARALLELCOLDETECTION = 16,

  // enable presolver SingletonStuffing in PaPILO?
  SIMPLIFIER_SINGLETONSTUFFING = 17,

  // enable presolver DualFix in PaPILO?
  SIMPLIFIER_DUALFIX = 18,

  // enable presolver FixContinuous in PaPILO?
  SIMPLIFIER_FIXCONTINUOUS = 19,

  // enable presolver DominatedCols in PaPILO?
  SIMPLIFIER_DOMINATEDCOLS = 20,

  // enable iterative refinement ?
  ITERATIVE_REFINEMENT = 21,

  /// adapt tolerances to the multiprecision used
  ADAPT_TOLS_TO_MULTIPRECISION = 22,

  /// enable precision boosting ?
  PRECISION_BOOSTING = 23,

  /// boosted solver start from last basis
  BOOSTED_WARM_START = 24,

  /// try different settings when solve fails
  RECOVERY_MECHANISM = 25,

  /// number of boolean parameters
  BOOLPARAM_COUNT = 26
} BoolParam;

/// integer parameters
typedef enum {
  /// objective sense
  OBJSENSE = 0,

  /// type of computational form, i.e., column or row representation
  REPRESENTATION = 1,

  /// type of algorithm, i.e., primal or dual
  ALGORITHM = 2,

  /// type of LU update
  FACTOR_UPDATE_TYPE = 3,

  /// maximum number of updates without fresh factorization
  FACTOR_UPDATE_MAX = 4,

  /// iteration limit (-1 if unlimited)
  ITERLIMIT = 5,

  /// refinement limit (-1 if unlimited)
  REFLIMIT = 6,

  /// stalling refinement limit (-1 if unlimited)
  STALLREFLIMIT = 7,

  /// display frequency
  DISPLAYFREQ = 8,

  /// verbosity level
  VERBOSITY = 9,

  /// type of simplifier
  SIMPLIFIER = 10,

  /// type of scaler
  SCALER = 11,

  /// type of starter used to create crash basis
  STARTER = 12,

  /// type of pricer
  PRICER = 13,

  /// type of ratio test
  RATIOTESTER = 14,

  /// mode for synchronizing real and rational LP
  SYNCMODE = 15,

  /// mode for reading LP files
  READMODE = 16,

  /// mode for iterative refinement strategy
  SOLVEMODE = 17,

  /// mode for a posteriori feasibility checks
  CHECKMODE = 18,

  /// type of timer
  TIMER = 19,

  /// mode for hyper sparse pricing
  HYPER_PRICING = 20,

  /// minimum number of stalling refinements since last pivot to trigger
  /// rational factorization
  RATFAC_MINSTALLS = 21,

  /// maximum number of conjugate gradient iterations in least square scaling
  LEASTSQ_MAXROUNDS = 22,

  /// mode for solution polishing
  SOLUTION_POLISHING = 23,

  /// print condition number during the solve
  PRINTBASISMETRIC = 24,

  /// type of timer for statistics
  STATTIMER = 25,

  // maximum number of digits for the multiprecision type
  MULTIPRECISION_LIMIT = 26,

  ///@todo precision-boosting find better parameter name
  /// after how many simplex pivots do we store the advanced and stable basis, 1
  /// = every iterations
  STORE_BASIS_SIMPLEX_FREQ = 27,

  /// number of integer parameters
  INTPARAM_COUNT = 28
} IntParam;

/// values for parameter OBJSENSE
enum {
  /// minimization
  OBJSENSE_MINIMIZE = -1,

  /// maximization
  OBJSENSE_MAXIMIZE = 1
};

/// values for parameter ALGORITHM
enum {
  /// primal simplex algorithm, i.e., entering for column and leaving for row
  /// representation
  ALGORITHM_PRIMAL = 0,

  /// dual simplex algorithm, i.e., leaving for column and entering for row
  /// representation
  ALGORITHM_DUAL = 1
};

/// values for parameter VERBOSITY
enum {
  /// only error output
  VERBOSITY_ERROR = 0,

  /// only error and warning output
  VERBOSITY_WARNING = 1,

  /// only error, warning, and debug output
  VERBOSITY_DEBUG = 2,

  /// standard verbosity level
  VERBOSITY_NORMAL = 3,

  /// high verbosity level
  VERBOSITY_HIGH = 4,

  /// full verbosity level
  VERBOSITY_FULL = 5
};

/// values for parameter SIMPLIFIER
enum {
  /// disabling presolving
  SIMPLIFIER_OFF = 0,

  /// using internal presolving methods
  SIMPLIFIER_INTERNAL = 3,

  /// using the presolve lib papilo
  SIMPLIFIER_PAPILO = 2,

  /// SoPlex chooses automatically (currently always "internal")
  SIMPLIFIER_AUTO = 1
};

/// values for parameter PRICER
enum {
  /// automatic pricer
  PRICER_AUTO = 0,

  /// Dantzig pricer
  PRICER_DANTZIG = 1,

  /// partial multiple pricer based on Dantzig pricing
  PRICER_PARMULT = 2,

  /// devex pricer
  PRICER_DEVEX = 3,

  /// steepest edge pricer with initialization to unit norms
  PRICER_QUICKSTEEP = 4,

  /// steepest edge pricer with exact initialization of norms
  PRICER_STEEP = 5
};

/// real parameters
typedef enum {
  /// primal feasibility tolerance
  FEASTOL = 0,

  /// dual feasibility tolerance
  OPTTOL = 1,

  /// general zero tolerance
  EPSILON_ZERO = 2,

  /// zero tolerance used in factorization
  EPSILON_FACTORIZATION = 3,

  /// zero tolerance used in update of the factorization
  EPSILON_UPDATE = 4,

  /// pivot zero tolerance used in factorization
  EPSILON_PIVOT = 5,

  /// infinity threshold
  INFTY = 6,

  /// time limit in seconds (INFTY if unlimited)
  TIMELIMIT = 7,

  /// lower limit on objective value
  OBJLIMIT_LOWER = 8,

  /// upper limit on objective value
  OBJLIMIT_UPPER = 9,

  /// working tolerance for feasibility in floating-point solver during
  /// iterative refinement
  FPFEASTOL = 10,

  /// working tolerance for optimality in floating-point solver during iterative
  /// refinement
  FPOPTTOL = 11,

  /// maximum increase of scaling factors between refinements
  MAXSCALEINCR = 12,

  /// lower threshold in lifting (nonzero matrix coefficients with smaller
  /// absolute value will be reformulated)
  LIFTMINVAL = 13,

  /// upper threshold in lifting (nonzero matrix coefficients with larger
  /// absolute value will be reformulated)
  LIFTMAXVAL = 14,

  /// sparse pricing threshold (\#violations < dimension * SPARSITY_THRESHOLD
  /// activates sparse pricing)
  SPARSITY_THRESHOLD = 15,

  /// threshold on number of rows vs. number of columns for switching from
  /// column to row representations in auto mode
  REPRESENTATION_SWITCH = 16,

  /// geometric frequency at which to apply rational reconstruction
  RATREC_FREQ = 17,

  /// minimal reduction (sum of removed rows/cols) to continue simplification
  MINRED = 18,

  /// refactor threshold for nonzeros in last factorized basis matrix compared
  /// to updated basis matrix
  REFAC_BASIS_NNZ = 19,

  /// refactor threshold for fill-in in current factor update compared to
  /// fill-in in last factorization
  REFAC_UPDATE_FILL = 20,

  /// refactor threshold for memory growth in factorization since last
  /// refactorization
  REFAC_MEM_FACTOR = 21,

  /// accuracy of conjugate gradient method in least squares scaling (higher
  /// value leads to more iterations)
  LEASTSQ_ACRCY = 22,

  /// objective offset
  OBJ_OFFSET = 23,

  /// minimal Markowitz threshold to control sparsity/stability in LU
  /// factorization
  MIN_MARKOWITZ = 24,

  /// minimal modification threshold to apply presolve reductions
  SIMPLIFIER_MODIFYROWFAC = 25,

  /// factor by which the precision of the floating-point solver is multiplied
  PRECISION_BOOSTING_FACTOR = 26,

  /// number of real parameters
  REALPARAM_COUNT = 27
} RealParam;
#pragma endregion

typedef enum {
  ON_UPPER, ///< variable set to its upper bound.
  ON_LOWER, ///< variable set to its lower bound.
  FIXED,    ///< variable fixed to identical bounds.
  ZERO,     ///< free variable fixed to zero.
  BASIC,    ///< variable is basic.
  UNDEFINED ///< nothing known about basis status (possibly due to a singular
            ///< basis in transformed problem)
} VarStatus;

/**@todo In spxchange, change the status to
   if (m_status > 0) m_status = REGULAR;
*/
typedef enum {
  ERROR = -15,          ///< an error occured.
  NO_RATIOTESTER = -14, ///< No ratiotester loaded
  NO_PRICER = -13,      ///< No pricer loaded
  NO_SOLVER = -12,      ///< No linear solver loaded
  NOT_INIT = -11,       ///< not initialised error
  ABORT_CYCLING = -8,   ///< solve() aborted due to detection of cycling.
  ABORT_TIME = -7,      ///< solve() aborted due to time limit.
  ABORT_ITER = -6,      ///< solve() aborted due to iteration limit.
  ABORT_VALUE = -5,     ///< solve() aborted due to objective limit.
  SINGULAR = -4,        ///< Basis is singular, numerical troubles?
  NO_PROBLEM = -3,      ///< No Problem has been loaded.
  REGULAR = -2,         ///< LP has a usable Basis (maybe LP is changed).
  RUNNING = -1,         ///< algorithm is running
  UNKNOWN = 0,          ///< nothing known on loaded problem.
  OPTIMAL = 1,          ///< LP has been solved to optimality.
  UNBOUNDED = 2,        ///< LP has been proven to be primal unbounded.
  INFEASIBLE = 3,       ///< LP has been proven to be primal infeasible.
  INForUNBD = 4,        ///< LP is primal infeasible or unbounded.
  OPTIMAL_UNSCALED_VIOLATIONS = 5 ///< LP has beed solved to optimality but
                                  ///< unscaled solution contains violations.
} SolverStatus;

typedef struct {
  void *prob;          ///< The SoPlex LP problem
  void *lp;            ///< The SoPlex LP data structure
  SolverStatus status; ///< Status of the LP problem after solving

  thvar_t *col_to_var; ///< Map from column index in the LP to theory var
  thvar_t *row_to_var; ///< Map from row index in the LP to theory var

  int32_t *var_to_col; ///< Map from theory var to column index in the LP
  int32_t *var_to_row; ///< Map from theory var to row index in the LP

  int32_t n_cols; ///< Number of estimated LP columns
  int32_t n_rows; ///< Number of estimated LP rows

  mpq_t *x; ///< Temporary rational for storing the solution
  mpq_t *y; ///< Temporary rational for storing the dual solution
} spx_t;

/** Maximum number of pivots before LP termination */
static const int pivot_threshold = 1000000;
/** Global flag indicating whether the QSopt_ex runtime has been initialized */
static bool spx_started = false;
/** Global variable representing the rational number -1 for LP computations */
static mpq_t mpq_oneLpNum;
static mpq_t mpq_zeroLpNum;
static mpq_t mpq_negoneLpNum;
static mpq_t mpq_infLpNum;
static mpq_t mpq_ninfLpNum;

static void global_spx_start() {
  if (spx_started)
    return;
  mpq_init(mpq_oneLpNum);
  mpq_set_si(mpq_oneLpNum, 1, 1);
  mpq_init(mpq_zeroLpNum);
  mpq_set_si(mpq_zeroLpNum, 0, 1);
  mpq_init(mpq_negoneLpNum);
  mpq_set_si(mpq_negoneLpNum, -1, 1);
  mpq_init(mpq_infLpNum);
  mpq_set_d(mpq_infLpNum, SoPlex_infinity);
  mpq_init(mpq_ninfLpNum);
  mpq_set_d(mpq_ninfLpNum, -SoPlex_infinity);
  spx_started = true;
}

void global_spx_clear() {
  if (!spx_started)
    return;
  mpq_clear(mpq_oneLpNum);
  mpq_clear(mpq_zeroLpNum);
  mpq_clear(mpq_negoneLpNum);
  mpq_clear(mpq_infLpNum);
  mpq_clear(mpq_ninfLpNum);
  spx_started = false;
}

/**
 * Checks whether a theory variable is already represented as a column in the
 * QSopt_ex problem.
 * @param spx The QSopt_ex problem wrapper containing column-to-variable maps.
 * @param v The theory variable to inspect.
 * @return true if the variable has a mapped column index; otherwise false.
 */
static bool var_in_columns(const spx_t *const spx, const thvar_t v) {
  return spx->var_to_col[v] != -1;
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
 * Determines whether a theory variable should be encoded as an auxiliary row in
 * the LP model.
 * We only care about polynomials that are not constants.
 * E.g., p := a.x or p := a.x + c, but not p := c, where c is a constant.
 * @param solver The simplex solver containing the variable table and bounds.
 * @param v The theory variable to inspect.
 * @return true if the variable is a polynomial-defined non-constant row; false
 * otherwise.
 */
static bool var_is_valid_row(simplex_solver_t *const solver, const thvar_t v) {
  if (!arith_var_def_is_poly(&solver->vtbl, v))
    return false;
  const polynomial_t *const p = arith_var_poly_def(&solver->vtbl, v);
  assert(p);
  return !(p->nterms == 1 && p->mono[0].var == const_idx) &&
         has_any_bound(solver, v);
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
static bool var_is_valid_strict_column(simplex_solver_t *const solver,
                                       const thvar_t v) {
  if (arith_var_is_free(&solver->vtbl, v) &&
      (has_strict_lb(solver, v) || has_strict_ub(solver, v)))
    return true;
  return false;
}

static external_simplex_status_t
spx_status_to_sol_status(const spx_t *const spx) {
  switch (spx->status) {
  case OPTIMAL:
  case UNBOUNDED:
    return is_strict_var_zero(spx->x[spx->n_cols]) ? EXTERNAL_SIMPLEX_INFEASIBLE
                                                   : EXTERNAL_SIMPLEX_FEASIBLE;
    break;
  case INFEASIBLE:
    return EXTERNAL_SIMPLEX_INFEASIBLE;
  case ABORT_ITER:
  case ABORT_TIME:
  case ABORT_CYCLING:
    return EXTERNAL_SIMPLEX_EXHAUSTED;
    break;
  default:
    return EXTERNAL_SIMPLEX_ERROR;
  }
}

/**
 * Creates a new QSopt_ex LP problem wrapper and configures solver parameters.
 * @param spx The wrapper to initialize.
 */
static void spx_init(spx_t *spx) {
  global_spx_start();
  memset(spx, 0, sizeof(spx_t));

  spx->prob = SoPlex_create();
  spx->lp = NULL;

  void *const prob = spx->prob;
  SoPlex_setRational(prob);
  SoPlex_setIntParam(prob, OBJSENSE, OBJSENSE_MINIMIZE);
  SoPlex_setIntParam(prob, SIMPLIFIER, SIMPLIFIER_OFF);
  SoPlex_setIntParam(prob, ALGORITHM, ALGORITHM_PRIMAL);
  SoPlex_setIntParam(prob, VERBOSITY, VERBOSITY_ERROR);
  SoPlex_setIntParam(prob, PRICER, PRICER_AUTO);
  SoPlex_setIntParam(prob, ITERLIMIT, pivot_threshold);

  // If delta, allow for feasibility tolerance
  SoPlex_setRealParam(prob, FEASTOL,
                      __smt2_globals.delta > 0 ? __smt2_globals.delta : 0.0);
  SoPlex_setRealParam(prob, OPTTOL, 0.0);
}

static void spx_estimate_n_cols_and_rows_epsilon(simplex_solver_t *const solver,
                                                 spx_t *spx) {
  assert(__smt2_globals.epsilon_mode);
  assert(spx->n_cols == 0);
  assert(spx->n_rows == 0);
  const uint32_t nvars = solver->vtbl.nvars;

  for (thvar_t v = 0; v < nvars; v++) {
    if (var_is_valid_row(solver, v)) {
      spx->n_rows++;
    } else if (var_is_valid_column(solver, v)) {
      spx->n_cols++;
    }
  }
}

static void allocate_and_init(mpq_t **array, const size_t size) {
  assert(*array == NULL);
  *array = safe_malloc(size * sizeof(mpq_t));
  for (size_t i = 0; i < size; i++) {
    mpq_init((*array)[i]);
  }
}

static void clear_and_free(mpq_t **array, const size_t size) {
  if (*array) {
    for (size_t i = 0; i < size; i++) {
      mpq_clear((*array)[i]);
    }
    free(*array);
    *array = NULL;
  }
}

static void spx_estimate_n_cols_and_rows_strict(simplex_solver_t *const solver,
                                                spx_t *spx) {
  assert(!__smt2_globals.epsilon_mode);
  assert(spx->n_cols == 0);
  assert(spx->n_rows == 0);
  const uint32_t nvars = solver->vtbl.nvars;
  for (thvar_t v = 0; v < nvars; v++) {
    if (var_is_valid_row(solver, v)) {
      spx->n_rows++;
      if ((has_strict_lb(solver, v) || has_strict_ub(solver, v)) &&
          has_lb(solver, v) && has_ub(solver, v)) {
        spx->n_rows++;
      }
    } else if (var_is_valid_column(solver, v)) {
      spx->n_cols++;
      // If epsilon mode is disables (i.e., we are using strict mode),
      // then we need to encode the strict bounds on the free var
      // by using some strict constraint
      if (has_strict_lb(solver, v)) {
        spx->n_rows++;
      }
      if (has_strict_ub(solver, v)) {
        spx->n_rows++;
      }
    }
  }
}

/**
 * Allocates the QSopt_ex column/row mappings and temporary numeric arrays for a
 * simplex solver.
 * @param solver The simplex solver whose arithmetic variables will be
 * translated to LP variables.
 * @param spx The QSopt_ex wrapper that receives the allocated arrays and
 * indexes.
 */
static void spx_init_vars(simplex_solver_t *const solver, spx_t *spx) {
  const uint32_t nvars = solver->vtbl.nvars;

  // Set the number of auxiliary variables in the QSopt_ex problem,
  // which is equal to the rows of the LP problem,
  // and the number of structural variables,
  // which is equal to the columns of the LP problem.
  spx->n_cols = 0;
  spx->n_rows = 0;
  if (__smt2_globals.epsilon_mode) {
    spx_estimate_n_cols_and_rows_epsilon(solver, spx);
  } else {
    spx_estimate_n_cols_and_rows_strict(solver, spx);
  }

  spx->lp = SoPlex_createLpProblemRational(spx->n_cols, spx->n_rows);
  spx->col_to_var = safe_malloc(spx->n_cols * sizeof(thvar_t));
  spx->row_to_var = safe_malloc(spx->n_rows * sizeof(thvar_t));
  spx->var_to_col = safe_malloc(nvars * sizeof(uint32_t));
  spx->var_to_row = safe_malloc(nvars * sizeof(uint32_t));
  // We are adding an additional variable to the LP problem
  // to collect the value of the strict var, if needed.
  // There is no need do add it anywhere else
  spx->x = NULL;
  spx->y = NULL;

  for (uint32_t i = 0; i < spx->n_cols; i++) {
    spx->col_to_var[i] = -1;
  }

  for (uint32_t i = 0; i < spx->n_rows; i++) {
    spx->row_to_var[i] = -1;
  }
  for (uint32_t i = 0; i < nvars; i++) {
    spx->var_to_col[i] = -1;
    spx->var_to_row[i] = -1;
  }
}

/**
 * Frees all memory owned by a QSopt_ex wrapper and clears the stored basis.
 * @param spx The QSopt_ex wrapper to destroy.
 */
static void spx_clear(spx_t *const spx) {
  SoPlex_freeLPProblemRational(spx->lp);
  SoPlex_free(spx->prob);
  safe_free(spx->col_to_var);
  safe_free(spx->row_to_var);
  safe_free(spx->var_to_col);
  safe_free(spx->var_to_row);
  clear_and_free(&spx->x, spx->n_cols + 1);
  clear_and_free(&spx->y, spx->n_rows);
}

/**
 * Adds all free arithmetic variables as structural columns in the QSopt_ex LP.
 * Each variable that is valid as a column is assigned the corresponding finite
 * or infinite lower/upper bounds from the simplex solver, and the mapping
 * arrays in @p spx are updated so later row-building logic can refer back to
 * the original theory variable identifiers. In epsilon mode, any strict bound
 * is made stricter by using an hardcoded value @f \epsilon @f.
 * @param solver The simplex solver containing the variable bounds and
 * definitions.
 * @param spx The QSopt_ex problem wrapper receiving the new columns.
 */
static void add_cols_epsilon(simplex_solver_t *const solver,
                             const spx_t *const spx) {
  assert(spx->n_cols > 0);
  void *lp = spx->lp;

  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  int col_idx = 0;
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {
    // Free variables. They come from the SMT input. Encode them as columns.
    if (var_is_valid_column(solver, v)) {
      bound_type_t lb, ub;
      get_bound_copy(solver, v, true, &lb);
      get_bound_copy(solver, v, false, &ub);

      spx->col_to_var[col_idx] = v;
      spx->var_to_col[v] = col_idx;
      SoPlex_addColToLpProblemRational(lp, NULL, 0, 0, mpq_zeroLpNum,
                                       lb.is_finite ? lb.val : mpq_ninfLpNum,
                                       ub.is_finite ? ub.val : mpq_infLpNum);

      col_idx++;
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
  bound_type_t lb;
  bound_type_t ub;
} row_data_t;

typedef struct row_accumulator_s {
  mpq_t *values;
  int *values_idxs;
  int n_values;
} row_accumulator_t;

static void row_accumulator_init(row_accumulator_t *const accumulator,
                                 const int n_cols) {
  accumulator->values = safe_malloc(n_cols * sizeof(mpq_t));
  memset(accumulator->values, 0, n_cols * sizeof(mpq_t));
  accumulator->values_idxs = safe_malloc(n_cols * sizeof(int));
  accumulator->n_values = 0;
}

static void row_accumulator_clear(row_accumulator_t *const accumulator,
                                  const bool clear_mpqs) {
  if (clear_mpqs) {
    for (int i = 0; i < accumulator->n_values; i++) {
      mpq_clear(accumulator->values[accumulator->values_idxs[i]]);
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
  if (accumulator->values[col_idx]->_mp_num._mp_d == NULL) {
    mpq_init(accumulator->values[col_idx]);
    mpq_set(accumulator->values[col_idx], value);
    accumulator->values_idxs[accumulator->n_values++] = col_idx;
  } else {
    mpq_add(accumulator->values[col_idx], accumulator->values[col_idx], value);
  }
}

static void row_accumulator_add_q(row_accumulator_t *const accumulator,
                                  const int col_idx, const rational_t *value) {
  if (is_ratgmp(value)) {
    row_accumulator_add_mpq(accumulator, col_idx, get_gmp(value));
  } else {
    if (accumulator->values[col_idx]->_mp_num._mp_d == NULL) {
      mpq_init(accumulator->values[col_idx]);
      mpq_set_si(accumulator->values[col_idx], get_num(value), get_den(value));
      accumulator->values_idxs[accumulator->n_values++] = col_idx;
    } else {
      mpq_add_si(accumulator->values[col_idx], get_num(value), get_den(value));
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
 * @param spx The QSopt_ex wrapper holding the column and row mappings.
 * @param v The theory variable whose polynomial contribution is being emitted.
 * @param row_data Aggregated row data that stores column indices and values.
 * @param accumulator Optional accumulator to collect non-zero coefficients for
 * the row.
 * @param p_coeff Optional parent coefficient to multiply into this polynomial.
 * @return The number of non-zero coefficients added to the row.
 */
static void monomials_to_row(simplex_solver_t *const solver,
                             const spx_t *const spx, const thvar_t v,
                             row_data_t *const row_data,
                             row_accumulator_t *const accumulator,
                             const rational_t *const p_coeff) {
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
      if (row_data->lb.is_finite) {
        mpq_q_sub(row_data->lb.val, row_data->lb.val, coeff);
      }
      if (row_data->ub.is_finite) {
        mpq_q_sub(row_data->ub.val, row_data->ub.val, coeff);
      }
    } else if (var_in_columns(spx, x)) {
      assert(var_is_valid_column(solver, x));
      // Add var coefficient
      row_accumulator_add_q(accumulator, spx->var_to_col[x], coeff);
    } else {
      assert(arith_var_def_is_poly(&solver->vtbl, x));
      monomials_to_row(solver, spx, x, row_data, accumulator, coeff);
    }

    q_clear(&temp_coeff);
  }
}

static int polynomial_to_row(simplex_solver_t *const solver,
                             const spx_t *const spx, const thvar_t v,
                             row_data_t *const row_data) {
  row_accumulator_t accumulator;
  row_accumulator_init(&accumulator, spx->n_cols);
  monomials_to_row(solver, spx, v, row_data, &accumulator, NULL);
  const int num_non_zeros = accumulator.n_values;

  for (int i = 0; i < num_non_zeros; i++) {
    const int col_idx = accumulator.values_idxs[i];
    row_data->col_idxs[i] = col_idx;
    // Transfer ownership to the row_data values array
    memcpy(row_data->values[i], accumulator.values[col_idx], sizeof(mpq_t));
  }

  // We do not need to clear the mpq_t values in the accumulator
  // because they have been assigned to the row_data values array,
  // which will be cleared later.
  row_accumulator_clear(&accumulator, false);
  return num_non_zeros;
}

/**
 * Extracts the value of a structural variable from the solved QSopt_ex LP and
 * stores it in the external solution object.
 * @param solver The simplex solver used to interpret the variable bounds.
 * @param spx The solved QSopt_ex problem containing the LP basis and values.
 * @param sol The destination solution record to update.
 * @param i The LP column index to extract.
 * @param vals The array of variable values from the solved LP.
 * If it is the spx->x array, then the variable is a column;
 * if it is the spx->y array, then it is a row.
 * If it is NULL, then the variable must be obtained from the LP activity.
 */
static void extract_value(simplex_solver_t *const solver, spx_t *const spx,
                          external_solution_t *const sol, const int i,
                          const mpq_t *const vals) {
  xrational_t *const x = sol->x;
  const bool is_col = vals == spx->x;
  const thvar_t v = is_col ? spx->col_to_var[i] : spx->row_to_var[i];
  const VarStatus var_status = is_col ? SoPlex_basisColStatus(spx->prob, i)
                                      : SoPlex_basisRowStatus(spx->prob, i);

  if (var_status == BASIC)
    int_bvset_add(&sol->b_vars, v);
  else
    int_bvset_add(&sol->nb_vars, v);

  switch (var_status) {
    // If we are dealing with a basic variable, we necessarily need to get its
    // value from the solved problem.
  case BASIC:
  case UNDEFINED: // Shared with basic
    // Start by setting the current basic result
    if (vals) {
      xq_set_mpq_prenormalize(x + v, vals[i]);
    } else {
      mpq_t activity;
      mpq_init(activity);
      if (is_col) {
        SoPlex_getColActivityRational_mpq(spx->prob, i, activity);
      } else {
        SoPlex_getRowActivityRational_mpq(spx->prob, i, activity);
      }
      xq_set_mpq_prenormalize(x + v, activity);
      mpq_clear(activity);
    }
    // Ensure the result is within the bounds of the variable, if any
    if (is_below_or_eq_lb(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_LOWER;
    } else if (is_above_or_eq_ub(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_UPPER;
    }
    break;
    // For non-basic variables we know the value is at a bound
    // and we can use the d_vars/proper LP bounds directly
  case FIXED:
  case ON_LOWER:
    assert(has_lb(solver, v));
    sol->bounds[v] = VAR_BOUND_AT_LOWER;
    break;
  case ON_UPPER:
    assert(has_ub(solver, v));
    sol->bounds[v] = VAR_BOUND_AT_UPPER;
    break;
  case ZERO:
    xq_set_mpq_prenormalize(x + v, mpq_zeroLpNum);
    assert(xq_is_zero(x + v));
    if (is_below_or_eq_lb(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_LOWER;
    } else if (is_above_or_eq_ub(solver, v, x + v)) {
      sol->bounds[v] = VAR_BOUND_AT_UPPER;
    }
    break;
  default:
    printf("Unknown variable status for variable %d: %c\n", v, var_status);
    exit(1);
  }
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
 * @param spx The QSopt_ex LP wrapper receiving the encoded rows.
 */
static void add_rows_epsilon(simplex_solver_t *const solver,
                             const spx_t *const spx) {
  assert(spx->n_rows > 0);
  mpq_t values[SoPlex_getNumColsLpProblemRational(spx->lp)];
  int col_idxs[SoPlex_getNumColsLpProblemRational(spx->lp)];
  for (int i = 0; i < SoPlex_getNumColsLpProblemRational(spx->lp); i++) {
    mpq_init(values[i]);
  }

  row_data_t rd = {.col_idxs = col_idxs, .values = values};

  // Add rows to the LP problem
  int row_idx = 0;
  const int32_t n_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < n_vars; v++) {
    const int r = row_idx;
    // Skip structural variables and constants
    if (!var_is_valid_row(solver, v)) {
      continue;
    }

    // Add row range
    get_bound_copy(solver, v, true, &rd.lb);
    get_bound_copy(solver, v, false, &rd.ub);

    const int num_non_zeros = polynomial_to_row(solver, spx, v, &rd);

    SoPlex_addRowToLpProblemRational(
        spx->lp, rd.values, rd.col_idxs, num_non_zeros,
        rd.lb.is_finite ? rd.lb.val : mpq_ninfLpNum,
        rd.ub.is_finite ? rd.ub.val : mpq_infLpNum);

    bound_type_clear(&rd.lb);
    bound_type_clear(&rd.ub);

    // Add the new row to the map
    spx->row_to_var[r] = v;
    spx->var_to_row[v] = r;
    row_idx++;
  }

  mpq_vector_clear(rd.values, SoPlex_getNumColsLpProblemRational(spx->lp));
}

/**
 * Extracts every solved value from the epsilon-mode QSopt_ex LP into the
 * external solution record.
 * @param solver The simplex solver whose bounds are used to validate each
 * value.
 * @param spx The solved QSopt_ex LP instance to read from.
 * @param sol The output solution object to populate.
 */
static void extract_solution_epsilon(simplex_solver_t *solver, spx_t *spx,
                                     external_solution_t *sol) {
  void *const prob = spx->prob;

  for (int col_idx = 0; col_idx < SoPlex_numCols(prob); col_idx++) {
    extract_value(solver, spx, sol, col_idx, spx->x);
  }
  for (int row_idx = 0; row_idx < SoPlex_numRows(prob); row_idx++) {
    extract_value(solver, spx, sol, row_idx, spx->y);
  }
}

/**
 * Builds the LP encoding for the epsilon-mode simplex problem.
 * @note `add_cols_epsilon` must be called before `add_rows_epsilon`, since
 * the latter depends on the column indices being populated first.
 * @param solver The simplex solver whose structural variables and constraints
 * define the LP.
 * @param spx The QSopt_ex wrapper to populate with columns and rows.
 */
static void spx_build_problem_epsilon(simplex_solver_t *const solver,
                                      spx_t *const spx) {
  add_cols_epsilon(solver, spx);
  add_rows_epsilon(solver, spx);
  SoPlex_loadLpProblemRational(spx->prob, spx->lp);
  assert(spx->n_cols == SoPlex_numColsRational(spx->prob));
  assert(spx->n_rows == SoPlex_numRowsRational(spx->prob));
}

#pragma endregion

#pragma region Strict mode

/**
 * Reserved placeholder for strict-mode column construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the variable definitions.
 * @param spx The QSopt_ex wrapper that would receive the strict-mode columns.
 */
static void add_cols_strict(simplex_solver_t *const solver, spx_t *const spx) {
  assert(spx->n_cols > 0);
  // Construct the columns of the LP by assigning upper/lower bounds to each
  // variable
  int col_idx = 0;
  const int32_t num_vars = (int32_t)solver->vtbl.nvars;
  for (thvar_t v = 0; v < num_vars; v++) {
    // Free variables. They come from the SMT input. Encode them as columns.
    if (var_is_valid_column(solver, v)) {
      bound_type_t lb, ub;
      get_bound_copy(solver, v, true, &lb);
      get_bound_copy(solver, v, false, &ub);

      spx->col_to_var[col_idx] = v;
      spx->var_to_col[v] = col_idx;
      SoPlex_addColToLpProblemRational(
          spx->lp, NULL, NULL, 0, mpq_zeroLpNum,
          lb.is_finite && !lb.is_strict ? lb.val : mpq_ninfLpNum,
          ub.is_finite && !ub.is_strict ? ub.val : mpq_infLpNum);

      col_idx++;
      bound_type_clear(&lb);
      bound_type_clear(&ub);
    }

    // If the variable is not free, it is an auxiliary variable.
    // We will encode those as rows later.
  }

  // At the end, add the strict variable column,
  // which is used to encode the strict bounds
  SoPlex_addColToLpProblemRational(spx->lp, NULL, NULL, 0, mpq_zeroLpNum,
                                   mpq_zeroLpNum, mpq_oneLpNum);
}

/**
 * Reserved placeholder for strict-mode row construction.
 * This function is intentionally empty because the strict-mode QSopt_ex bridge
 * is not yet implemented.
 * @param solver The simplex solver containing the row definitions.
 * @param spx The QSopt_ex wrapper that would receive the strict-mode rows.
 */
static void add_rows_strict(simplex_solver_t *const solver, spx_t *const spx) {
  assert(spx->n_rows > 0);

  const int strict_var_idx = spx->n_cols; // Index of the strict variable column
  mpq_t rhs;
  mpq_init(rhs);
  mpq_t values[SoPlex_getNumColsLpProblemRational(spx->lp)];
  int col_idxs[SoPlex_getNumColsLpProblemRational(spx->lp)];
  for (int i = 0; i < SoPlex_getNumColsLpProblemRational(spx->lp); i++) {
    mpq_init(values[i]);
  }

  row_data_t rd = {.col_idxs = col_idxs, .values = values};

  // Add rows to the LP problem
  int row_idx = 0;
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
        rd.col_idxs[0] = spx->var_to_col[v];
        rd.col_idxs[1] = strict_var_idx;
        // Add 1 coeff to the variable and -1 to the strict variable
        mpq_set(rd.values[0], mpq_oneLpNum);
        mpq_set(rd.values[1], mpq_negoneLpNum);
        // Set the sense 'Greater Than'
        // Set the right-hand side to the lower bound of the variable
        copy_to_gmp(rhs, &get_lb(solver, v)->main);

        SoPlex_addRowToLpProblemRational(spx->lp, rd.values, rd.col_idxs, 2,
                                         rhs, mpq_infLpNum);

        // Update the mapping and increment the row index
        spx->row_to_var[row_idx] = v;
        spx->var_to_row[v] = row_idx;
        row_idx++;
      }
      if (has_strict_ub(solver, v)) {
        assert(has_ub(solver, v));
        rd.col_idxs[0] = spx->var_to_col[v];
        rd.col_idxs[1] = strict_var_idx;
        // Add 1 coeff to the variable and 1 to the strict variable
        mpq_set(rd.values[0], mpq_oneLpNum);
        mpq_set(rd.values[1], mpq_oneLpNum);
        // Set the right-hand side to the lower bound of the variable
        copy_to_gmp(rhs, &get_ub(solver, v)->main);

        SoPlex_addRowToLpProblemRational(spx->lp, rd.values, rd.col_idxs, 2,
                                         mpq_ninfLpNum, rhs);

        // Update the mapping and increment the row index
        spx->row_to_var[row_idx] = v;
        spx->var_to_row[v] = row_idx;
        row_idx++;
      }
      continue;
    }

    // Add row range
    get_bound_copy(solver, v, true, &rd.lb);
    get_bound_copy(solver, v, false, &rd.ub);

    int num_non_zeros = polynomial_to_row(solver, spx, v, &rd);

    // There is at least a strict bound, they need to be handled by including
    // the strict variable in the row
    if (has_strict_lb(solver, v) || has_strict_ub(solver, v)) {
      const bool is_lb_strict = has_strict_lb(solver, v);

      if (rd.lb.is_finite) {
        if (is_lb_strict) {
          rd.col_idxs[num_non_zeros] = strict_var_idx;
          mpq_set(rd.values[num_non_zeros], mpq_negoneLpNum);
          num_non_zeros++;
        }

        SoPlex_addRowToLpProblemRational(spx->lp, rd.values, rd.col_idxs,
                                         num_non_zeros, rd.lb.val,
                                         mpq_infLpNum);

        // Add the new row to the map
        spx->row_to_var[row_idx] = v;
        spx->var_to_row[v] = row_idx;
        row_idx++;
      }

      if (rd.lb.is_strict)
        num_non_zeros--;

      if (rd.ub.is_finite) {
        if (rd.ub.is_strict) {
          rd.col_idxs[num_non_zeros] = strict_var_idx;
          mpq_set(rd.values[num_non_zeros], mpq_oneLpNum);
          num_non_zeros++;
        }

        SoPlex_addRowToLpProblemRational(spx->lp, rd.values, rd.col_idxs,
                                         num_non_zeros, mpq_ninfLpNum,
                                         rd.ub.val);

        // Add the new row to the map
        spx->row_to_var[row_idx] = v;
        spx->var_to_row[v] = row_idx;
        row_idx++;
      }

      bound_type_clear(&rd.lb);
      bound_type_clear(&rd.ub);
      continue;
    }

    assert(!has_strict_lb(solver, v) && !has_strict_ub(solver, v));

    SoPlex_addRowToLpProblemRational(
        spx->lp, rd.values, rd.col_idxs, num_non_zeros,
        rd.lb.is_finite ? rd.lb.val : mpq_ninfLpNum,
        rd.ub.is_finite ? rd.ub.val : mpq_infLpNum);

    bound_type_clear(&rd.lb);
    bound_type_clear(&rd.ub);

    // Add the new row to the map
    spx->row_to_var[row_idx] = v;
    spx->var_to_row[v] = row_idx;
    row_idx++;
  }

  assert(row_idx == SoPlex_getNumRowsLpProblemRational(spx->lp));
  mpq_vector_clear(rd.values, SoPlex_getNumColsLpProblemRational(spx->lp));
  mpq_clear(rhs);
}

/**
 * Builds the strict-mode LP representation used when strict mode is enabled.
 * @param solver The simplex solver whose constraints define the problem.
 * @param spx The QSopt_ex wrapper to populate.
 */
static void spx_build_problem_strict(simplex_solver_t *const solver,
                                     spx_t *const spx) {
  add_cols_strict(solver, spx);
  add_rows_strict(solver, spx);
  SoPlex_loadLpProblemRational(spx->prob, spx->lp);
  assert(spx->n_cols == SoPlex_numColsRational(spx->prob) - 1);
  assert(spx->n_rows == SoPlex_numRowsRational(spx->prob));
}

/**
 * Extracts every value from a strict-mode LP solution into the external result.
 * @param solver The simplex solver defining the model.
 * @param spx The solved QSopt_ex problem.
 * @param sol The output solution to fill.
 */
static void extract_solution_strict(simplex_solver_t *solver, spx_t *spx,
                                    external_solution_t *sol) {
  const int strict_col_idx = spx->n_cols;
  void *const prob = spx->prob;
  bool is_strict_basic = SoPlex_basisColStatus(prob, strict_col_idx) == BASIC;

  // TODO: we may skip ensuring that the strict variable is 0 entirely
#if 1
  if (spx->x && is_strict_basic && mpq_is_pos(spx->x[strict_col_idx])) {
    SoPlex_changeVarBoundsRational_mpq(spx->prob, strict_col_idx, mpq_zeroLpNum,
                                       mpq_zeroLpNum);

    spx->status = SoPlex_optimize(prob);

    switch (spx->status) {
    case OPTIMAL:
    case UNBOUNDED:
      assert(SoPlex_hasSol(prob));
      clear_and_free(&spx->y, spx->n_rows);
      if (spx->x == NULL)
        allocate_and_init(&spx->x, spx->n_cols + 1);
      SoPlex_getPrimalRational_mpq(prob, spx->x);
      assert(spx->x);
      assert(!spx->y);
      break;
    case INFEASIBLE:
      assert(SoPlex_hasDualFarkas(prob));
      clear_and_free(&spx->x, spx->n_cols + 1);
      if (spx->y == NULL)
        allocate_and_init(&spx->y, spx->n_rows);
      SoPlex_getDualRational_mpq(prob, spx->y);
      assert(!spx->x);
      assert(spx->y);
      break;
    default:
      break;
    }

    const external_simplex_status_t status = spx_status_to_sol_status(spx);
    if (status != EXTERNAL_SIMPLEX_FEASIBLE &&
        status != EXTERNAL_SIMPLEX_INFEASIBLE) {
      // An error occurred, so we don't have a solution
      sol->status = status;
      return;
    }

    is_strict_basic = SoPlex_basisColStatus(prob, strict_col_idx) == BASIC;
  }

  // By this point, if we have a feasible solution,
  // the strict variable is either basic and at 0,
  // or it is non-basic and we don't care about its value.
  // If there is no feasible solution, all bets are off.
  assert(sol->status != EXTERNAL_SIMPLEX_FEASIBLE || !is_strict_basic ||
         mpq_is_zero(spx->x[strict_col_idx]));
#endif

  for (int col_idx = 0; col_idx < spx->n_cols; col_idx++) {
    extract_value(solver, spx, sol, col_idx, spx->x);
  }
  for (int row_idx = 0; row_idx < spx->n_rows; row_idx++) {
    // We already encountered the nonbasic version of this row, we can skip it
    if (int_bvset_member(&sol->nb_vars, spx->row_to_var[row_idx]))
      continue;
    extract_value(solver, spx, sol, row_idx, spx->y);
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
 * @param spx The QSopt_ex LP instance to solve.
 * @param solution The output structure receiving the solved status and variable
 * count.
 */
static void spx_solve_lp(simplex_solver_t *const solver, spx_t *const spx,
                         external_solution_t *const solution) {
  void *const prob = spx->prob;

  spx->status = SoPlex_optimize(prob);

  switch (spx->status) {
  case OPTIMAL:
  case UNBOUNDED:
    assert(SoPlex_hasSol(prob));
    clear_and_free(&spx->y, spx->n_rows);
    if (spx->x == NULL)
      allocate_and_init(&spx->x, spx->n_cols + 1);
    SoPlex_getPrimalRational_mpq(prob, spx->x);
    assert(spx->x);
    assert(!spx->y);
    break;
  case INFEASIBLE:
    assert(SoPlex_hasDualFarkas(prob));
    clear_and_free(&spx->x, spx->n_cols + 1);
    if (spx->y == NULL)
      allocate_and_init(&spx->y, spx->n_rows);
    SoPlex_getDualRational_mpq(prob, spx->y);
    assert(!spx->x);
    assert(spx->y);
    break;
  default:
    break;
  }

  const int refinements = SoPlex_numRefinements(prob);
  if (refinements > solver->stats.iterative_refinements)
    solver->stats.iterative_refinements = refinements;

  const unsigned int num_precision_boosts = SoPlex_numPrecisionBoosts(prob);
  const double precision_boosting_factor =
      SoPlex_getRealParam(prob, PRECISION_BOOSTING_FACTOR);
  unsigned int precision = num_precision_boosts == 0 ? sizeof(double) * 8 : 167;
  for (int i = 1; i < num_precision_boosts; i++) {
    precision = (unsigned int)(precision * precision_boosting_factor);
  }
  if (precision > solver->stats.max_precision)
    solver->stats.max_precision = precision;

  if (__smt2_globals.delta >= 0) {
    const double max_bound_violation =
        SoPlex_getMaxBoundViolationRationalToDouble(prob);
    const double max_row_violation =
        SoPlex_getMaxRowViolationRationalToDouble(prob);
    if (max_bound_violation > solver->stats.max_delta)
      solver->stats.max_delta = max_bound_violation;
    if (max_row_violation > solver->stats.max_delta)
      solver->stats.max_delta = max_row_violation;
    if (max_bound_violation > 0 || max_row_violation > 0)
      solver->stats.delta_calls++;
#if 0
    printf("Max bound violation: %g\n", max_bound_violation);
    printf("Max row violation: %g\n", max_row_violation);
#endif
  }

  solution->nvars = solver->vtbl.nvars;
  solution->status = spx_status_to_sol_status(spx);
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
void spx_solve(simplex_solver_t *solver, external_solution_t *sol) {
  const double start_setup = get_cpu_time();

  spx_t spx;
  spx_init(&spx);
  spx_init_vars(solver, &spx);

  // Edge case: empty problem, feasible by definition
  if (spx.n_cols == 0 || spx.n_rows == 0) {
    sol->status = EXTERNAL_SIMPLEX_FEASIBLE;
    spx_clear(&spx);
    return;
  }

  if (__smt2_globals.epsilon_mode)
    spx_build_problem_epsilon(solver, &spx);
  else
    spx_build_problem_strict(solver, &spx);
#if 0
  static int i = 0;
  mpq_QSdump_prob(spx.prob);
  fprintf(stderr, "Problem %d %s: n_cols = %d, n_rows = %d\n", i,
          __smt2_globals.epsilon_mode ? "epsilon" : "strict", spx.n_cols,
          spx.n_rows);
  char filename[256];
  snprintf(filename, sizeof(filename),
           "/home/campus.ncl.ac.uk/c3054737/Programming/phd/yices2/"
           "qsproblem_%d_%s.lp",
           i, __smt2_globals.epsilon_mode ? "epsilon" : "strict");
  mpq_QSwrite_prob(spx.prob, filename, "LP");
  i++;
#endif
  const double start_solve = get_cpu_time();

  {
    spx_clear(&spx);
    sol->status = EXTERNAL_SIMPLEX_ERROR;
    return;
  }

  spx_solve_lp(solver, &spx, sol);
  // Only extract a solution if the external solver found a valid one
  if (sol->status == EXTERNAL_SIMPLEX_FEASIBLE ||
      sol->status == EXTERNAL_SIMPLEX_INFEASIBLE) {
    if (__smt2_globals.epsilon_mode)
      extract_solution_epsilon(solver, &spx, sol);
    else
      extract_solution_strict(solver, &spx, sol);
  }
  spx_clear(&spx);

  const double end_solve = get_cpu_time();
  solver->stats.external_lp_setup_time += time_diff(start_solve, start_setup);
  solver->stats.external_lp_run_time += time_diff(end_solve, start_setup);
}
