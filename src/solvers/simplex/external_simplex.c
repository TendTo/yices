/**
 * @author c3054737
 * @copyright 2026 yices2
 * @licence BSD 3-Clause License
 * @file
 * external_simplex class.
 */
#include "external_simplex.h"

#include "../../frontend/smt2/smt2_commands.h"
#include "../egraph/egraph_base_types.h"
#include "matrices.h"
#include "simplex.h"
#include "simplex_printer.h"
#include "simplex_types.h"
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

static const bool use_delta = false;
static mpq_t epsilon;
static bool qsx_started = false;

static void convert_to_gmp(rational_t *r, mpq_t *loc) {
  assert(loc);
  assert(!is_ratgmp(r));

  mpq_init(*loc);
  mpq_set_int32(*loc, get_num(r), get_den(r));
  set_ratgmp(r, *loc);
}

static void qsx_start() {
  if (qsx_started)
    return;
  qsx_started = true;
  QSexactStart();
  mpq_init(epsilon);
  mpq_set_ui(epsilon, 1, 1000000);
}

static void qsx_clear() {
  if (!qsx_started)
    return;
  QSexactClear();
  mpq_clear(epsilon);
  qsx_started = false;
}

#if 0

void add_rows() {
  uint32_t strict = 0;

  // Assign each variable to a row and column variable as it appears in the
  // input
  std::vector<int> numNonZeroPerRow;
  std::vector<int> beginRowIdx;
  std::vector<int> colIdxs;
  std::vector<mpq_class> values;

  d_rhs.reserve(d_rowToArithVar.size());
  d_range.reserve(d_rowToArithVar.size());
  numNonZeroPerRow.reserve(d_rowToArithVar.size());
  beginRowIdx.reserve(d_rowToArithVar.size());
  colIdxs.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  values.reserve((d_colToArithVar.size() + d_rowToArithVar.size()) * 2);
  d_sense.reserve(d_rowToArithVar.size());

  // Construct the rows of the LP by parsing the polynomial constraints together
  // with the row bounds on the auxiliary variables
  for (const ArithVar v : d_rowToArithVar) {
    Assert(d_vars.isAuxiliary(v));

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    // std::cout << d_vars.asNode(v).getName() << "\n\n";

    numNonZeroPerRow.emplace_back(p.size());
    beginRowIdx.emplace_back(colIdxs.size());
    for (Polynomial::iterator j = p.begin(), end = p.end(); j != end; ++j) {
      const Monomial &mono = *j;
      const Constant &constant = mono.getConstant();
      const VarList &variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      const int colIdx = static_cast<int>(d_colIndices[av]);

      colIdxs.emplace_back(colIdx);
      // TODO: maybe we can just borrow the reference?
      values.emplace_back(constant.getValue().getValue());
    }

    if (d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)) // Bounded
    {
      d_rhs.emplace_back(!d_useDelta && hasStrictLb(v)
                             ? varToLb(v) + SMALL_FIXED_EPSILON
                             : varToLb(v));
      d_range.emplace_back(
          !d_useDelta && hasStrictUB(v)
              ? mpq_class{varToUb(v) - varToLb(v) - SMALL_FIXED_EPSILON}
              : mpq_class{varToUb(v) - varToLb(v)});
      d_sense.emplace_back('R');
    } else if (d_vars.hasLowerBound(v)) // Only lower bound
    {
      d_rhs.emplace_back(!d_useDelta && hasStrictLb(v)
                             ? varToLb(v) + SMALL_FIXED_EPSILON
                             : varToLb(v));
      d_range.emplace_back(0);
      d_sense.emplace_back('G');
    } else if (d_vars.hasUpperBound(v)) // Only upper bound
    {
      d_rhs.emplace_back(!d_useDelta && hasStrictUB(v)
                             ? varToUb(v) - SMALL_FIXED_EPSILON
                             : varToUb(v));
      d_range.emplace_back(0);
      d_sense.emplace_back('L');
    } else // Unbounded
    {
      d_rhs.emplace_back(mpq_NINFTY);
      d_range.emplace_back(0);
      d_sense.emplace_back('G');
    }
  }

  static_assert(sizeof(mpq_class) == sizeof(mpq_t),
                "mpq_class layout assumption broken");
  mpq_QSadd_ranged_rows(
      d_qsx, static_cast<int>(numNonZeroPerRow.size()), numNonZeroPerRow.data(),
      beginRowIdx.data(), colIdxs.data(),
      reinterpret_cast<const mpq_t *>(values.data()),
      reinterpret_cast<const mpq_t *>(d_rhs.data()), d_sense.data(),
      reinterpret_cast<const mpq_t *>(d_range.data()), nullptr);
}

#endif

typedef struct {
  bool is_finite;
  bool is_strict;
  bool is_lb;
  rational_t val;
} bound_type_t;

/**
 * Obtain a pointer to a bound in terms of mpq_t.
 * The value returned depends on some parameters:
 * - If has_bound is false, the bound is either +infinity or -infinity,
 *   based on the is_lb parameter.
 *   Its value is a pointer to either mpq_INFTY or mpq_NINFTY.
 * - If has_bound is true, the bound is the value of val, possibly adjusted
 *   based on the is_strict parameter.
 *   Since val is a rational_t, it may be stored in a temporary mpq_t if it is
 *   not already a GMP rational. The used_temp parameter indicates whether a
 *   temporary allocation was used.
 * @param bound the value of bound,
 * including whether it is a lower or upper bound, and whether it is strict.
 * @param[out] used_temp whether a temporary allocation was used.
 * If true, the caller is responsible for clearing the temporary mpq_t after
 * use.
 * @param[out] temp a temporary mpq_t.
 * It may be initialized and be pointed by the returned mpq_ptr.
 * If that happens, the caller is responsible for clearing it after use.
 * @return a pointer to the bound
 */
static mpq_ptr get_bound(bound_type_t bound, bool *const used_temp,
                         mpq_t *temp) {
  assert(!*used_temp);
  // Infinity bound
  if (!bound.is_finite) {
    return bound.is_lb ? mpq_NINFTY : mpq_INFTY;
  }

  // Finite bound
  if (is_rat32(&bound.val)) { // Need to convert to GMP
    *used_temp = true;
    convert_to_gmp(&bound.val, temp);
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
        (bound_type_t){.is_finite = has_lb,
                       .is_strict = !use_delta && strict_lb,
                       .is_lb = true,
                       .val = has_lb ? bounds[lb_idx].main : (rational_t){0}},
        &used_temp_lb, &tmp_lb);
    mpq_ptr ub = get_bound(
        (bound_type_t){.is_finite = has_ub,
                       .is_strict = !use_delta && strict_ub,
                       .is_lb = false,
                       .val = has_ub ? bounds[ub_idx].main : (rational_t){0}},
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

  mpq_QSdump_prob(qsx_prob);
}

bool simplex_check_feasibility_external(simplex_solver_t *solver) {
  if (!solver->tableau_ready)
    return true;

  matrix_t *matrix = &solver->matrix;
  arith_vartable_t *vtbl = &solver->vtbl;
  // ivector_t *leaving_vars;
  row_t *row;
  thvar_t x;
  int32_t r, k;
  uint32_t repeats, loops, bthreshold;
  bool feasible;

  printf("\n\n*** SIMPLEX START ***\n");
  // print_simplex_vars_summary(stdout, solver);
  printf("==== Pivots ====\n");
  printf("%d", solver->stats.num_pivots);
  printf("\n==== Simplex variables ====\n");
  print_simplex_vars(stdout, solver);
  printf("\n==== Tableau ====\n");
  print_simplex_matrix(stdout, solver);
  printf("\n==== Assignment ====\n");
  print_simplex_assignment(stdout, solver);
  printf("\n==== Bounds  ====\n");
  print_simplex_bounds(stdout, solver);
  printf("\n==== Atoms ====\n");
  print_simplex_atoms(stdout, solver);
  printf("\n");

  qsx_start();
  mpq_QSprob qsx_prob = mpq_QScreate_prob(NULL, QS_MIN);

  mpq_QSset_param(qsx_prob, QS_PARAM_SIMPLEX_MAX_ITERATIONS, pivot_threshold);
  mpq_QSset_param(qsx_prob, QS_PARAM_SIMPLEX_DISPLAY, __smt2_globals.verbosity);

  add_cols(solver, qsx_prob);

  for (uint32_t i = 0; i < matrix->ncolumns; i++) {
    // thvar_t x = matrix->column[i];
  }

  // Assign each variable to a row and column variable as it appears in the
  // input
  for (uint32_t i = 0; i < matrix->nrows; i++) {
    int32_t r = i;
    row = matrix->row[r];
  }

  mpq_QSfree_prob(qsx_prob);
  qsx_clear();

  return true;
}
