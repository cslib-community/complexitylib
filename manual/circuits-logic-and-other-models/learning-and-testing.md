# Learning and property testing

The learning development makes a useful distinction between statistical/sample complexity, membership-query complexity and native running time. Its main local algorithms prove the first two. They should not be described as computational PAC learners merely because their sample or query bounds are polynomial or quasi-polynomial. [complexitylib][complexitylib]

## Upstream PAC and local uniform learning

Upstream [ConceptClass](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/MachineLearning/PACLearning/Defs.lean#L121) defines a concept class as a set of functions and a learner as a function from an indexed labelled sample to a hypothesis. Success probabilities and excess error are measured over an explicit family of input/label distributions. It provides deterministic and internally randomized PAC notions and sample-complexity operators. The `R` in `IsRPACLearnerFor` denotes randomized, not realizable; realizability is imposed through the chosen distribution family. A learner is not required to be an encoded algorithm in this definition. [cslib][cslib]

Local [uniformExamples](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/MachineLearning/UniformLearning/Basic.lean#L91) specializes to Boolean functions on a finite cube and independent uniform examples. `uniformError` is the fraction of cube inputs on which the hypothesis differs from the target. `Learns` bounds this error with failure probability delta after a prescribed number of labelled samples. Its bridge to upstream PAC instantiates the uniform realizable family; it does not establish distribution-free learning.

The [low-degree Fourier learner](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/MachineLearning/UniformLearning/LowDegree.lean) estimates low-degree coefficients from examples and thresholds the resulting polynomial. With N retained coefficients, its sample condition is of the form `m >= (4N/epsilon) log(2N/delta)` together with a Fourier-tail assumption. The [AC0 learning theorem](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/MachineLearning/UniformLearning/AC0.lean) combines this learner with Linial–Mansour–Nisan concentration, giving quasi-polynomial sample bounds for the stated bounded-depth/size circuit class. The local exponent is the implementation's quantitative version, with its circuit-depth convention; native Fourier arithmetic and hypothesis-evaluation time are not part of this theorem.

The upstream randomized variant, [IsRPACLearnerFor](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/MachineLearning/PACLearning/Defs.lean#L181), chooses a sample-to-hypothesis learner using an internal probability space and bounds the expected sample-failure probability, with the stated almost-everywhere measurability condition. This is a separate semantic randomization layer from random training examples.

## Membership-query learners

[QueryLearner](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/MachineLearning/UniformLearning/MembershipQuery.lean#L76) takes a random seed to a decision tree. A queried coordinate is itself an input point for the unknown target function, and a leaf is a hypothesis function. `QueriesAtMost` bounds tree depth for every seed. This represents adaptive membership queries directly, while nonadaptive point lists are a specialization.

Uniform random examples can be simulated by querying independently sampled points, with exact distributional correctness. The [Kushilevitz–Mansour development](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/MachineLearning/UniformLearning/KushilevitzMansour.lean) reuses a nonadaptive sample set across stages, with the explicit query bound `m(2n+3)` and a sample schedule depending on spectral norm, error and confidence. Bounded-leaf decision trees supply a concrete learnable class through a spectral-norm bound. These statements charge oracle queries only; they do not bound the time or finite representation needed for all Fourier operations and output hypotheses.

## Property testing as decision trees

The existing BLR local test compiles to a decision tree through `PCP.LocalTest.decisionTree`. [depth_decisionTree_repeatAll_blrTest_le](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/PropertyTesting/Linearity.lean#L52) proves that k independent repetitions use at most 3k queries, accept every parity with probability one and accept a function at uniform relative Hamming distance at least epsilon from every parity with probability at most `(1-epsilon)^k`.

The corresponding [one-sided lower bound](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/PropertyTesting/LinearityLowerBound.lean) shows that a tester of depth at most two that accepts every parity perfectly cannot reject the specified nonlinearity witness with value false at zero. This establishes the three-query boundary under those hypotheses. It is a lower bound for worst-case query depth, not expected queries, and it is formulated for arbitrary randomness support through the tested tree property.

## Exact finite counterexamples

For the circumference-eight circle, import
[`QuarterQCD`](../../Complexity/GameTheory/FacilityLocation/QuarterQCD.lean).
`weights` computes the squared opposite arcs with floor four and `cost` normalizes
by their sum. Coordinates must be canonical, in $[0,8)$; the three reports are in
increasing order. `quarterQCD_counterexample` gives an improving first-agent report
from $(0,3,4)$ to $(1,3,4)$ and ratio $137/116>7/6$. `witness_optimum` proves the
optimum is four against every real canonical facility location. The restricted
ordered-report strategyproofness predicate is already false. This does not provide
the paper's general graph mechanism search. See the
[complete checked client](../../ComplexityTests/PaperEndpoints/QuarterQCD.lean).

For the six rational least-squares observations, import
[`NonRange`](../../Complexity/Statistics/LeastSquares/NonRange.lean).
`scatter` is centered cross-scatter, $\sum xy-(\sum x)(\sum y)/|S|$.
`nonrange_optimum` identifies the unique minimizing four-set and proves that no
real plane cuts it out on the saddle lift $(x,y,xy)$. The rational oriented-volume
certificates cover the fifteen four-lift determinants. Indices are zero based;
`retained` is the source's points 2, 3, 5 and 6. This finite obstruction does not
supply an integral-stability algorithm. The
[checked client](../../ComplexityTests/PaperEndpoints/NonRange.lean) also constructs
an empty lifted-plane range, distinguishing the range notion from the failed optimum.

## Weighted least-squares monotonicity and rounding

Import [`Monotone`](../../Complexity/Statistics/LeastSquares/Monotone.lean) and open
`Cslib.LeastSquares`. A base Gram matrix `G` and normal-equation right-hand side `g`
represent fixed observations. `rankOneEstimate G g x y a` is the actual estimate
$(G+a x x^\top)^{-1}(g+a x y)$ for one added observation.
Supply `hG : G.PosDef` and a nonnegative weight to `rankOneEstimate_eq` for its
Sherman–Morrison formula. `rankOneEstimate_monotone_or_antitone` covers every linear
target `e`; the direction depends on the data and target.

For a finite set of observations `s`, `weightedEstimate` adds their contributions
to the fixed base. `exists_round_weights` rounds weights in $[0,1]$ to endpoints
without increasing the target. `exists_round_weights_loss_lt` bounds lost mass
strictly below any positive `k` bounding the number of genuinely fractional weights.
Both require the fixed base itself to be positive definite, even after all variable
observations are removed. The [checked client](../../ComplexityTests/PaperEndpoints/MonotoneRounding.lean)
includes different endpoint estimates and two observations with opposite responses.

Import [`Backbone`](../../Complexity/Statistics/LeastSquares/Backbone.lean) when the
fixed observations have not been specified separately. `GeneralPosition x` means
that every set of $d$ design rows is linearly independent. Given weights in $[0,1]$,
retained mass at least $2d$, and at most $d$ fractional coordinates,
`exists_round_sparse` derives a positive definite backbone from the fully retained
observations and rounds the entire design. It preserves observations outside the
index set, does not increase any chosen linear target, loses strictly less than
$d$ retained mass, and proves the rounded Gram matrix positive definite.
The [checked client](../../ComplexityTests/PaperEndpoints/Submission1326.lean)
starts with three scalar rows and weights $(1,1,1/2)$; no backbone is supplied.

Import [`Stability`](../../Complexity/Statistics/LeastSquares/Stability.lean) for
the complete mathematical rounding assembly. `Feasible x y e θ w` requires box
weights, a positive definite Gram matrix and the linear inequality target.
`fractionalStability` is the infimum of deleted mass over these weights;
`integralStability` is the natural minimum over feasible retained subsets. Its
empty-set value is zero, so use the theorems' feasibility hypotheses rather than
interpreting that value as an infeasibility certificate.

`exists_sparse_weights` (Lemma 3.2, through
[`Sparsification`](../../Complexity/Statistics/LeastSquares/Sparsification.lean))
starts with arbitrary box weights of mass above $d-1$. It preserves the fitted
coefficient vector, does not decrease mass and leaves at most $d$ fractional
coordinates. It maximizes mass subject to the residual normal equations and
chooses an extreme point, using the reusable finite-dimensional box-fiber API
in [`Box`](../../Complexity/Foundations/LinearAlgebra/Box.lean).
`exists_round_subset` starts with arbitrary feasible weights of mass at least
$2d$ and produces an actual feasible retained subset with loss strictly below $d$.
No sparse-input or supplied-backbone premise remains.

`fractionalStability_attained_of_gap` proves attainment whenever feasibility is
nonempty and $n-s_{\rm frac}>d-1$. `fractionalStability_attained_sparse` also
provides a sparse optimizer. `stability_bounds` proves
$s_{\rm frac}\le s_{\rm int}<s_{\rm frac}+d$ under GP and the $2d$ feasible-mass
hypothesis. `stability_ceiling_bounds` gives the interval of $d$ consecutive
integers starting at $\lceil s_{\rm frac}\rceil$; the dimension-one and dimension-two
specializations are `integralStability_eq_ceil_of_card_eq_one` and
`integralStability_eq_ceil_or_succ`. These conclusions allow arbitrary linear
targets and do not require an intercept or a positive original target value.
The [complete checked client](../../ComplexityTests/PaperEndpoints/FullRounding1326.lean)
has six nonzero scalar rows, four half weights and a violated full-data target;
it exercises sparsification, subset rounding and the dimension-one equality.

These are the mathematical statements of Lemmas 3.1–3.2, Theorem 3.3 and
Corollary 3.4 (PDF pp. 6–7). For execution, import
[`RoundingExecution`](../../Complexity/Statistics/LeastSquares/RoundingExecution.lean)
and open `Cslib.LeastSquares.RoundingExecution`. `execute lp x y w e` starts
with the actual input weights; `VertexLP lp` requires a vertex-returning optimum
of a box-constrained linear program. It does **not** assume sparse weights, a
preserved fit or a rounding conclusion. `sparsify_correct` derives these facts.
`execute_correct` and `execute_retained` certify the computed integral weights,
actual retained subset, feasibility, strict loss below $d$, and final inverse and
response caches, under GP, input feasibility and retained mass at least $2d$.
The scalar field is polymorphic, so the arithmetic code executes over rationals;
the correctness statements use the real inverse-matrix semantics.

The operation contract counts one initial Cramer solve, one external LP call,
one determinant/adjugate inverse initialization, at most $d$ processed
coordinates and at most $2d$ signed rank-one calls. `execute_calls`,
`run_coordinates` and `run_rankChanges` derive the counts from the stages and
executed branches. The initial solve computes $\beta(w)$ before constructing the
LP and is charged separately. The generic matrix kernels live in
[`Matrix.RankOne`](../../Complexity/Foundations/LinearAlgebra/Matrix/RankOne.lean).
This is a coarse operation contract: scalar arithmetic, comparisons, allocation,
finite enumeration and retained-set materialization are outside that counter.
Determinant-based inversion has no cubic-time certificate. Supply a standard LP
implementation with vertex recovery; an arbitrary interior optimizer does not
satisfy the contract. No rational bit-complexity or Lean compiler-speed bound
follows from these primitive counts.

For Corollary 3.4(iii), import
[`ExternalSolver`](../../Complexity/Statistics/LeastSquares/ExternalSolver.lean)
and open `Cslib.LeastSquares.ExternalSolver`. `NormalOracle` is the external
Moitra–Rohatgi equality-target normal-equation decision contract, allowing
singular solutions, for a zero target in a specified coefficient.
[`EqualityTarget`](../../Complexity/Statistics/LeastSquares/EqualityTarget.lean)
proves that these decisions coincide with the local nonsingular inequality
thresholds in the queried regime; strict full-data target violation is required
here. `bracket_start` proves that the executed `search` returns the ceiling of
fractional stability, and `integral_bracket` gives the $d$ consecutive candidate
integers. `bracket_time` composes an external $C n^{c d^3}$ decision bound into
$2(C+1)n^{(c+1)d^3}$. The external solver and its cost are explicit assumptions;
the adapter assumes neither a fractional optimum nor an integral bracket.
The cited endpoint is a threshold decision procedure. This API computes the
integer bracket without claiming to return an arbitrary exact real value of
fractional stability.

For a general affine target $e^\top\beta\le\theta$, import
[`AffinePreprocessing`](../../Complexity/Statistics/LeastSquares/AffinePreprocessing.lean)
and open `Cslib.LeastSquares.AffineTarget`. `solve` selects a nonzero target
coordinate, materializes all transformed rows and responses in original order,
and calls your external zero-coefficient solver on that actual table.
`solve_correct` returns the ceiling of the original fractional stability;
`solve_integral_bracket` returns its dimension-many integral bracket. Supply
`NormalOracle` correctness for your solver on the transformed observations,
GP, a feasible input of mass at least $2d$, and strict full-data target violation.
The last two conditions exclude $e=0$; the program returns `none` for that case.

[`AffineTarget`](../../Complexity/Statistics/LeastSquares/AffineTarget.lean)
proves the change $\beta=b_0+B\gamma$ with $e^\top\beta-\theta=\gamma_j$.
Residuals and singular-inclusive normal equations agree, and the weighted Grams
are related by $G'=B^\top G B$. GP, positive definiteness, inequality feasibility,
fractional stability and integral stability are preserved. The weights and
original row indices do not change. This needs no intercept column and permits
negative and nonfirst pivots. `weightedEstimate_eq_of_normal` in
[`Sparsification`](../../Complexity/Statistics/LeastSquares/Sparsification.lean)
identifies any normal-equation solution with the inverse fit under positive
definiteness alone; use it instead of reconstructing a GP/mass argument when
positive definiteness is already known.

`preprocess_real_ret` links actual list output to the semantic change.
`preprocessing_linear` bounds pivot selection and full table materialization
by $12nd$ operations for positive $n,d$. The model charges each scalar arithmetic
operation and zero comparison once, and charges list cons/termination; vector
reads and finite-index views are free. Rational programs execute with the same
counters, but these are exact-real arithmetic bounds, not rational bit time or
Lean compiler runtime. `solve_time` includes this preprocessing cost and the
existing external scan bound $2(C+1)n^{(c+1)d^3}$.

From the repository root, run
`scripts/build.sh ComplexityTests.PaperEndpoints.AffineTarget1326`
to check the [complete affine client](../../ComplexityTests/PaperEndpoints/AffineTarget1326.lean).
It checks a negative nonfirst pivot, a materialized two-row rational table and
its exact counter, zero-target rejection, singular normal-equation feasibility,
and a concrete inhabited external oracle with nonzero affine threshold.

The exact optimum-output clause remains separate. MR23 arXiv v2 Theorem 1.2
(PDF p. 3) and Theorem A.4 (pp. 13–14) state threshold decisions; its real model
is specified in footnote 3 (p. 7). Integer queries determine a ceiling, and
finite bisection does not produce an arbitrary real boundary exactly. For
rational or algebraic data, an exact-output extension needs a representation
such as a defining polynomial with isolating interval or Thom data, parameterized
elimination/optimization, and an output-cost theorem. For arbitrary real data,
it must specify representation relative to the input field or stronger
real-algebraic primitives. These are remaining proof obligations; the adapter
does not assume an exact optimum or assert that exact output is impossible.

From the repository root, run
`scripts/build.sh ComplexityTests.PaperEndpoints.RoundingExecution`
to check the [complete client](../../ComplexityTests/PaperEndpoints/RoundingExecution.lean).
It checks an input with more fractional coordinates than the dimension, the
constructed residual equations, both actual rational rounding branches, inverse
and response caches, exact counters, and threshold-search boundary cases.

The full empirical certificate inventory in Section 6 remains open. A fresh
release-PDF inspection on 2026-11-06 found no embedded attachments, despite
Appendix B's attachment claim; the release exposes only the PDF for this paper.
The named `certlib.py`, `fe_cert.py`, drivers and `grid.jsonl`, `fe.jsonl`,
`scale.jsonl`, `small.jsonl` were therefore unavailable. Reproduction needs the
archive, exact source data and preprocessing, per-regression identities, exact
LP dual interval bounds or groupwise lower-envelope certificates, retained row
identifiers and exact successful cross-scatter/positive-scatter checks for all
640 cross-sections and 44 panels. The third-party CFPS and housing files are not
redistributed according to Appendix B. Numerical summaries alone cannot supply
these certificates or repair Table 1's missing nondegeneracy evidence. See
[issue 2527](https://github.com/cslib-community/complexitylib/issues/2527) for scope.

## Exact fixed-effects first crossings

Import [`FixedEffects`](../../Complexity/Statistics/LeastSquares/FixedEffects.lean)
and open `Cslib.LeastSquares.FixedEffects`. Supply a list of groups, each a list of
rational `(x, y)` observations. `audit groups` computes `some plan`; each `Choice`
records the actual retained sublist and its deletion count. `mem_choices` and
`deletion_accounting` connect these witnesses to removal of input observations,
including repeated values. `audit_exists` also covers empty inputs. Empty and
singleton retained groups contribute zero scatter.

The slope is the sum of within-group cross-scatters divided by the sum of
within-group regressor scatters. Group means are recomputed after each removal;
`dummy_normal_equation` and `pooled_normal_equation` verify the refitted dummy
and pooled regressor normal equations. `Feasible` requires a positive denominator
and a nonpositive slope. A zero denominator is singular, even though Lean's total
division assigns a value to its slope expression.

`audit_lower_bound` proves that the first crossing's deletion count bounds every
feasible plan from below. `audit_optimal_of_nondegenerate` proves optimality if a
numerator minimizer at that cost has positive denominator. The algorithm minimizes
cross-scatter and then maximizes regressor scatter, so the returned minimizer is
also nonsingular under that hypothesis. `audit_optimal_of_negative_numerator`
derives nondegeneracy from a strict negative crossing. The
[complete checked client](../../ComplexityTests/PaperEndpoints/FixedEffects1326.lean)
computes a positive-slope example, proves universal optimality, checks a two-group
convolution and distinguishes singular and nonsingular zero crossings. Its
`import all` directives load implementation bodies for exact kernel computation;
ordinary imports suffice to apply the public theorems.

For the resource-certified implementation, import
[`FixedEffects.Resources`](../../Complexity/Statistics/LeastSquares/FixedEffects/Resources.lean)
and open `Cslib.LeastSquares.FixedEffects.Resources`. From the repository root,
check its [complete client](../../ComplexityTests/PaperEndpoints/FixedEffectsResources1326.lean)
with `scripts/build.sh ComplexityTests.PaperEndpoints.FixedEffectsResources1326`.
`run groups` returns a time-monad computation. Its `.ret` is `some r`, where
`r.hit.index` is the first crossing, `r.hit.entry.plan` is the actual removal plan,
and `r.retained` contains the copied retained observations. Its `.time` records
the counted execution. `run_exists` proves termination and `run_spec` proves
validity, exact deletion count, first-crossing minimality and score minimality.
The existing `audit` API and its checked clients remain available.

`groupCurve` computes sufficient statistics once per retained sublist and caches
one lexicographic minimum per group deletion count. The shared-array convolution
in [`FiniteMinPlus.Cached`](../../Complexity/Foundations/Optimization/FiniteMinPlus/Cached.lean)
compares cached scores and shares persistent witness tails; `table_correct`
proves refinement of the existing reference recurrence, including ties and
unreachable costs. The pipeline precomputes curves once, doubles the cap from
one until it finds a crossing, then copies the retained observations. The final
cap can exceed the sample size by less than a factor two. It is not clipped.

`run_time_of_nondegenerate` proves the explicit bound
$300(n2^T+nK)$ on this pipeline, including input measurement and recovery, when
input groups are nonempty, each has size at most $T$, the original numerator is
positive, and the source's first-crossing nondegeneracy condition holds. It also
proves that $K$ is the optimal deletion count. `run_time` compares the work
against any positive-cost feasible removal plan; `run_isBigO` gives the bound
along any family and filter of admissible inputs. These results derive work
from the executable loops and do not take a runtime guarantee as a hypothesis.
The client checks exact work counts, a cap-one failure followed by cap-two
success, and materialized recovery. Singular crossings remain possible without
nondegeneracy.

This is an arithmetic RAM count: rational arithmetic, natural indexing,
constant-size record/list operations, array accesses, and score-pair comparisons
have unit cost. Expanding a pair operation into rational scalar operations
changes the constant by at most three. Rational bit time and Lean allocator or
compiler performance are separate. Inputs are already grouped; sorting raw
labeled observations is not included. The functions handle empty groups, but
the advertised $n$-only bound excludes them: reading arbitrary empty groups
requires a group-count term. Empty input has ten counted initialization/scan
operations. The subset preprocessing uses $O(n_g2^{n_g})$ work per group, which
sums to $O(n2^T)$; the sharper per-group Gray-code claim is not asserted.
The scalar and fixed-column adapters and fixed-size relaxation are described
below. The rounding execution and conditional external-solver adapter above
use different models; complete empirical certificates remain open. This
fixed-effects resource endpoint does not complete the paper.

## Real matrix semantics and general geometry

Import [`FixedEffects.MatrixBridge`](../../Complexity/Statistics/LeastSquares/FixedEffects/MatrixBridge.lean)
for the matrix interpretation of the computed fixed-effects plan. `Active plan`
indexes the nonempty retained groups and `Rows plan g` indexes their actual
observations. The real design has one regressor column (`none`) and one dummy
column (`some g`) per active group. `real_gram_posDef_iff` derives positive
definiteness exactly from the algorithm's positive denominator;
`real_inverse_slope` identifies the actual inverse-matrix coefficient with the
computed rational slope. `matrix_feasible_iff` includes both nonsingularity and
the sign target. These are proved from the matrix normal equations, rather than
assuming the within-estimator formula or full rank.

`Resources.run_matrix_optimal` connects the executed pipeline to
`refittedIntegralStability` and its $300(n2^T+nK)$ arithmetic-operation bound.
This stability infimum permits vanished groups and removes their dummies, as the
paper requires. It is a separate model from the fixed-column
`LeastSquares.integralStability`: retaining a vanished group's zero dummy makes
the latter Gram matrix singular. `MatrixModel.not_posDef_of_empty_group` proves
that obstruction. The original-index adapter below derives equality of optimum
values when every input group is nonempty and a feasible plan exists; individual
feasible subsets can still differ. The matrix model accepts arbitrary real observations; the executed
pipeline and cast bridge take rational observations. Empty feasibility has
natural infimum zero, so use the optimality theorem, which supplies feasibility,
instead of interpreting the infimum alone.

Import [`FractionalGeometry`](../../Complexity/Statistics/LeastSquares/FractionalGeometry.lean)
and open `Cslib.LeastSquares.Simple` for Proposition 5.3's optimizer geometry.
`MassOptimal x y w` means a global maximum of retained mass among all feasible
real box weights, with positive mass and regressor scatter. Given positive
full-data cross-scatter, `MassOptimal.self_centered` proves zero cross-scatter
and a threshold for `(x_i - mean_x)(y_i - mean_y)` at the optimizer's own
centroid. Fractional coordinates lie on that threshold.
`MassOptimal.fractional_pair` proves the weak anti-monotone inequality for any
two fractional coordinates. These conclusions hold for every attained optimizer;
this module separates their geometry from existence. Import
[`SimpleMatrix`](../../Complexity/Statistics/LeastSquares/SimpleMatrix.lean)
to discharge existence: `design x` is the actual two-column design in
slope/intercept order, `signFeasible_iff` identifies scalar and generic
inverse-matrix feasibility, and `design_generalPosition` derives the design-row
hypothesis from distinct regressor values. `exists_sparse_massOptimal` starts
from any feasible scalar weights of mass greater than one and returns a global
optimizer with at most two fractional coordinates and the attained generic
fractional-stability value. `exists_sparse_self_centered` combines this with
Proposition 5.3 when the input mass is at least four and the full-data
cross-scatter is positive. `exists_round_sign_subset` starts from arbitrary
feasible scalar weights of mass at least four and returns a nonsingular subset
with mass loss strictly below two. These are mathematical existence results;
they do not certify execution or a running time for an LP solver.

From the repository root, check the
[complete matrix and fractional client](../../ComplexityTests/PaperEndpoints/LeastSquaresGeometry1326.lean)
with `scripts/build.sh ComplexityTests.PaperEndpoints.LeastSquaresGeometry1326`.
It proves global optimality of a nonintegral three-point weighting, checks the
vanished-group design's inverse slope $-1$, and applies the matrix resource
theorem to an actually executed audit.

Import [`RadonGeometry`](../../Complexity/Statistics/LeastSquares/RadonGeometry.lean)
and open `Cslib.LeastSquares.Geometry` for Theorem 5.7. `UniqueMinimum` compares
actual subsets of the same cardinality, without a sign assumption.
`LiftedGeneralPosition` requires independence of each at-most-four homogeneous
saddle lifts `(xy,x,y,1)`; `liftedGeneralPosition_iff_four` reduces this to
four-element subsets when there are at least four observations.
`isRange_iff_sublevel` equates strict separation with the source's strict conic
sublevel convention, including omitted boundary points. All plane coefficients
are real.

`UniqueMinimum.local_witness` returns a `FiveWitness` with five distinct original
indices and normalized positive weights on both sides of a Radon partition.
Exactly two or three witness observations are omitted, and whichever side has
two points is strictly anti-monotone. It also returns those omitted observations
as a set `D`: the optimum stays unique among all same-size subsets of `S ∪ D`
and no real plane selects it there. `UniqueMinimum.witness_exclusion` is the
averaged-swap argument forcing negative cross-scatter in the common convex
combination. The proof extracts the witness using Mathlib separation and
Carathéodory, rather than assuming colored nonseparation or a supplied witness.

Check the [complete Radon client](../../ComplexityTests/PaperEndpoints/LeastSquaresRadon1326.lean)
with `scripts/build.sh ComplexityTests.PaperEndpoints.LeastSquaresRadon1326`.
It transfers the exact six-point construction to the general real definitions,
checks all 57 subsets of size at most four for homogeneous independence, applies
the localization theorem, and checks its explicit omitted pair's product
$-961/625$. Theorem 5.7 is a general statement; that finite test only demonstrates
its hypotheses on a concrete instance.

Import [`FixedSize`](../../Complexity/Statistics/LeastSquares/FixedSize.lean)
for Proposition 5.2. `setPolytope p m` is the actual convex hull of the saddle
sums of original subsets of size $m$, and `setPolytope_eq_image` proves it equals
the image of all box weights of mass $m$. `PolytopeMinimum` compares every point
of that convex hull. For $2\le m<n$, `fixedSize_relaxation` derives attainment
and the full dichotomy under lifted general position: a lower hyperbolic-range
subset attains the relaxation, or every minimizer is an interior interpolation
of two distinct lower subset sums differing by one strictly anti-monotone swap.
`IsLowerSwap` supplies the actual supporting-plane coefficients: its common
retained observations are strictly below the plane, its exchanged pair is on
it, and every other observation is strictly above it. Thus its exposed face
is the swap segment. `IsLowerRange` has saddle coefficient one and is equivalent
to a strict axis-parallel hyperbolic sublevel set by `isLowerRange_iff`.
This relaxation deliberately includes singular designs and imposes no sign
condition; do not use its minima as feasible slope reversals without checking
positive regressor scatter separately.

For fixed columns, import
[`FixedEffects.FixedColumns`](../../Complexity/Statistics/LeastSquares/FixedEffects/FixedColumns.lean)
and open `Cslib.LeastSquares.FixedEffects.MatrixModel`. A retained subset of
`Sigma I` records original row positions, including repeated data. `Kept s g`
restricts each original group to its surviving rows. `feasible_iff_preservesGroups`
characterizes generic fixed-column feasibility by group preservation, positive
pooled within-scatter and nonpositive pooled cross-scatter. Group preservation
is derived from positive definiteness, and `preservesGroups_of_deletions_lt`
derives it whenever fewer rows are deleted than any group contains.
`subsetStability` allows groups to vanish and counts deletions by original row
positions. The earlier `integralStability_eq_subsetStability` gives a sufficient
small-deletion criterion for arbitrary indexed real data.

For the actual grouped rational input and computed output, import
[`FixedEffects.Indexed`](../../Complexity/Statistics/LeastSquares/FixedEffects/Indexed.lean)
and use `Cslib.LeastSquares.FixedEffects.Indexed`. `Corresponds gs plan s`
identifies retained occurrences with distinct original row positions, even when
values repeat. `subset_of_valid` and `plan_of_subset` prove both directions;
`Corresponds.deletions`, `.cross`, `.scatter` and `.feasible_iff` preserve cost and
regression semantics. `refittedIntegralStability_eq_subsetStability` identifies
the two refitted infima, including their zero convention when infeasible.

An optimal feasible plan cannot erase an originally nonempty group: retaining
one observation in that group changes neither within-group scatter and saves a
deletion. `Corresponds.preservesGroups_of_optimal` proves this fact.
`integralStability_eq_refittedIntegralStability` therefore needs nonempty input
groups and an existing feasible plan, but no comparison with group sizes.
`run_indexed_optimal` links the actual returned observations to an original-index
subset, proves fixed-column inverse feasibility and optimality, and retains the
$300(n2^T+nK)$ arithmetic-RAM bound for the executed pipeline. The positional
witness is a mathematical refinement; this theorem does not charge a separate
algorithm for materializing row identifiers.

From the repository root, run
`scripts/build.sh ComplexityTests.PaperEndpoints.FixedEffectsIndexed`
to check the [complete indexed client](../../ComplexityTests/PaperEndpoints/FixedEffectsIndexed.lean).
Its computed optimum deletes one row while preserving a singleton group, so
the earlier strict group-size bound cannot prove this instance. It also checks
duplicate observations and refitted equality with an empty original group.

From the repository root, run
`scripts/build.sh ComplexityTests.PaperEndpoints.LeastSquaresRelaxation`
to check the [complete client](../../ComplexityTests/PaperEndpoints/LeastSquaresRelaxation.lean).
It derives sparse scalar attainment and rounding on the strict-gap instance,
rejects a constant regressor, forces the fractional-edge branch on the exact
six-point non-range instance, and checks both a feasible grouped inverse fit
and failure after erasing an entire group. The existing matrix/Radon clients
above retain the checked source-instance construction and executed resource
bounds.

## Exact equality-target regression hardness

Import
[`RegressionEquality`](../../Complexity/Computability/Complexity/Problems/RegressionEquality.lean)
and open `Cslib.LeastSquares.EqualityDeletion`. `BinaryProblem` asks whether an
actual sublist of explicitly supplied binary-regressor/integer-response rows
has a nonsingular two-column OLS design and an exactly-zero inverse-matrix
slope, within an at-most deletion budget. `binaryEncoding` uses a regressor bit,
a signed binary response and a binary nonnegative budget. `binary_npHard` is
Theorem 3.7; general position is deliberately absent.

`expand (fromSubsetSum a)` is the actual polynomial-time many-one map from the
existing binary `SubsetSum`: one $(0,0)$ row, positive responses at regressor
one, a negative target and a zero response. Zero source entries are filtered;
a zero target uses a fixed yes instance. `computableInPolyTime_reduction` and
`reduction_mem_iff` prove resources and both correctness directions without
assuming a desired map or hardness conclusion. `ExactFit` uses the actual real
matrix inverse, while `exactFit_iff` derives its scalar characterization.
The only regressor-zero row must survive because an all-one regressor is
singular. A negative slope is rejected unless it is exactly zero.

From the repository root, run
`scripts/build.sh ComplexityTests.PaperEndpoints.RegressionEquality`
to check the [complete hardness client](../../ComplexityTests/PaperEndpoints/RegressionEquality.lean).
It includes positive and negative instances, duplicate values, zero entries,
zero/positive targets on empty lists and a singular remainder. This is weak
NP-hardness for binary magnitudes, not a strong-hardness or general-position
claim. The rounding execution and conditional external-solver adapter are
described above. Full empirical certificates remain open; these endpoints
do not complete the paper.

## Exact least-squares stability gaps

For exact simple regression, import
[`Rational`](../../Complexity/Statistics/LeastSquares/Rational.lean) and open
`Cslib.LeastSquares.Simple`. `crossNumerator` and `xNumerator` are retained mass
times centered cross-scatter and regressor scatter. `slope` is their ratio;
`intercept` and `normal_equations` include the fitted intercept. Require positive
regressor scatter rather than trusting Lean's total division on singular data.
`realVector` and the four cast lemmas transfer exact rational certificates to
real-valued mass, scatter and slope. `keep s` gives integral retention weights.
The [checked client](../../ComplexityTests/PaperEndpoints/Submission1326.lean)
checks slope two/intercept one and separately rejects a constant regressor.

[`SharpGap`](../../Complexity/Statistics/LeastSquares/SharpGap.lean), `sharp_gap`,
proves Proposition 3.6 (PDF pp. 7–8): the ten-point instance has positive initial
slope, real fractional stability below $0.98$, and integral stability exactly two.
`fractionalStability` is an infimum over all feasible **real** weights, with
nonsingularity and an inequality target. The explicit fractional witness deletes
$4899/5000=0.9798$ mass; the proof does not use floating-point approximations.

[`RangeAudit`](../../Complexity/Statistics/LeastSquares/RangeAudit.lean),
`range_audit_gap`, proves Theorem 5.5 (PDF p. 13): the twelve-point instance has
integral stability two and best lifted-plane-range stability three. General
position and lifted general position are checked exactly. The nonseparation
argument covers every real plane; an explicit integer-coefficient plane witnesses
the feasible three-deletion range. `feasible_iff_real` connects the exact scatter
test with nonsingular real OLS. The general geometry, equality-target hardness,
rounding execution and conditional external-solver adapter are described above.
The full empirical certificate inventory remains open; see
[issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).

## Known Limitations

The examples use semantic hypotheses and real probability/analysis. These results provide formal sample/query guarantees and formal bridges to PAC/query models. Claims of polynomial native training time or succinct executable output hypotheses require separate resource theorems. Keep these limitations in view when choosing a learning model: the notions of efficiency differ.

[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
