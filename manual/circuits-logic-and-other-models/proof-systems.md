# Propositional models and proof complexity

cslib-frontier represents propositional syntax as concrete finite data and distinguishes satisfiability, derivability and resource-bounded proof objects. This supports reductions, model counting and lower bounds without identifying a proof's length with the time needed to find it. [cslib-frontier][complexitylib]

## CNF, CSP and quantified formulas

[CNF](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CNF.lean#L67) is a list of clauses, each a list of signed variables. Ordering and repeated occurrences are retained. Several useful sizes coexist: clause count, literal-occurrence count, distinct-variable support, maximum clause width and serialized bit length. In a fixed-width SAT theorem the stated width convention must be checked; in resolution, width is explicitly the number of distinct literals.

To certify a program that evaluates a formula, import
`CslibFrontier.Logics.Propositional.CNF.PolyTime`. Its `fun_prop` rules
`Literal.computableInPolyTime_eval`, `Clause.computableInPolyTime_eval` and
`CNF.computableInPolyTime_eval` handle evaluation under an assignment `σ a`. They need a
certificate for `fun p => σ p.1 p.2` on the pair of the input and a variable. Clients no longer need
to pass `CNF.eval`, `Clause.eval` or `Literal.eval` to `fun_prop`. If the assignment is a named
definition whose certificate is stated for a differently nested input, unfold that definition
instead, as in `fun_prop [assignment]`. The [checked examples](../../CslibFrontierTests/CNFPolyTime.lean)
include an assignment without a certificate, which `fun_prop` rejects.

The [ClauseSet](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/ClauseSet/Basic.lean#L55) representation instead uses finite sets of finite sets of literals, so order and repetitions disappear. Its occurrence measure counts clauses mentioning a variable. List/set conversions preserve satisfying assignments but need separate size/occurrence lemmas. This is the representation used by the sparsification development.

For ordinary disjunction with exactly three distinct variables per clause, import
`CslibFrontier.Computability.Complexity.Problems.EUThreeSAT` and use `EUThreeSAT_npComplete`.
The bounded-occurrence variant behaves differently: `EUThreeSATThree.mem_P` checks syntax,
because every valid formula is satisfiable. For not-all-equal semantics, import
`CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT`. Here `CNF.evalNAE` requires a true
and a false literal in each clause. **NAE EU3SAT** has exactly three distinct variables per clause
and is proved NP-complete by `NAEEUThreeSAT_npComplete`. **NAE3SAT** permits width at most three;
**NAE3SAT-3** also bounds total occurrences per variable by three, and is proved NP-complete by
`NAEThreeSATThree_npComplete`. The latter permits binary clauses. See the
[checked examples](../../CslibFrontierTests/NAEAndEUThreeSAT.lean) for the complete import context,
satisfiable and unsatisfiable instances, and applications of these endpoints. Run
`scripts/build.sh CslibFrontierTests.NAEAndEUThreeSAT` from the repository root to check them;
successful compilation confirms the displayed theorem types and examples.

For maximum 2-satisfiability, import `CslibFrontier.Computability.Complexity.Problems.MaxTwoSAT` and
use `MaxTwoSAT_npComplete`. An instance `⟨φ, K⟩ : MaxTwoSATInstance` is encoded by `encMaxTwoSAT`,
so the target `K` is binary. Every clause has at most two literals, unit clauses included, and
clauses are counted with multiplicity: `⟨φ, K⟩ ∈ MaxTwoSAT` when some assignment satisfies at least
`K` entries of the list `φ`. The [checked examples](../../CslibFrontierTests/MaxTwoSAT.lean) cover the
Garey–Johnson–Stockmeyer gadget table, an unsatisfiable 2-CNF formula that is a yes-instance for a
smaller target, and the reduction on satisfiable and unsatisfiable inputs; check them with
`scripts/build.sh CslibFrontierTests.MaxTwoSAT`.

For sparse exact `k`-CNFs, import `CslibFrontier.Logics.Propositional.CNF.Moser.Probability`.
Formulas are `φ : CNF (Fin n)` on the variables `Fin n`, with `m = φ.length` clauses.
`CNF.IsExactDistinct k` requires exactly `k` literals over distinct variables in every clause, and
`Moser.degree φ i` counts the other clause indices `j ≠ i` whose clause shares a variable with
clause `i`, so a duplicated clause counts separately.
Moser's resampling algorithm is a step function `Moser.step` reading an explicit tape
`ℕ → Bool`, run with a budget of resamplings. Under `3 ≤ k` and `degree φ i < 2 ^ (k - 3)`,
`Moser.satisfiable_of_degree_lt` proves satisfiability by the entropy-compression count of
Fortnow's exposition. On the fair-coin tape `Cslib.BitString.coinFlips`,
`Moser.ae_exists_eval_final` says the run almost surely stops with a satisfying assignment, and
`Moser.lintegral_resamplings_le` bounds the expected number of resamplings by `m + 2`, the
constant of this encoding. These count resamplings, not machine time. The existential Local Lemma
for the same formulas is `CNF.IsExactDistinct.satisfiable_of_exp_mul_le` in
`CslibFrontier.Logics.Propositional.CNF.LocalLemma`: `Moser.degree φ i ≤ d` for every clause and
`Real.exp 1 * (d + 1) ≤ 2 ^ k` give satisfiability, with no algorithm. Its constant is better, but
it does not say how to find the assignment. Fortnow's Kolmogorov-complexity form of the
compression argument is in `CslibFrontier.Logics.Propositional.CNF.Moser.Kolmogorov`. There the
complexity is `ecomplexity` for the explicit decoder `Moser.descriptionMethod φ k L`, not for a
universal machine. Under `3 ≤ k`, `CNF.IsExactDistinct k φ` and `degree φ i < 2 ^ (k - 3)`,
`Moser.not_exhausts_of_length_sub_le_ecomplexity` shows that a tape word `y` of length `n + t k`
whose complexity for `Moser.descriptionMethod φ k (k - 3)` is at least `n + t k - c` does not use
up a budget of `t > m + c` resamplings. The
[checked examples](../../CslibFrontierTests/Moser.lean) include a concrete run, its log, the
recovered tape and its description, and a formula where only the existential bound applies;
check them with `scripts/build.sh CslibFrontierTests.Moser`.

The general Moser–Tardos theorem for the variable form of the Local Lemma is in
`CslibFrontier.Probability.MoserTardos` [mosertardos10]. The setting is finitely many independent
variables `σ v ∼ μ v` and finitely many measurable events `A i`, each depending (in Mathlib's
`DependsOn` sense) only on the variables in a finite set `vbl i`. The algorithm's randomness is
the table `MoserTardos.table μ` of independent samples `T (v, n)`, where `T (v, n)` is the value
of `v` after its `n`-th resampling. A selection rule `sel T w : Option ι` picks the next event
after the log `w`. It may depend on the whole table, and it is *valid* when it only picks events
that occur. Assume `x i ∈ [0, 1)` and `Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)`, where `Γ i`
contains every other event sharing a variable with `A i`. Under this hypothesis, Theorem 1.2 of
the paper is `MoserTardos.lintegral_resamplings_le`: for every valid rule the expected number of
resamplings of `A i` is at most `x i / (1 - x i)`. The rule need not be measurable, so this `∫⁻`
is a lower integral. `exists_measurable_ge_resamplings` closes the gap: one measurable function
with the same bound dominates the count under every valid rule, so the bound also holds for the
outer expectation. The total over all events is `lintegral_sum_resamplings_le`. Almost sure
termination is `ae_exists_run_eq_none`. `ae_exists_forall_notMem_run` says that a valid rule
that stops only when no event occurs almost surely reaches an assignment avoiding every event;
`ae_exists_forall_notMem_run_greedy` is the greedy case. The existential corollary is
`exists_forall_notMem`. The witness trees of the proof are recorded as finite sets of
`(label, depth)` pairs in `CslibFrontier.Probability.MoserTardos.Witness`. Lemma 2.1 is
`proper_witness`, the coupling `check_witness`, `measure_check_eq_prod` and, combined,
`table_witness_le`. Here `Proper` is the level independence proved inside Lemma 2.1(i), which
implies the paper's properness. The paper's Galton–Watson counting is replaced by a depth
induction, `sum_prod_shapes_le`; relation-parameterized variants `witnessRel`, `ProperRel` and
`sum_prod_shapesRel_le` support the lopsided extension.

Symmetric weights `Real.exp 1 * q * (d + 1) ≤ 1` (`MoserTardos.exists_weights_of_symmetric`) and
`PMF.pi` transport bridges live in `CslibFrontier.Probability.MoserTardos.Symmetric`. They give
`lintegral_resamplings_le_symmetric` (`1 / d` for `1 ≤ d`), `lintegral_resamplings_le_symmetric_zero`
(`q / (1 - q)` for `d = 0`), `lintegral_sum_resamplings_le_symmetric`,
`ae_exists_forall_notMem_run_symmetric` and `exists_forall_notMem_symmetric`, together with
`toReal_toOuterMeasure_pi_eq_measureReal`, `lintegral_resamplings_le_pmfPi`,
`lintegral_resamplings_le_pmfPi_symmetric`, `ae_exists_forall_notMem_run_pmfPi` and
`ae_exists_forall_notMem_run_pmfPi_symmetric` for events stated against `Cslib.Probability.PMF.pi`.

The Section 6 lopsided extension is in `CslibFrontier.Probability.MoserTardos.Lopsided`
[mosertardos10]. `Lopsidependent` and `lopsidedAdj` replace variable sharing by lopsidependency in
the witness-tree relation `witnessRel (lopsidedAdj vbl A)`, using canonical depth-ordered log
normalization for Lemma 6.2 (`Lopsided.table_isLog_eq_prod` and `Lopsided.table_witness_le`) and
yielding Theorem 6.1 (`Lopsided.lintegral_resamplings_le`, `Lopsided.lintegral_sum_resamplings_le`,
`Lopsided.ae_exists_run_eq_none`, `Lopsided.ae_exists_forall_notMem_run`,
`Lopsided.exists_forall_notMem`, and symmetric `Lopsided.lintegral_resamplings_le_symmetric`,
`Lopsided.ae_exists_forall_notMem_run_symmetric` and `Lopsided.exists_forall_notMem_symmetric`).

For exact `k`-CNF satisfiability with improved constants,
`CslibFrontier.Logics.Propositional.CNF.Moser.LocalLemma` instantiates these theorems on
`CNF.IsExactDistinct k` formulas with the deterministic rule `Moser.firstViolatedRule`. Under
standard share degree `Moser.degree φ i ≤ d` and `Real.exp 1 * (d + 1) ≤ 2 ^ k`, it supplies
`Moser.lintegral_resamplings_le_of_exp_mul_le`, `Moser.lintegral_sum_resamplings_le_of_exp_mul_le`,
and `Moser.ae_exists_eval_run_firstViolated_of_exp_mul_le` (yielding a constructive proof of
`CNF.IsExactDistinct.satisfiable_of_exp_mul_le` above). Using `Moser.Conflicts` and
`Moser.conflictDegree`, `Moser.not_lopsidependent_of_not_conflicts` weakens the neighborhood to
clauses sharing a variable with opposite polarity, yielding
`Moser.lintegral_resamplings_le_of_conflict_exp_mul_le`,
`Moser.lintegral_sum_resamplings_le_of_conflict_exp_mul_le`,
`Moser.ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le` and
`CNF.IsExactDistinct.satisfiable_of_conflict_exp_mul_le` under `Real.exp 1 * (d' + 1) ≤ 2 ^ k`.

The model counts resamplings; it does not charge for sampling or for detecting occurring events.
Theorems 1.3 (the parallel version) and 1.4 (the deterministic version) are not formalized. The
[checked examples](../../CslibFrontierTests/MoserTardos.lean) give one fair coin, where the bound is
`x / (1 - x) = 1`, two dependent events on three coins that meet the hypothesis with equality, an
impossible event with `x = 0`, two complementary events for which no `x` satisfies the
hypothesis, a concrete valid log on a fixed table whose witness tree is computed by `decide`
and passes its check, symmetric (`d = 0` and `d = 1`) and `PMF.pi` bridges, and Section 6
lopsided events sharing a variable where the standard bound fails; check them with
`scripts/build.sh CslibFrontierTests.MoserTardos`. The
[constructive `k`-SAT examples](../../CslibFrontierTests/MoserLocalLemma.lean) cover an exact
`4`-CNF exceeding `degree < 2 ^ (k - 3)`, a `decide`-verified `firstViolatedRule` step, and
exact `3`-CNFs where `conflictDegree` (`0` and `1`) succeeds while `degree = 3` fails the standard
Local Lemma; check them with `scripts/build.sh CslibFrontierTests.MoserLocalLemma`.

Support-based CNF model counting counts assignments to variables that occur. Declared-universe counting instead fixes a larger variable set and can include free choices for unused variables. The library supplies relabeling and exact gadget-counting bridges, so a reduction claiming preservation of counts must specify which convention it preserves. This distinction is particularly relevant to dense relabeling and the [native fixed-width counting endpoint](../machines-and-classes/native-counting.md).

For interoperability and generic solver/branching APIs over `CNF`, import
[StdSat](../../CslibFrontier/Logics/Propositional/CNF/StdSat.lean),
[Restrict](../../CslibFrontier/Logics/Propositional/CNF/Restrict.lean),
[Simplification](../../CslibFrontier/Logics/Propositional/CNF/Simplification.lean), and
[UnitPropagation](../../CslibFrontier/Logics/Propositional/CNF/UnitPropagation.lean). `CNF.toStdSat`
and `CNF.ofStdSat` give exact bijections with `Std.Sat.CNF` preserving `Sat`, `Unsat`, relabeling,
`Std.Sat.CNF.relabelFin`, and exact `Fintype.card` vs `modelCountOn`/`modelCount` on `Std.Sat.CNF (Fin n)` (bundled as
`Clause.equivStdSat` and `CNF.equivStdSat`). `CNF.restrict` splits models via the explicit
bijections `CNF.restrictModelsEquiv` and `CNF.modelsSplitEquiv` and gives additive branching
(`CNF.modelCountOn_eq_add_restrict`) plus length and occurrence bounds; `CNF.unitPropagate` performs fuel-bounded structural propagation
while conserving satisfiability and model counts (`CNF.modelCountOn_unitPropagate`,
`CNF.modelCount_unitPropagate`); and `CNF.Sparsification` width-free lemmas track evaluation,
scaling, total literal counts, and occurrences under `removeTautologies`, `dedup`, `dedupClauses`,
`reduce`, `normalize`, and `countingNormalize`. For binary encodings paired with a unary
variable bound `numVars`, [DeclaredCNF](../../CslibFrontier/Computability/Complexity/Problems/SAT/Declared.lean)
supplies `declaredCNFDecoder` and the polynomial-time well-formed word recognizer
`declaredCNFCode`. See the [CNF basis tests](../../CslibFrontierTests/CNFBasics.lean), checked with
`scripts/build.sh CslibFrontierTests.CNFBasics`.

[Constraint](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CSP.lean#L69) has a relation alphabet and constraints consisting of a relation label plus a variable list. Semantics evaluates the label on the corresponding list of domain values. Arity is not enforced by the relation's type; a fixed-arity interpretation is an additional condition. Boolean/CNF translations and partition-function clients instantiate this generic semantic interface; see [weighted CSP partition functions and variable elimination](networks-and-iteration.md#weighted-csp-partition-functions-and-variable-elimination) for `partitionFunctionOn`, separator conditioning, `FactorTable` tensor bridges, and `TimeM` / weight-cost variable elimination.

[QBF](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/QBF.lean#L76) uses named-variable Boolean quantifiers. Evaluating an existential or universal binder updates the assignment with both possible values and ORs or ANDs the results. Arithmetization and native/interactive-proof completeness clients live in their corresponding sections. This formula syntax does not by itself assert a resource bound for evaluation.

## Boolean functional completeness

Import `CslibFrontier.Logics.BooleanClone.Post` for Post's five-class criterion. A family
`G n` of Boolean operations is `BooleanClone.FunctionallyComplete G` exactly when it has
an operation outside each of the 0-preserving, 1-preserving, monotone, self-dual and affine
classes (`BooleanClone.functionallyComplete_iff`). The witnesses may have different arities;
the family may be infinite. Affinity uses the existing `BitString.IsAffine` convention.

`BooleanClone.generated` records finite superpositions and projections. Its foundation and
four-generator classification are shared with Schaefer's proof below. Import
`CslibFrontier.Logics.BooleanClone.Formula` for `generated_iff_exists_formula` and
`exists_circuit_of_postCriterion`: the generated operations have actual formula and circuit
realizations. See the [checked NAND and incomplete-basis examples](../../CslibFrontierTests/PostCompleteness.lean).

This API quantifies over **positive input arities**. Constants are unary constant functions.
NAND alone is complete in this sense, but cannot synthesize a zero-input constant gate.
Circuit `Interpretation.IsComplete` also quantifies over zero inputs, so the Post theorem
supplies positive-arity circuits without claiming that stronger instance. No gate-count bound
or full classification of Post's lattice is asserted.

## Boolean Schaefer dichotomy

Import `CslibFrontier.Computability.Complexity.Problems.CSP.Schaefer` for the full Boolean
classification. `Cslib.Complexity.CSPSAT.schaefer_dichotomy` proves native P membership when a
common unary constant, AND, OR, ternary majority or ternary parity preserves the language, and
native NP-completeness otherwise. `CSPSAT.mem_P_or_npComplete` gives the unconditional
alternative. No assumption that P differs from NP is used.

`CSPSAT arity sem` uses the existing CSP lists. The relation alphabet is finite and fixed; each
symbol has an arbitrary fixed arity and Boolean list semantics. Every scope must have exactly
its declared length. The encoding is `encCSP encRel encNat`, with framed lists/pairs and binary
variable labels. Repeated variables, empty relations, nullary relations and empty alphabets are
allowed; malformed scopes are rejected even when their list semantics would accept them.
Constants in `CSP.HasSchaeferPolymorphism` are standard unary operations. An empty relation is
preserved vacuously, so the constant decider explicitly rejects constraints using empty relations.
`CSPSAT.mem_P_of_constant` supplies native P in either constant case.

The other native tractable endpoints are `CSPSAT.mem_P_of_and`, `mem_P_of_or`,
`mem_P_of_majority` and `mem_P_of_parity`. Each endpoint selects its fixed local
normal forms internally and invokes a certified compiler and solver. There is no solver or
template hypothesis. Bounds apply to each fixed language; no uniform bound on preprocessing a
supplied language or truth table is asserted. Local positions use unary lookup indices; original
variable names remain binary throughout. The shared arity-check certificate is
`Cslib.Complexity.CSP.computableInPolyTime_validArity` in `PolyTime.CSP.Boolean`;
`CSPSAT.polyTimeReducible_of_guard` in `Problems.CSP.Basic` turns any polynomial-time compiler
that is faithful on well-formed instances, together with a fixed reject instance outside the
target, into the guarded reduction used by each endpoint.

[The full checked client](../../CslibFrontierTests/Schaefer.lean) exercises every tractable arm,
a concrete NAE hard language, arbitrary fixed arities, sparse labels and an empty alphabet.
[Horn/dual-Horn clients](../../CslibFrontierTests/CSPHorn.lean) give AND-only and OR-only languages
and malformed/repeated-scope examples. [Affine clients](../../CslibFrontierTests/CSPAffine.lean)
cover cancellation, sparse labels, empty/nullary relations and actual compiler/solver runs.
[The initial contract examples](../../CslibFrontierTests/BooleanCSP.lean) and
[constant/majority clients](../../CslibFrontierTests/CSPTractability.lean) remain useful entry points.

For the structural APIs, `Cslib.Logic.IsPolymorphism` combines satisfying tuples coordinatewise.
It is preserved by conjunction, substitution (including repeated variables), existential projection
and composition. Its operation index may be empty; this general nullary notion is distinct from
the unary constants in the criterion. For every finite coordinate type, majority preservation is equivalent to a
2CNF definition (`PL.isPolymorphism_majority_iff_exists_twoCNF`), AND/OR preservation to a
Horn/dual-Horn definition (`PL.isPolymorphism_and_iff_exists_hornCNF`,
`PL.isPolymorphism_or_iff_exists_dualHornCNF`), and ternary parity preservation to an affine
system (`PL.isPolymorphism_parity_iff_exists_affineSystem`). These definitions need no auxiliary
variables and include empty/nullary relations. See the [majority examples](../../CslibFrontierTests/MajorityCNF.lean).

The ordinary solvers are also reusable: `TwoSAT.mem_P`
([TwoSAT/PolyTime.lean](../../CslibFrontier/Computability/Complexity/Problems/TwoSAT/PolyTime.lean)),
`HornSAT.mem_P`, `DualHornSAT.mem_P` and `XORSAT.satisfiable_mem_P`. For `TwoSAT`,
`TwoSAT.assignment` constructs a satisfying assignment in polynomial time on binary CNF encodings
(`TwoSAT.computableInPolyTime_assignment`, `TwoSAT.eval_assignment_of_mem`) by filtering
occurrence-bounded implication-graph reachability lists (`TwoSAT.reach`). Horn syntax counts
positive occurrences, so two copies of a positive literal violate the syntax condition; repeated
negatives and opposite-polarity tautologies are supported. Forward chaining reaches the pointwise-least
model in `numVars + 1` passes (`HornSAT.isLeast_assignment`), storing filtered occurrences rather than
an array indexed by the largest name; `HornSAT.exists_multiple_models` exhibits a satisfiable Horn
formula whose least model is not the unique satisfying model on its occurring variables. Affine
equations are variable lists paired with Boolean right-hand sides; repeated variables cancel in the
Boolean ring. Dense Gaussian elimination preserves row count and weakly decreases its complete framed
state encoding at each column. See the [SCC and 2-SAT tests](../../CslibFrontierTests/SCCAndTwoSAT.lean),
[Horn solver tests](../../CslibFrontierTests/HornSAT.lean)
and [XOR solver tests](../../CslibFrontierTests/XORSAT.lean).

The hard branch `CSPSAT.npComplete_of_not_hasSchaeferPolymorphism` imports all its mathematical
and reduction ingredients. The positive-arity Boolean clone classification
(`Cslib.Logic.BooleanClone.classification`) covers every arity: absent the six operations, every
polymorphism is a projection or negated projection and preserves all self-dual relations.
`SelfDualThreeSAT.npComplete` gives a hard source by lifting signed ternary clauses with a shared
reference bit. XOR with that bit normalizes any model of the reduction's output to an ordinary
clause model. The eight lifted relations are proved self-dual, nonempty and column-separating.

`CSP.exists_ppGadget_of_polymorphisms` constructs their actual finite primitive-positive gadgets,
and `CSP.computableInPolyTime_replaceGadgetsGuarded` certifies replacement with even original
names, fresh odd auxiliary names and malformed-input rejection. The gadget API requires nonempty
targets with separating columns; this application discharges those hypotheses and makes no claim
of general equality elimination. See [clone examples](../../CslibFrontierTests/BooleanClone.lean),
[gadget examples](../../CslibFrontierTests/CSPGadget.lean) and
[hardness examples](../../CslibFrontierTests/SchaeferHardness.lean).

`CSPSAT.exists_linear_size_reduction_from_threeSAT` supplies one reduction with native
polynomial-time computation, correctness and the bound
$n' + m' \le C_\Gamma m \le C_\Gamma(n + m)$. Here `numVars` counts distinct occurring
variables, `length` counts clauses or constraints, and the constant depends only on the fixed
target language. The bound holds for every raw CNF, including malformed and empty inputs.
`CSP.length_replaceGadgets` and `CSP.vars_length_replaceGadgets` give exact sums of template
constraint and occurrence counts; distinct variables are bounded by occurrences. The guarded
compiler retains a uniform linear bound because an invalid input is nonempty. These are
combinatorial size bounds; neither linear running time nor linear binary encoding length is
asserted. See the [checked size clients](../../CslibFrontierTests/SchaeferSize.lean).

The result is the Boolean dichotomy; symmetric and larger-domain dichotomies are outside its scope.

## Planar Boolean CSP prerequisites

`CslibFrontier.Foundations.Data.BitString.CyclicDifference` defines ordered cyclic differences:
`cyclicDifference x i` is `x i ^^ x (finRotate n i)`. Its image is exactly the even-parity
tuples, and `cyclicIntegral` constructs an inverse by prefix parity. The fiber theorem
`cyclicDifference_eq_iff` says that two tuples have the same differences precisely when they
are equal or complementary. Consequently, `mem_cyclicDifferenceRelation_iff` recovers any
`IsSelfComplementary` relation from its difference relation. Empty and nullary relations are
included. These are the tuple and relation transformations of Kazda–Kolmogorov–Rolínek,
arXiv:1602.03124v6, Definitions 13–14, printed p. 0:6.

Import `CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Operations` for relational
`BitString.IsDeltaMatroid` and `BitString.IsEvenDeltaMatroid`. The exchange axiom is one-sided:
for feasible `x,y` disagreeing at `i`, some disagreeing coordinate `j` makes
`flipOn {i,j} x` feasible. A delta-matroid is nonempty. Evenness means that all feasible tuples
have the same parity, which may be odd; it forces `j ≠ i`. Twists and coordinate equivalences
preserve these properties, and feasible tuples are connected by feasible two-coordinate flips.
The four-coordinate lemmas isolate local exchange consequences used by the paper's blossom
proof; they do not prove its full forest or whole-blossom contraction invariants.

[Difference tests](../../CslibFrontierTests/CyclicDifference.lean) show that ternary NAE maps to
an even delta-matroid of three weight-two tuples. [Exchange tests](../../CslibFrontierTests/DeltaMatroid.lean)
include odd exactly-one relations, the empty-coordinate case, and failures of exchange/evenness.
The complete explicit-table edge solver is documented below. Planar embedding recognition,
geometric realization and the full complexity dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Occurrences, explicit tables and ordered incidence rotations

`CslibFrontier.Logics.Propositional.CSP.Occurrence` indexes arguments by constraint position and
scope position, preserving repeated variables and identical constraints. `ValidLabeling` checks
each ordered local tuple; `ConsistentLabeling` requires agreement at all occurrences of a variable.
Given a supplied `outside : D`, their conjunction is equivalent to the existing CSP
satisfiability predicate. Reconstruction assigns `outside` to every nonoccurring variable; the
domain-value hypothesis is necessary when the domain may be empty. `EdgeInstance`
requires exactly two occurrences per occurring variable, in distinct constraints, and supplies a
partner involution. Its endpoint agreement is equivalent to global consistency. The native
`Cslib.Complexity.CSP.incidenceGraph` in `Problems.CSP.Incidence` reuses the existing listed graph
and positive-CNF adapter. It retains one edge per argument, dense variable vertices followed by
constraint-position vertices, and a native polynomial construction with binary source labels.
See [occurrence and incidence tests](../../CslibFrontierTests/CSPOccurrence.lean).

`CslibFrontier.Computability.PolyTime.CSP.Table` supplies `CSP.Table` as an explicit, potentially
infinite relation alphabet for the same CSP lists. Arity is binary; accepted rows are doubly
framed Boolean lists, including duplicate rows. Width errors reject every row. The local
`Table.contract` retains rows with zero or one deviation from a feasible reference on selected
internal positions, projects outside positions in their original order, and appends the connector
bit. Its row count cannot increase; at least two distinct in-range internal positions imply
strict width decrease and nonincrease of the full encoded table size. `Table.exactlyOne`
constructs the new connector relation in native polynomial time from a scope list: the list's
length pays for quadratic output. There is no polynomial-output claim from a binary arity alone.
The zero-connector relation is empty. [Table tests](../../CslibFrontierTests/CSPTable.lean) cover
malformed widths, repeated rows, contraction cases and framed size calculations. These operation
lemmas supply executable operations and quantitative bounds. Mathematical closure and
whole-instance correctness are documented separately below.

`Problems.Graph.RotationSystem` represents edge ends by edge-list position and a Boolean side.
Loops have two distinct ends, and parallel edges retain separate positions. Vertex rotations
have exactly one cycle per nonempty endpoint fiber. Face orbits use reversal followed by inverse
rotation and include fixed-point orbits. `Problems.CSP.RotationSystem` maps ordered arguments to
these ends and states `RespectsArgumentOrder`: the rotation at a constraint follows cyclic scope
order. Mirroring a ternary constraint can violate that order. Nullary constraints have no argument
ends, so this order condition is vacuous for them. See [graph rotation tests](../../CslibFrontierTests/RotationSystem.lean)
and [constraint-order tests](../../CslibFrontierTests/CSPRotationSystem.lean).

A rotation structure alone does not impose genus zero. The finite-certificate layer in
`Problems.CSP.RotationSystem.Certificate` checks a supplied rotation table: one binary successor
index for each of the graph's `2m` indexed darts. It checks exact length, declared endpoints,
permutation and equality of successor orbits with endpoint fibers, then decodes an accepted table
to the existing rotation structure. Constraint successors must also follow the original cyclic
scope order. A mirrored ternary rotation can pass the graph check and fail this order check.

`Graph.RotationSystem.NumericalGenusZero` requires `V + F = E + 2` independently in every edge
component. It counts distinct vertices, listed edges and all face orbits, including singleton
orbits; every face stays within one component. An isolated declared vertex uses the separate
point convention `V = 1, E = 0, F = 1`, without creating a dart. The native graph checker is
`Graph.RotationCertificate.verifyGenusZero`. Its completeness theorem
`exists_bounded_certificate_iff` requires declared endpoints and supplies a certificate of at most
`10 * (N + 1)^2` bits, where `N` is the graph's complete `encGraph` bit length.

The native CSP checker `CSP.verifyRotationCertificate` combines numerical genus zero with
`RespectsArgumentOrder`. `CSP.exists_bounded_rotationCertificate_iff` proves both directions of
certificate completeness, and `CSP.polyBounded_rotationCertificateBound` bounds its certificate
size polynomially in the source CSP encoding. `CSP.computableInPolyTime_verifyRotationCertificate`
uses `encCSPRotationCertificate encRel encV`, pairing the original framed CSP with the framed
successor table. The native cost proof covers malformed tables and enormous binary labels or
indices; only actual list lengths fund iteration. See the [graph certificate tests](../../CslibFrontierTests/RotationCertificate.lean)
and [ordered CSP certificate tests](../../CslibFrontierTests/CSPRotationCertificate.lean).

These are finite encoding and numerical-verification results; the indexed duality and lifting
theorems below extend their mathematical interface. The guarded candidate constructor below
adds success soundness. Geometric realization, identifying the outer face across disconnected
components and complete bare-instance recognition/construction remain open.
The complete explicit-table edge solver is documented below. Exact relation-arity and satisfiability guards are
separate: a false nullary relation passes the port-order check. Rejection of a supplied toroidal
rotation does not prove that its graph is nonplanar. The full objective remains
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Frozen XOR queries and checked candidate recovery

From the repository root, import
`CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Query` and
`CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Recovery`.
The namespace is `Cslib.Complexity.Graph.RotationRecognition`. The
[checked guide clients](../../guide/CslibFrontierGuide/NPCompleteness.lean#frozen-xor-queries-and-checked-recovery)
show the ordinary imports, concrete validation/failure cases and success contracts.
The [regression suite](../../CslibFrontierTests/RotationRecognition.lean) additionally exercises
loops, parallel edges, repeated scopes, nullaries and large binary labels; run
`scripts/build.sh CslibFrontierTests.RotationRecognition` to check it. Successful compilation
checks actual solver/recovery evaluations and theorem applications, without proving completeness.

`FixedRotationInput` pairs the existing listed graph with optional complete clockwise dart
words. `Valid` requires declared vertices exactly `List.range n`, endpoints below `n`, exactly
`n` table entries, and every `some word` to enumerate its entire endpoint fiber without
duplicates. `none` leaves a vertex free; `some []` is valid at an isolate. `Realizes` fixes the
full cyclic successor, without reflection; `Consecutive` constrains only successive entries
inside a directed block. `Feasible` is existence of the existing `RotationSystem` satisfying
`NumericalGenusZero` and `Realizes`.

`query` computes `validate I && XORSAT.solve (compile I)`. Each edge is twice subdivided;
fixed vertices freeze their incident first/last segments, and middle segments stay movable.
The stored segment components have named accessors `Segment.endpoints`, `Segment.source`,
`Segment.target` and `Segment.frozen`; their tuple representation and encoding are unchanged.
The reference order reverses prescribed leaves within each center block. Each independent
unordered segment pair emits one sparse affine row of width at most four, with frozen
contributions omitted. `query_eq_true_iff` proves exactly `Valid I` and affine satisfiability.
Import the [finite move topic](../../CslibFrontier/Computability/Complexity/Problems/Graph/RotationSystem/Recognition/Moves.lean)
for `query_eq_true_iff_exists_frozen_moves`: the same equations have a finite
segment-by-vertex Boolean witness with literal frozen zeros. Neither statement identifies
these equations with `Feasible`.

`recover` tries clockwise append candidates using ephemeral `split` queries. A split redirects
the selected indexed ends to fresh hub `n`, appends nonloop connector `(n,v)`, and fixes the
hub's complete word to `block ++ [2m]`; the source remains free. The connector need not be a
bridge. Old edge occurrences and earlier full orders are retained. The outer state stores the
original graph and its current order table; split graphs and XOR systems do not accumulate.
The final candidate must pass `RotationCertificate.verifyGenusZero` and `verifyFixed`.
`recover_sound` gives these exact guards; `recover_feasible` supplies `Feasible` on success.
`length_recover_successor` gives exactly `2m` output entries, and `length_enc_recover_le`
bounds the complete framed certificate by `2m * (4m + 1)` bits.

`ofCSP` uses the actual `CSP.incidenceGraph`: variable vertices are free, and each indexed
constraint's actual scope fixes its full order. It retains repeated variables, identical
constraints and nullary constraint vertices. Relation semantics and declared arity metadata
are not consulted. `recoverCSP` also runs the existing original CSP argument-order checker;
`recoverCSP_sound` proves that this checker accepts every returned certificate. A false nullary
relation can therefore yield a successful numerical candidate: this program does not decide
CSP satisfiability. `none` may come from input rejection, a false XOR query, failed candidate
search or a rejected final table; it implies neither nonplanarity nor CSP unsatisfiability.
Dvořák–Kupec's constraint-set convention and the indexed duplicate-preserving CSP convention
are distinct models; applying a source theorem requires an explicit bridge, not deduplication.

`query_polyTime`, `recover_polyTime` and `recoverCSP_polyTime` certify the actual native
programs on all raw encodings, with no solver, growth or runtime provider. Binary names fund
no unary scans. `encFixedRotationInput` frames the graph and optional binary dart-word list;
the temporary frame uses a unary vertex count, binary segment endpoints/frozen bits, and a
binary reference order. The [query-budget topic](../../CslibFrontier/Computability/Complexity/Problems/Graph/RotationSystem/Recognition/RecoveryBudget.lean)
charges at most `1 + 2m²` queries generally and `1 + m²` for CSP incidence recovery, where `m`
counts listed graph edges, hence actual scope occurrences for CSPs. These are query charges,
not running-time exponents.
For original CSP encoded length `B`, put `K = B + 1`. The
[storage bounds](../../CslibFrontier/Computability/Complexity/Problems/Graph/RotationSystem/Recognition/CSPBounds.lean)
give initial XOR storage at most `9K² * (32 * (log₂(9K²) + 1) + 21)` bits, including all
framing. The same bound for a split requires `Valid (split (ofCSP F) v block)`;
the general form requires validity and both frame dimensions at most `3K`.
It is not a bound on arbitrary malformed compiled systems in terms of `B` alone.

The finite equations reconstruct Schaefer's *Toward a Theory of Planarity*, §§5.3–5.4,
printed pp. 399–401 ([primary source](https://jgaa.info/index.php/jgaa/article/download/paper298/2658/2465)).
Here frozen segments have zero moves past every vertex; the paper's PEP restriction fixes
embedded edges past embedded vertices. Equivalence needs proof. Fulek–Kynčl–Pálvölgyi,
*Unified Hanani–Tutte theorem*, arXiv:1612.00688v3, Theorem 1, p. 2
([primary source](https://arxiv.org/pdf/1612.00688v3)), is a prospective bridge from independent
evenness and evenness at selected vertices to a rotation-preserving embedding; it is not
formalized here. The contiguous candidate recovery is original, with reconstruction and
implementation credit retained in the source headers.

The open obligations are `Valid I → (XORSAT.Satisfiable (compile I) ↔ Feasible I)`, the
split feasibility equivalence with original numerical genus zero, full orders and
`Consecutive block` (including clockwise order, nonloop contraction and duplicate-declaration
cleanup), and the geometric/source correspondence with frozen-switch and Hanani–Tutte proofs.
The shared `Graph.RotationSystem.Declarations` supplies duplicate-declaration numerical
transport; `Recognition.Declarations` adds only the fresh-range relabeling. These ingredients
do not discharge the split equivalence. This bounded runtime/soundness milestone leaves
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091) open; no final planarity
P theorem or decision completeness is claimed.

## Indexed duality and Boolean difference lifting

Import `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Dual`,
`ComponentCounts` and `Lifting` at the same module prefix. The namespace is
`Cslib.Complexity.Graph.RotationSystem`. These modules use the existing listed multigraph and
rotation models. `dualGraph` preserves each listed edge position and names its incident faces
by their least actual dart indices. `dualRotation` uses the source face successor as its vertex
rotation; the dual face successor is edge reversal, source rotation, then edge reversal.
The complete face/incident-vertex equivalences include singleton face orbits and retain loops,
parallel occurrences and repeated boundary vertices.

`numericalGenusZero_dual_iff r hG` preserves the existing componentwise numerical predicate.
Its explicit `hG` requires every endpoint to be declared. Source isolated points have no dart
and are omitted by dualization; their conventional source Euler equation is trivial. The
empty graph and disconnected mixtures of point and edge components are included. The proof
provides actual component bijections and exact vertex, edge and face counts.

`FaceEven x` requires even parity on every actual face boundary. Darts are counted separately,
so repeated appearances of an edge contribute with their boundary multiplicity. `edgeGradient`
assigns the XOR of the endpoint spins to each indexed edge. With declared endpoints and
`r.NumericalGenusZero`, `faceEven_iff_exists_vertexSpins r hG hgenus x` proves
`r.FaceEven x ↔ ∃ spin : Nat → Bool, G.edgeGradient spin = x` for arbitrary finite listed graphs.
The proof derives connectivity and characteristic-two incidence ranks internally. The reverse
implication, `faceEven_edgeGradient`, telescopes along face boundaries and needs neither graph
premise. Duplicate vertex declarations and sparse natural-number names are supported.

The [dual and lifting tests](../../CslibFrontierTests/RotationDual.lean) check actual bridge, loop
and digon dual data; a toroidal obstruction; disconnected point/edge mixtures; duplicate
vertex declarations; names of size `2^100`; and the endpoint guard. The generic
`Matrix.endpointIncidence` API is in
`CslibFrontier.Foundations.LinearAlgebra.Matrix.EndpointIncidence`; loops contribute twice and
cancel over `ZMod 2`, while parallel column positions stay distinct. Finite permutation orbit
transport is shared through `CslibFrontier.Foundations.GroupTheory.Perm.Doubled`.

These are combinatorial duality and lifting results, reconstructing the graph prerequisite in
Dvořák–Kupec, §3, printed p. 439. The checked compiler below supplies the native
supplied-certificate CSP reduction, followed by the complete native edge solver below.
Geometric realization, bare rotation recognition and final planar assembly remain open
under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Face boundaries and closed-passage intersection parity

Import `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity`.
For an indexed Boolean edge labeling, `G.VertexEven x` sums actual dart incidences at each
vertex; both ends of a loop contribute and cancel. With declared endpoints `hG` and
`r.NumericalGenusZero`, `r.vertexEven_iff_exists_faceColors hG hgenus x` proves
`G.VertexEven x ↔ ∃ q : r.Face → Bool, r.faceBoundary q = x`. The boundary labels an edge by
the XOR of its two incident face colors. The proof applies the existing lifting theorem to
the actual indexed dual, retaining sparse names, duplicate declarations, disconnected
components and isolated points.

`Graph.ClosedPassages G x` pairs all darts of the supported edge set exactly once, with
distinct ports at the same vertex. Separate visits and arbitrary local pairings are allowed.
`r.Alternates` uses the literal forward cyclic interval between ports; `r.intersectionParity`
adds the crossing bits of every passage pair. For two systems with disjoint edge supports,
`r.intersectionParity_eq_false hG hgenus P Q hdisj` proves even total intersection parity.
Face colors make the local interval sums telescope, then the closed-system endpoint
contributions cancel. No intersection-parity or Jordan theorem is supplied as a premise.

The [complete regression clients](../../CslibFrontierTests/RotationIntersection.lean) include
bridges, singleton loop faces, parallel digons, degree-eight multiple passages, disconnected
sparse names and empty supports. The interlaced two-loop torus has odd intersection parity
and fails the genus hypothesis. The [scoped audit](../../CslibFrontierTests/RotationIntersectionAudit.lean)
checks stored declarations and environment linters. These are original finite-map proofs;
they do not establish drawing operations, geometric realization, Hanani–Tutte, recognition
or the full planar dichotomy. The checked guide's “Face Boundaries and Intersection Parity”
section gives complete generic applications.

## Indexed rotation surgery

The modules at `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem` construct
actual indexed rotations and prove preservation of the existing componentwise numerical
genus predicate. Import `CornerGenus` for corner insertion, `VertexMergeGenus` for cofacial
vertex identification, `EdgeDeletionGenus` for deletion, `EdgeContractionGenus` for contraction,
and `Declarations` for changing only declared vertex lists. Their namespace is
`Cslib.Complexity.Graph.RotationSystem`. The guide's “Indexed Rotation Surgery” section gives
complete generic clients.

Given existing dart corners `h` and `k`, `r.insertEdge h k` appends one listed edge between
their vertices. `numericalGenusZero_insertEdge r hG hr h k hf` requires declared endpoints,
source numerical genus zero and `hf : r.faceNext.SameCycle h k`. Corners and vertices may
coincide. In the selected component, the edge and face counts each increase by one.
`numericalGenusZero_mergeVertices` additionally requires distinct selected vertices and the
same-face premise; its actual name update retains indexed edges and directed port order.
Arbitrary noninjective relabeling alone is not a genus-preservation result.

For `r : RotationSystem (lastEdgeGraph G u v)`, `r.deleteLastEdge` removes exactly the final
listed edge and retains the original graph `G`. `numericalGenusZero_deleteLastEdge r hH hr`
requires declared source endpoints and source numerical genus zero. It covers splitting
bridges, loops, pendant edges that create isolated points and disconnected mixtures.
For `huv : u ≠ v`, `r.contractLastEdge huv` instead targets
`G.relabel (Function.update id u v)`. `numericalGenusZero_contractLastEdge r huv hH hr`
requires neither a bridge nor cofaciality nor connectedness. The selected directed blocks
are spliced without reflection; retained edge and end positions stay explicit.

Contraction maps the declared vertex list pointwise and can leave duplicate declarations.
`redeclare r W` changes that list while retaining all edges, darts and successors.
`numericalGenusZero_redeclare_iff hm r` requires equal old/new declared membership;
`numericalGenusZero_append_duplicate_iff hv r` removes a repeated already declared name.
These transports justify cleanup; the duplicated and cleaned graph pairs need not be equal.

The `Lifting` module's `component_euler_le` bounds `V + F ≤ E + 2` for an incident component
under the endpoint guard, without a genus premise. `numericalGenusZero_of_faceEven_lifts`
proves the converse algebraic characterization of numerical genus zero. The deletion and
contraction proofs discharge its lifting hypothesis internally by extending face-even edge
labels. `FacePotential` concerns differences along the face permutation, on any rotation;
it is not a vertex-spin or genus-zero assumption. Isolated components retain the separate
conventional face; no nonexistent dart is introduced.

The [corner](../../CslibFrontierTests/RotationCornerFaces.lean),
[vertex identification](../../CslibFrontierTests/VertexIdentification.lean),
[general deletion](../../CslibFrontierTests/RotationDeletionComponents.lean),
[contraction](../../CslibFrontierTests/RotationContraction.lean) and
[algebraic converse](../../CslibFrontierTests/RotationLiftingConverse.lean) clients check actual
successor tables, nonbridge connectors, loops at both endpoints, empty residual blocks,
reflected-order rejection and untouched point/edge components. Arbitrary-degree star
rotations are supplied by importing `Star` at the same module prefix and using
`starRotation` and `numericalGenusZero_starRotation`.
The general point-insertion, cycle-surgery and selected-orbit APIs live in
`CslibFrontier.Foundations.GroupTheory.Perm.InsertAfter`, `CycleSurgery` and
`SelectedOrbits`, in `Equiv.Perm.Insertion`, `Equiv.Perm.CycleSurgery` and
`Equiv.Perm.SelectedOrbits`; they import no graph modules. The complete
[permutation-only client](../../CslibFrontierTests/PermutationSurgery.lean) uses these imports
without the graph layer.
These are original permutation/algebraic proofs, with no native runtime or geometric
realization claim. Full gadget-recipe realization, recognition, Hanani–Tutte and the planar
dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Polygonal geometry prerequisites

Loop-only numerical-genus-zero rotations now have actual polygonal embeddings with their
exact clockwise order, as documented below. The general numerical-genus / polygonal-realization
equivalence still needs general forward restoration of nonloop contractions by directed
contiguous vertex splits. The finite polygonal-to-numerical converse is proved below from
actual embeddings and literal clockwise realization. Topological taming, indexed FZ versus DK set conventions
and source comparison, frozen-switch completeness, Hanani–Tutte recognition and the full
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091) endpoint remain open.

**Start:** complete [checkout setup](../workflows/getting-started.md#prerequisites-and-the-checkouts-version)
and work from the repository root. Open the checked guide's “Polygonal Geometry Prerequisites”
section in [the complete chapter](../../guide/CslibFrontierGuide/NPCompleteness.lean), including its
ordinary imports and local `open` context. For a small client, import the required modules:

- `CslibFrontier.Foundations.Geometry.Polygonal.Route` defines `Cslib.Polygonal.Route`;
  `Segment` at the same prefix adds `Route.line` and `isSimple_line_iff`, `Germs` gives
  end-segment interpolation, and `Neighborhood` separates finite compact segment families.
- `CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing` defines drawings;
  `.Germs` adds incident-direction injectivity, `.Neighborhood` adds vertex balls,
  `.Points` supplies edgeless drawings and `.Star` supplies arbitrary-degree star embeddings.
- `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic`
  defines literal clockwise realization. `CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Loop`
  exposes the extracted single-loop passage and the numerical noninterlacing theorem.

A route lists `bends + 2` points in `ℂ` and has `bends + 1` actual real affine segments.
`eval i t` ranges over all real parameters in `[0,1]`; `support` is the union of those segments.
`IsSimple` identifies adjacent segment junctions by their equal global parameter and permits
first/last closure, excluding other contacts. Thus `Route.isSimple_line_iff a b` says a
one-segment route is simple exactly when `a ≠ b`; a one-segment loop is rejected.

In `Cslib.Complexity.Graph`, `PolygonalDrawing G` uses the existing natural-number names and
listed edge occurrences. Its only fields are vertex coordinates, a route per edge position
and endpoint equations. `IsEmbedding` requires injectivity on distinct declared names,
route simplicity, declared-vertex avoidance except at corresponding ends, and contacts of
different routes only at common named ends. Repeated declarations name one point; identical
listed endpoint pairs retain separate routes. Undeclared names are unconstrained. A loop
retains two end parameters and two outgoing germs. No genus certificate or geometry provider
is stored in a drawing.

For `hD : D.IsEmbedding`, `hD.directions_injective a b hv hdir` proves `a = b` from equal
vertex names and directions, including the same-loop case. `hD.exists_vertex_ball v hv`,
where `hv : v ∈ G.1`, constructs `ε > 0` such that every segment meeting the ball at
`D.vertex v` is a first segment starting at `v` or a last segment ending at `v`. It uses
finite compact-segment separation internally; it is not a topological disk or splitting patch.

`D.Realizes r` is separate from embedding. It requires nonzero germs, distinct incident
directions and literal clockwise order for every distinct incident triple `a,b,c`:
`sbtw (D.direction c) (D.direction b) (D.direction a) ↔ b ∈ r.rotationInterval a c`.
The reversed `Real.Angle` betweenness makes forward `rotate` clockwise in the fixed complex
plane, without reflection. `faceNext = rotate⁻¹ ∘ reversal` (`σ⁻¹ α`) keeps the right-side face.

`PolygonalDrawing.star_isEmbedding n` proves embedding for every finite degree, including
zero; it does not prove arbitrary-degree star realization. `points_isEmbedding vertices`
and `points_realizes vertices r` handle any declared isolate list and any rotation of that
edgeless graph. The guide checks degree 20 and sparse repeated point declarations.
`ClosedPassages.loop e he` pairs the two indexed ends of a loop with singleton edge support.
`r.not_alternates_loops hG hr e f hef he hf` excludes alternating ends of distinct loops,
assuming all incident endpoints are declared (`hG`), numerical genus zero (`hr`), distinct
edge positions (`hef`) and the two loop equations. It needs no connectedness or degree bound
and supplies no drawing.

From the repository root, run
`scripts/build.sh CslibFrontierTests.PolygonalDrawing CslibFrontierTests.PolygonalDrawingAudit CslibFrontierTests.RotationIntersection --wfail --iofail`.
All three modules should elaborate; use [artifact troubleshooting](../workflows/troubleshooting.md#diagnose-missing-or-stale-artifacts)
for missing imports, and retain the ordinary imports if a declaration is unavailable.
The [geometric clients](../../CslibFrontierTests/PolygonalDrawing.lean) also check actual bridge,
closed-loop and parallel-digon realizations, degrees 0 and 5, sparse isolate separation,
clockwise sign and reverse-order rejection. The [scoped audit](../../CslibFrontierTests/PolygonalDrawingAudit.lean)
checks stored declarations and environment linters; the [intersection clients](../../CslibFrontierTests/RotationIntersection.lean)
reuse the extracted loop constructor. This is original geometric infrastructure, with no
DK, FKP or Hanani–Tutte formalization, coordinate bit bound or native runtime theorem.

### Loop-only clockwise realization

Import `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Bouquet`.
For `r : RotationSystem G`, `r.exists_polygonalDrawing_of_loops hG hr hloop` returns
`∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r`. Its hypotheses declare every
incident endpoint (`hG`), require `r.NumericalGenusZero` (`hr`), and require each listed edge's
two endpoint names to agree (`hloop`). There is no noncrossing, drawing, disk or provider
hypothesis. Repeated loop pairs, disconnected vertices, sparse or duplicate declarations,
isolates and the empty graph are included, with no degree bound.

The construction derives nonalternation from numerical genus zero, ranks actual darts in
clockwise order, and draws each loop with five real affine segments. Disjoint or nested rank
intervals have disjoint interiors; positive port coordinates fix the clockwise germ order.
A common spacing separates distinct vertex names. `PolygonalDrawing.bouquet` is the explicit
drawing, with `bouquet_isEmbedding` and `bouquet_realizes` supplying its contracts. This is an
original coordinate construction, with no coordinate-bit or native-runtime bound claimed.

The [checked guide](../../guide/CslibFrontierGuide/NPCompleteness.lean) applies the theorem and
constructs a two-loop embedding with a repeated declaration and a disconnected isolate.
The [bouquet tests](../../CslibFrontierTests/PolygonalBouquet.lean) supply a nonvacuous family
at every degree, nested/disjoint loops, negative interlacing and reversed-order cases;
[their audit](../../CslibFrontierTests/PolygonalBouquetAudit.lean) checks stored declarations.
Run `scripts/build.sh CslibFrontierTests.PolygonalBouquet CslibFrontierTests.PolygonalBouquetAudit --wfail --iofail`.
This proves the loop-only forward direction. Together with the converse below it gives the
loop-only equivalence. General nonloop restoration and the full planar objective remain open.

## Polygonal embeddings imply numerical genus zero

Import `CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse`.
For an actual `D : PolygonalDrawing G`, `hD : D.IsEmbedding`, declared incident endpoints
`hG` and literal clockwise realization `hR : D.Realizes r`, apply
`hD.numericalGenusZero hG hR`. The conclusion is the existing componentwise
`r.NumericalGenusZero`. No genus, face-color, lifting, disk, Jordan or Hanani–Tutte premise
is supplied. Coordinates are arbitrary complex numbers; all real parameters on every affine
segment are retained. Loops keep two ends, parallel occurrences keep their positions, and
arbitrary degree, disconnected graphs, sparse/duplicate declarations, points and empty graphs
are included. The [checked guide](../../guide/CslibFrontierGuide/NPCompleteness.lean) gives
complete ordinary-import clients and combines it with the loop-only forward theorem.

The constructive intermediate API is `hD.exists_faceColors hR hG x hx`, from
`PolygonalDrawing.FaceColors`. For every actual `x : Fin G.2.length → Bool` satisfying
`hx : G.VertexEven x`, it constructs colors `q : r.Face → Bool` with
`r.faceBoundary q = x`. These are the actual permutation face classes, not a replacement
geometric-face definition. A generic ray direction is chosen from the finite segment endpoints;
angular-prefix values transport along all real segment interiors, through bends and through
the empty inverse-rotation sectors. Vertex-evenness cancels endpoint cuts, including singleton
rotations and both ends of loops. The values descend through the literal `faceNext`; the exact
indexed dual/lifting cycle-space criterion then proves numerical genus zero.

Generic ray, determinant, segment and fan-order facts live under
`CslibFrontier.Foundations.Geometry.Polygonal`; their proofs have no graph dependency.
`AngleOrder` supplies the one-turn span criterion shared by fixed horizontal ports and
moving local fans, allowing either choice of argument cut.
`RayParityEven` supplies local constancy from zero total endpoint jump on the observation
ray; even incidence derives that premise. `RayParityTransport` reuses this criterion after
removing the observed segment, whose endpoint heights differ from the observation height.
The [ray-parity tests](../../CslibFrontierTests/PolygonalRayParity.lean) check a single selected
segment with odd endpoint incidence where the weaker local criterion applies.
The graph-specific construction data stay private. The existing lifting-based criterion is a
proof tool: callers of the final theorem do not supply its face-color premise. `LocalSplitFan`
and `LocalSplitOrder` supply the needed fan/order facts, with the span-order proof shared through
`AngleOrder`; the remaining cut/join scaffolding belongs to the still-open forward lane.

Run `scripts/build.sh CslibFrontierTests.PolygonalConverse CslibFrontierTests.PolygonalConverseAudit --wfail --iofail`.
The [concrete converse client](../../CslibFrontierTests/PolygonalConverse.lean) applies the endpoint
to actual loop, bridge and parallel-digon embeddings and a clockwise degree-five star, then
checks sparse/duplicate isolates and emptiness. A nonzero loop label separates its two actual
faces. The torus test rules out realizing that interlaced rotation; it makes no nonplanarity
claim about the underlying graph. The [audit](../../CslibFrontierTests/PolygonalConverseAudit.lean)
covers stored declarations in the new endpoint modules, with its exclusions explicit.

This is an original finite PL proof. General forward restoration, arbitrary topological-arc
taming and source-model comparison, frozen-switch completeness, HT/recognition, native
coordinate/runtime bounds and full [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)
remain separate obligations.

## Ordered incidence-to-polygon rotations

Import `CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler`.
In `Cslib.Complexity.CSP`, `polygonGraph F` has one listed edge per actual argument occurrence,
from its variable to the next variable in the same cyclic scope. Variable names are replaced by
the existing dense occurrence names. Unary scopes give loops; repeated variables and identical
constraints retain their separate edge and constraint positions. With `M` occurrences, there
are exactly `M` edges and at most `M` variable vertices.

Given an incidence rotation `r`, `polygonRotation r` constructs the corresponding abstract
polygon rotation. `RespectsArgumentOrder r` records the original cyclic scope order. If every
actual scope is positive, `polygonFaceEquiv r hOrder hPos` identifies all polygon faces with
`Fin F.length ⊕ r.Face`: one indexed black face per constraint, plus every original incidence
face as a white face. Singleton faces are included, and the two sides of every polygon edge
belong to distinct faces. The positivity guard concerns actual scopes, independently of any
relation arity or semantics. Nullary constraints require separate treatment.

`polygonComponentEquiv F hPos` gives the complete component correspondence. Per component,
`V_incidence = V_polygon + constraintCount`, `E_incidence = E_polygon`, and
`F_polygon = constraintCount + F_incidence`. These actual counts prove
`numericalGenusZero_polygon_iff r hOrder hPos` for the existing componentwise numerical
predicate. Empty and disconnected instances are included, without a finite universe or
magnitude bound on variable names.

The [primal rotation tests](../../CslibFrontierTests/CSPPrimalRotation.lean) cover unary loops,
repeated arguments and identical constraints, sparse `2^100` labels, disconnected/empty bodies,
malformed declared arity, the nullary guard, and an ordered toroidal example where both
numerical predicates fail. General face-quotient cardinality facts are in
`CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts`; dense vertex
counts reuse the existing component-vertex set API. Incidence endpoint declaration now lives
at its source in `Problems.CSP.Incidence`, with its name and certificate clients preserved.

This reconstructs the finite maps behind Dvořák–Kupec's ordered face model, printed p. 434.
`polygonGraph` is an explicit list construction; abstract rotation/equivalence inverses are
proof data. The supplied-certificate compiler below supplies a native executable stage.
Geometric realization, bare recognition and the complete
planar CSP reduction/solver remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Checked cyclic-difference edge compiler

Import `CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Spec` for
`Cslib.Complexity.CSP.CyclicCompiler.compile_spec`, and `.Size` for its bounds.
For a fixed finite Boolean language, call `compile arity sem (F, cert)` on the original
list CSP and a supplied ordered numerical rotation certificate. The two static hypotheses
are self-complementarity of every canonical relation and the even-delta-matroid property
of each **nonempty** relation's cyclic-difference image. Empty symbols are allowed.

The same compiler has ordinary native polynomial time on all raw inputs. Its output is
an `EdgeInstance`, with exact table/scope widths and nonempty even delta-matroid constraints.
Target satisfiability is equivalent to source satisfiability together with
`WellFormed arity F` and `verifyRotationCertificate F cert = true`.
Malformed scopes, invalid certificates and occurring empty relations reject to two
incompatible nonempty unary pins. True nullaries disappear internally; false nullaries
reject. `Primal.Nullary` proves the required face/Euler bridge without a positive-scope
premise on the source. Repeated arguments, identical constraints and disconnected inputs
retain positional identity.

Input encoding is `encCSPRotationCertificate encRel encNat`: the framed CSP followed by
the certificate, whose successor indices are binary. Output uses `encCSP encTable encNat`,
including explicit rows, binary arities/names and list/pair framing. Language preprocessing
may depend exponentially on fixed arity; it is not a uniform algorithm on language descriptions.
White boundaries use width-three parity chains: a boundary of length `k ≥ 4` yields
`k−2` constraints and `k−3` auxiliaries, avoiding exponential white truth tables.

With `C` source constraints and `M` actual occurrences, every raw output has at most
`C+M+2` constraints and `4M+2` ports, with names below `2M+1`.
`polyBounded_length_compile` proves polynomiality of the complete framed output length;
these counts alone are not its runtime certificate. The [compiler tests](../../CslibFrontierTests/CSPCyclicCompiler.lean)
execute SAT/UNSAT NAE examples, long boundaries, nullaries, malformed and toroidal rotations,
and binary labels/indices up to `2^250`.

The compiler reuses the now-public runtime helpers `orbitBool_polyTime`,
`faceTable_polyTime` and `argumentNextIndex_polyTime`, preserving their statements,
proofs and local automation. This implements the supplied numerical-certificate stage of
Dvořák–Kupec §3, printed pp. 439–440, Lemma 5/Corollary 4/Theorem 2; bounded scans and
parity-chain implementation are original. The complete explicit-table solver below supplies
the edge algorithm. Geometric realization, bare recognition and the full planar dichotomy remain
open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Delta-matroid composition and local contraction closure

`CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Composition` proves direct products,
elimination of equal coordinate pairs, and relational composition. `IsDeltaMatroid.comp` and
`IsEvenDeltaMatroid.comp` join relations on `ι ⊕ κ` and `κ ⊕ τ` along the finite shared `κ`
coordinates, then remove those coordinates. Both require a nonempty composed relation:
nonempty inputs alone do not guarantee compatible shared values. Empty external coordinate
types are allowed. The proof uses successive one-sided exchanges, without assuming simultaneous
exchange. This maps Proposition 6 and its parity corollary in Kazda–Kolmogorov–Rolínek,
arXiv:1602.03124v6, printed pp. 0:4–0:5, with output nonemptiness made explicit.

`CslibFrontier.Logics.Propositional.CSP.Table.DeltaMatroid` connects this mathematics to the actual
guarded table semantics. `Table.isEvenDeltaMatroid_contract` requires the original declared-arity
table relation to be even and `Table.canContract table reference positions = true`. The latter
supplies the feasible reference and distinct in-range internal positions; the reference witnesses
nonemptiness of the output internally. The proof preserves outside-coordinate order and the
final connector, using composition with a proved star gadget that permits zero internal changes
or one internal change paired with a true connector. No blossom or solver hypothesis appears.
Unlike strict width decrease, closure requires no lower bound of two on the selected positions.

`Table.isEvenDeltaMatroid_exactlyOne` proves closure for every nonempty connector scope, with odd
common parity. The empty-scope relation is rejected under the nonempty delta-matroid convention.
[Composition and contraction tests](../../CslibFrontierTests/DeltaMatroidComposition.lean) cover
incompatible shared coordinates, empty external coordinates, arbitrary scope lengths, ordered
outside ports, empty selections, nullary tables, and malformed guards. Native operation and size
certificates remain those of `PolyTime.CSP.Table`. The whole-instance mathematical layer appears below;
the complete native solver appears below. The full planar dichotomy remains open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Prefix-valid walks and augmentation

Import `CslibFrontier.Logics.Propositional.CSP.Edge.Augmenting` for Boolean occurrence-label
optimization. `CSP.defects` counts distinct occurring variables carrying unequal endpoint labels;
`CSP.IsOptimalLabeling` requires validity and minimum defect count among all valid labels.
Valid labels with zero defects are equivalent to a model of the original CSP, using `false`
on nonoccurring variables. `EdgeInstance` supplies the exact-two/distinct-constraint condition.
`EdgeInstance.EvenConstraints` states that each relation on its actual ordered scope positions
is an even delta-matroid; local common parity may be odd and may differ between constraints.

A `CSP.Walk` stores a starting variable and a list of incidence pairs. Its `IsWalk` predicate
requires linked constraint steps and no reused incidence, while allowing repeated constraint
positions and closed trails. `IsFWalk` requires distinct endpoints, consistent internal variables,
and validity after every variable-ended prefix. Final validity alone is insufficient. An
augmenting walk has two defective endpoints. Its flip is valid, and
`Walk.IsAugmenting.card_defects_flip_add_two` proves that it removes exactly two defects. Prefix validity and the
partner-transition lemmas connect these paths to the original indexed occurrence model.

`EdgeInstance.augmentingWalk` implements the two phases of Lemma 31 in
Kazda–Kolmogorov–Rolínek, arXiv:1602.03124v6, printed p. 0:15. Given valid `f,g` with fewer
defects in `g`, it repairs comparison-only defects and follows remaining disagreements using
deterministic positional scans. Its specification returns an augmenting walk starting away
from an arbitrary specified variable; that variable may still be the endpoint. The combined
number of local exchanges is at most half the initial occurrence Hamming distance. This is an
exchange-count bound, not a native-machine runtime bound. `isOptimalLabeling_iff_no_augmentingWalk`
then characterizes optimality without assuming a solver.

[Augmenting-walk tests](../../CslibFrontierTests/EdgeCSPWalk.lean) include doubled equality
constraints, actual returned paths, odd unsatisfiable units, repeated constraint positions,
empty/nullary cases, sparse labels, and a trail whose final flip is valid but an intermediate
prefix is invalid. This routine takes an improving comparison labeling as input. The fresh
forest search below instead starts from the base labeling alone and stops at exhaustion,
augmentation or a blossom. The contraction/lifting entry below supplies the mathematical
next step, followed by the complete native edge solver. The planar dichotomy remains open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

For explicit tables, import `CslibFrontier.Computability.PolyTime.CSP.Edge.Augmenting`.
In `Cslib.Complexity.CSP.EdgeAugmenting`, `Input` contains the original `CSP Table Nat`,
two occurrence-bit buffers and the excluded starting variable. `encInput` frames the CSP and
both buffers; the final excluded variable is binary without an additional frame. Table arities,
source names and output walk indices are binary. Internal scan positions are unary.
`computableInPolyTime_run` proves ordinary native polynomial time in the complete encoded input,
including malformed tables and buffers. Iteration depends on actual lists, never the largest name.

`run_eq` identifies the finite output with the existing mathematical routine whenever both buffer
lengths equal the occurrence count. `run_spec` additionally takes the edge-instance and even
relation hypotheses, valid original/comparison labels and a strict defect improvement; it returns
an actual existing `Walk`, its decoder equation, augmentation correctness and the combined
half-Hamming exchange bound. `none` is a helper failure or width rejection, not an unsatisfiability
answer. [Native augmentation tests](../../CslibFrontierTests/EdgeCSPAugmentingNative.lean) exercise
returned paths, both phases, width rejection, empty/nullary constraints and sparse binary names.
The supplied improving comparison remains necessary for this two-phase routine. The fresh search
below has no comparison input, and its native compiler is documented separately below.
The whole-instance mathematical layer and complete native edge solver are documented below.

The reusable scan lives in `CSP.Occurrence.Enumeration`: `incidenceList` and
`occurrences_eq_map_incidenceList` connect typed occurrences to the existing ordered record list.
`PolyTime.CSP.Occurrence` supplies `encOccurrenceRecord` and
`computableInPolyTime_occurrences` without importing graph construction. Both incidence graphs
and the native augmentation compiler use that same enumeration and certificate.

## Algebraic proof systems

Nullstellensatz (NS) certificates and Polynomial Calculus (PC) proofs use coefficients in a
commutative semiring `R`, in the namespaces `Cslib.Logic.PL.NS` and `Cslib.Logic.PL.PC`.
The caller supplies all input axioms for the chosen encoding and basis. Standard Boolean and
complementary axioms such as `x² - x` and `x + x̄ - 1` require a ring. In the two proof modules,
`NS.IsProof.eval_eq_zero` and `PC.IsProof.eval_eq_zero` show that every proved polynomial vanishes
at any common zero of the inputs. Their `exists_eval_ne_zero` lemmas
require `Nontrivial R` and show that a refutable system has no common zero.
[NS proof module](../../CslibFrontier/Logics/Propositional/Algebraic/Nullstellensatz/Proof.lean),
[PC proof module](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/Proof.lean).

The computable `NS.size` is the sum of products of input and multiplier support sizes, exactly
the standard NS size `∑ᵢ ‖pᵢ‖ ‖fᵢ‖` in de Rezende et al., §8.1 (STOC 2021, p. 217), where
`‖p‖` counts nonzero monomials. `PC.size` sums support sizes across all proof lines, counting
repeated lines separately. `NS.degree` bounds sums of input and multiplier total degrees for
nonzero multipliers. A nonzero multiplier of a zero input still contributes its degree.
`PC.degree` is the maximum total degree of a proof line. Both degrees return `0` on empty data.
The lemmas `NS.degree_le_iff` and `PC.degree_le_iff` recover the term and line bounds. These
measures concern formal polynomials, so a Boolean or other basis change needs its own resource
comparison. [de Rezende et al.](https://www.ias.edu/sites/default/files/deRezendeGoNoPiRoSo_Automating.pdf)

`PC.exists_isProof_of_ns` translates an NS certificate for any nonzero target polynomial `q`,
of size at most `s` and total degree at most `d`, into one PC proof containing `q`, of size at
most `s² + (d + 1)s` and total degree at most `d`. Under `Nontrivial R`,
`PC.exists_refutation_of_ns` specializes this to refutations (`q = 1`). Fact 8.1 (p. 218)
addresses arbitrary target polynomials, including zero, and block degree over fields; here the
target must be nonzero and only total degree is treated.
[NS-to-PC simulation](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/Nullstellensatz.lean).

For input total degrees at most `d₀`, `PC.RefutableInSize.of_ns` gives PC size at most
`(d₀ + 1)s² + s` from NS size at most `s`, under the same nontriviality assumption. Its auxiliary
gap-truncation bound `NS.IsProof.exists_degree_le_mul_size`, proved here, first supplies a
replacement NS certificate of no larger size and degree at most `d₀` times the original size.
The replacement discards high-degree cancellation and multipliers of zero inputs.

Over every commutative semiring, `NS.exists_isProof_of_pc` gives a certificate for every PC
proof line, without a size or degree bound.
[PC-to-NS conversion](../../CslibFrontier/Logics/Propositional/Algebraic/Nullstellensatz/PolynomialCalculus.lean).

The clause-only CNF arithmetization uses `Literal.toPolyAssignment` to assign each literal its
Boolean truth value in the coefficient semiring. Over a ring, positive and negative coordinates
are `a` and `1 - a`. A clause polynomial multiplies the coordinates of complementary literals,
so `x ∨ ¬y` becomes `x̄ · y`. These are the twin variables of polynomial calculus resolution
(PCR), as in [Alekhnovich et al., §4.1, p. 1197](https://doi.org/10.1137/S0097539700366735).
The identity `Clause.eval_toPoly` gives value `0` for a satisfied
clause and `1` for a falsified clause. With `Nontrivial R`,
`CNF.eval_eq_true_iff_forall_eval_toPoly_eq_zero` characterizes satisfaction by the vanishing of
every clause polynomial at that same Boolean assignment. Arbitrary literal coordinates can give
a spurious solution to contradictory unit clauses.
[Pointwise CNF encoding](../../CslibFrontier/Logics/Propositional/Algebraic/CNF.lean).

The checked [proof-system examples](../../CslibFrontierTests/ProofComplexity/AlgebraicProofSystems.lean)
exercise the simulations over semirings and rings with zero divisors, including a nonconstant
nonzero target and a satisfiable system with no refutation. The
[CNF examples](../../CslibFrontierTests/ProofComplexity/AlgebraicCNF.lean) cover both literal
polarities, the empty clause and spurious zeros at noncomplementary coordinates. Each file
includes its imports. From the repository root, check them with:

```bash
scripts/build.sh \
  CslibFrontierTests.ProofComplexity.AlgebraicProofSystems \
  CslibFrontierTests.ProofComplexity.AlgebraicCNF
```

### Resolution to polynomial calculus with resolution

Import `CslibFrontier.Logics.Propositional.Algebraic.CNF.PCR` for the
[complete PCR encoding](../../CslibFrontier/Logics/Propositional/Algebraic/CNF/PCR.lean).
`Clause.toPCRPoly` multiplies one complementary literal variable for each **distinct** literal
of the clause. Thus both `x ∨ x` and `x` give `x̄`, whereas the existing `Clause.toPoly` retains
list multiplicity. The squarefree encoding has at most one nonzero monomial and degree at most
`Clause.width`, including for resolvents whose concatenated lists repeat literals.

For a finite variable type, `CNF.toPCRPolys` appends `PCR.axioms` to the clause polynomials:
`X l ^ 2 - X l` for both literal polarities, and
`PCR.complementAxiom v = X (v, true) + X (v, false) - 1` for each original variable. The
assignment convention is still `1` for a true literal. Over a nontrivial commutative ring,
`CNF.eval_eq_true_iff_forall_eval_toPCRPolys_eq_zero` characterizes satisfaction at those
literal truth values, and `CNF.not_satisfiable_of_pcr` gives refutation soundness. Over a field,
`CNF.exists_commonZero_toPCRPolys_iff` also characterizes arbitrary common zeros: the Boolean
and complementarity equations force them to come from Boolean assignments.

The [resolution translation](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/Resolution.lean)
uses the existing `PC.IsProof` constructors over this input list. Import
`CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Resolution` and apply
`CNF.IsProof.exists_pcr` to a resolution proof with `s` lines, each of width at most `w`.
Over any commutative ring it gives one PCR proof with `PC.size ≤ (5 * w + 13) * s` and
`PC.degree ≤ w + 1`, containing the polynomial of every resolution line. Thus the empty
clause supplies the constant polynomial `1`; `CNF.IsProof.exists_pcr_refutation` retains both
bounds for a refutation. The squarefree representation and the treatment of tautological parents
cover the library's list-based resolution rule without a normalization assumption.

`CNF.RefutableInWidth.pcr_refutableInDegree` gives degree at most `w + 1` from a width-`w`
refutation. `CNF.RefutableInSize.pcr_refutableInSize` gives size at most
`(10 * N + 13) * s`, where `N = φ.vars.toFinset.card`, using the bound `w ≤ 2 * N`.
This is a joint resource bound: it does not remove dependence on width or on the number of
variables. A uniform polynomial bound in the resolution line count alone, as discussed in
[#3542](https://github.com/cslib-community/cslib-frontier/issues/3542), requires a further argument.
PCR size sums the supports of formal polynomial lines, including repetitions; it is neither
the number of lines nor a count of monomials after reduction modulo the Boolean ideal.

PCR's twin-variable representation follows [Alekhnovich et al., §4.1](https://doi.org/10.1137/S0097539700366735)
(the [author preprint](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/ABRA01/ABRA01.pdf),
pp. 17–18). The explicit size and degree constants here come from this construction; the paper's
Lemma 4.1 concerns space. Encoded translation time, degree-controlled substitution into the
original-variable PC encoding, and configuration-space bounds remain separate objectives.

The [checked examples](../../CslibFrontierTests/ProofComplexity/ResolutionPCR.lean) show that
arbitrarily many repetitions of a literal leave squarefree degree at `1`, while the old
list-product degree grows with the repetition count. A three-line contradictory-unit
refutation translates to at most `54` monomials and degree `2` over every commutative ring,
instantiated over `ℚ` and `ZMod 2`. The examples also check both orientations of a tautological
parent, a repeated nonpivot literal in a resolvent, satisfiable formulas with no PCR
refutation, and the empty variable type. From the repository root, run:

```bash
scripts/build.sh CslibFrontierTests.ProofComplexity.ResolutionPCR
```

### Refutations over the Boolean cube

[The Boolean-cube layer](../../CslibFrontier/Logics/Propositional/Algebraic/Boolean.lean) reuses
the NS and PC proofs above and passes the Boolean axioms `X i ^ 2 - X i` as explicit inputs,
`F ++ boolAxioms σ R`. `IsBoolSolution F x` says that every `f ∈ F` vanishes at the `0/1` point
`x : σ → Bool`, read in `R` with `1` for true. Soundness (`NS.IsProof.not_isBoolSolution`,
`PC.IsProof.not_isBoolSolution`) holds over every nontrivial commutative ring. Completeness holds
over a field. If every input has total degree at most `D` in `n = card σ` variables and there is
no Boolean solution, then `NS.refutableInDegree_of_forall_not_isBoolSolution` gives a
Nullstellensatz refutation of degree at most `n + D`, and `PC.RefutableInDegree.of_ns` transfers
it to polynomial calculus (`NS.refutableInDegree_iff`, `PC.refutableInDegree_iff`). The proof uses
Mathlib's Combinatorial Nullstellensatz. The bound `n + D` comes from that argument; the sharper
polynomial calculus bound `max(D, n + 1)` of Impagliazzo, Pudlák and Sgall (Lemma 4.1) is not
formalized. Two helpers support these results:
[`NS.exists_isProof_of_sum`](../../CslibFrontier/Logics/Propositional/Algebraic/Nullstellensatz/Combination.lean)
turns a finite combination of inputs into a certificate with the same degree bound, and
[`PC.IsProof.mono`](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/Invariant.lean)
enlarges the input list. `Algebraic.setOf_mem_boolAxioms` identifies the members of
`boolAxioms σ R` with the set `SOS.Psatz.booleanAxioms σ R` that Positivstellensatz refutations
take as equations ([sum-of-squares](#sum-of-squares)).

[The Boolean CNF encoding](../../CslibFrontier/Logics/Propositional/Algebraic/CNF/Boolean.lean)
substitutes `X v` for the positive literal coordinate and `1 - X v` for the negative one in
`Clause.toPoly`. So `Clause.toBoolPoly` is the standard product encoding in the original
variables: `x ∨ ¬y` becomes `(1 - x) · y`. With `1` read as true, the clause polynomial is `0`
at a satisfying point and `1` at a falsifying point (`Clause.eval_toBoolPoly`), and
`CNF.isBoolSolution_toBoolPolys_iff` identifies Boolean solutions with satisfying assignments.
Because the Boolean axioms are inputs, contradictory unit clauses have no spurious solution.
`CNF.not_satisfiable_of_ns` and `CNF.not_satisfiable_of_pc` give soundness. Over a field,
`CNF.ns_refutableInDegree_iff` and `CNF.pc_refutableInDegree_iff` give refutability in degree
`card V + w`, for clauses of at most `w` literals, exactly when the formula is unsatisfiable.

[The Boolean-cube quotient module](../../CslibFrontier/Foundations/BooleanAnalysis/BooleanQuotient.lean)
identifies the quotient `MvPolynomial ι R ⧸ boolIdeal ι R` over any commutative ring `R` and
finite `ι` with the ring `(ι → Bool) → R` of cube functions (`boolQuotientAlgEquiv`), and proves
uniqueness of multilinear representatives in `restrictDegree ι R 1` over arbitrary commutative
rings and index types (`existsUnique_mem_restrictDegree_sub_mem_boolIdeal`, coinciding with
`multilinearExtension` when `ι` is finite). The companion linear equivalences
`restrictDegreeOneLinearEquiv` and `restrictDegreeOneQuotientEquiv` (with `@[simp]` evaluation and
inverse lemmas `restrictDegreeOneLinearEquiv_apply`, `coe_restrictDegreeOneLinearEquiv_symm`,
`restrictDegreeOneQuotientEquiv_apply`, `eval_coe_restrictDegreeOneQuotientEquiv_symm`, and
`coe_restrictDegreeOneQuotientEquiv_symm_mk`) transport between multilinear polynomials, cube
functions, and quotient cosets. Over a reduced ring `boolIdeal` is radical
(`boolIdeal_isRadical`), and over a field `K` the quotient has dimension `2 ^ Fintype.card ι`
(`finrank_boolQuotient`).
[Algebraic/CNF/Counting](../../CslibFrontier/Logics/Propositional/Algebraic/CNF/Counting.lean)
identifies the spans of `boolAxioms` and `SOS.Psatz.booleanAxioms` with `boolIdeal`
(`span_boolAxioms_eq_boolIdeal`, `span_booleanAxioms_eq_boolIdeal`), characterizes unsatisfiability
over a field by `1 ∈ Ideal.span {p | p ∈ F} ⊔ boolIdeal σ K`
(`Algebraic.one_mem_sup_boolIdeal_iff`), and defines the `0`/`1` clause and formula satisfaction
indicators `Clause.satPoly R c := 1 - c.toBoolPoly R` and `CNF.satIndicatorPoly R φ`. Over any
commutative ring `R`, summing `φ.satIndicatorPoly R` over Boolean assignments to `declared`,
`φ.vars.toFinset`, or `bitsAssignment φ.distinctVars i` (`i < 2 ^ φ.numVars`) equals the natural
count cast into `R`, `(φ.modelCountOn declared : R)` or `(φ.modelCount : R)`
(`CNF.sum_eval_satIndicatorPoly_declared`, `CNF.sum_eval_satIndicatorPoly_vars`,
`CNF.sum_range_eval_satIndicatorPoly_distinctVars`), whereas over the finite ambient cube `V → Bool`
it equals `(2 : R) ^ (Fintype.card V - φ.numVars) * (φ.modelCount : R)` with the unused-variable
factor `(2 : R) ^ (Fintype.card V - φ.numVars)` (`CNF.sum_eval_satIndicatorPoly`); in positive
characteristic, casting into `R` preserves the counts only modulo the ring characteristic.
[Checked examples](../../CslibFrontierTests/BooleanQuotientSAT.lean) verify uniqueness over the
non-reduced ring `ZMod 4` (where `boolIdeal` fails to be radical), the dimension `4` on two
variables over `ℚ`, unsatisfiability in `span F ⊔ boolIdeal`, and the cube-sum identities including
unused variables (`sparseFin3`, where `modelCount = 3` and the `Fin 3 → Bool` sum is `6`).

[The subset-sum lower bound](../../CslibFrontier/Logics/Propositional/Algebraic/SubsetSum.lean) is
Theorem 5.1 of Impagliazzo, Pudlák and Sgall. Suppose every `c i` is nonzero and `n ≥ 1`. Then
`m - ∑ c i * X i`, with the Boolean axioms, has no polynomial calculus refutation
(`PC.not_refutableInDegree_subsetSumPoly`) and no Nullstellensatz refutation
(`NS.not_refutableInDegree_subsetSumPoly`) of degree `⌈n/2⌉ = (n + 1) / 2`. The source proves
this over `ℝ`; the formal statement needs only a field in which `⌈n/2⌉!` is nonzero. When no subset
of the `c i` sums to `m`, completeness gives a refutation of degree `n + 1`
(`PC.refutableInDegree_subsetSumPoly_iff`). The proof runs the invariant method
`PC.IsProof.mem_of_degree_le` on the submodule of polynomials that agree on the cube with
`(m - ∑ c i x i) · r` for some `r` of degree below `d`, using Lemma 5.2 from the
[foundations section](#foundations-for-algebraic-degree-lower-bounds). The
[tests](../../CslibFrontierTests/ProofComplexity/Algebraic.lean) check the following instances:

- An explicit degree-2 Nullstellensatz refutation of `1/2 - x`, which has no degree-1
  polynomial calculus refutation.
- `x₁ + x₂ + x₃ + x₄ = 5` over `ℚ` and over `ZMod 7`, refutable in degree 5 but not in degree 2.
- `x₁ + x₂ + x₃ = m` over the field with nine elements, for `m` outside `0, 1, 2, 3`, refutable
  in degree 4 but not in degree 2, although `3!` vanishes there.
- The instance with no variables, refutable in degree 0, which shows that `n ≥ 1` is needed.
- `v ∧ ¬v`, refuted in degree 1, and the satisfiable formula `v`, which has no refutation.

Run `scripts/build.sh CslibFrontierTests.ProofComplexity.Algebraic` from the repository root to
check them.

[The algebraic functional pigeonhole encoding](../../CslibFrontier/Logics/Propositional/Algebraic/FunctionalPigeonhole.lean)
defines `algFPHP m n R` for `m` pigeons and `n` holes over a commutative ring `R` in variables
`Fin m × Fin n` (`x_{ij} = 1` when pigeon `i` occupies hole `j`, matching the `1`-for-true
Boolean-cube convention above). It decomposes as
`algFPHPConstraints m n R ++ boolAxioms (Fin m × Fin n) R`, combining pigeon axioms
`algFPHPPigeonPoly i := 1 - ∑ j, X (i, j)` (note the opposite sign convention from `pigeonPoly`
in [SumOfSquares/Pigeonhole](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Pigeonhole.lean)),
functionality axioms `X (i, j) * X (i, j')` (`j < j'`), hole axioms `X (i, j) * X (i', j)`
(`i < i'`), and the shared Boolean axioms `boolAxioms`. Over any nontrivial commutative ring,
Boolean solutions correspond bijectively to injective maps `Fin m ↪ Fin n` via `pigeonIndicator`
(`isBoolSolution_algFPHP_iff`, `boolSolutionEquivEmbedding`); over any integral domain, arbitrary
common zeros are forced to be `0`/`1`-valued and share the same bijection
(`eval_algFPHP_eq_zero_iff`, `commonZeroEquivEmbedding`). Consequently, satisfiability holds
exactly when `m ≤ n` (`exists_isBoolSolution_algFPHP_iff`, `exists_commonZero_algFPHP_iff`),
polynomial calculus refutability over fields holds iff `n < m`
(`exists_pc_refutableInDegree_algFPHP_iff`, via `not_pc_refutableInDegree_algFPHP` and
`pc_refutableInDegree_algFPHP_of_lt`), and when `n = 0 < m`, pigeon `0`'s axiom `algFPHPPigeonPoly`
is already `1` (`algFPHPPigeonPoly_zero`), giving an explicit degree-`0` refutation over any
commutative ring (`pc_refutableInDegree_algFPHP_zero`). The
[checked examples](../../CslibFrontierTests/ProofComplexity/AlgebraicFunctionalPigeonhole.lean)
verify `algFPHP 1 1`, `algFPHP 2 1` (including an explicit `6`-line degree-`2` PC refutation over
every commutative ring), `n = 0 < m`, `m = 0`, and roundtrips for `boolSolutionEquivEmbedding` and
`commonZeroEquivEmbedding`; check them with
`scripts/build.sh CslibFrontierTests.ProofComplexity.AlgebraicFunctionalPigeonhole`.

Not yet formalized ([Impagliazzo, Pudlák and Sgall][impagliazzopudlaksgall99]; [#3569](https://github.com/cslib-community/cslib-frontier/issues/3569)):
the matching subset-sum upper bound of Theorem 4.2, the general and `algFPHP` size–degree
tradeoffs, standard-CNF `FPHP`–`algFPHP` PCR encoding equivalence, pigeonhole degree and size
lower bounds, and the degree-controlled resolution translation into the original-variable PC
encoding. The twin-variable PCR simulation is described [above](#resolution-to-polynomial-calculus-with-resolution).

### Tseitin formulas

[The Tseitin degree lower bound](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/Tseitin.lean)
is the polynomial calculus counterpart of the Ben-Sasson–Wigderson width lower bound. Take a field
`K` with `2 ≠ 0` and a connected multigraph `ends : E → Sym2 V`. Then a polynomial calculus
refutation of degree `d` of the clause polynomials of `CNF.tseitinFormula ends χ`, together with
the Boolean axioms, forces `e(G) ≤ 2 d`
(`Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree`). Here `e(G)` is
`Multigraph.minBalancedCut`, the same expansion used in the width bound. The Nullstellensatz form
follows through `PC.RefutableInDegree.of_ns`
(`Tseitin.minBalancedCut_le_two_mul_of_ns_refutableInDegree`). The sum-of-squares counterpart,
Grigoriev's bound `e(G) ≤ d` for the `±1` encoding of the Tseitin parity system, is described
under [Sum-of-squares](#sum-of-squares). That Tseitin formulas are hard for
polynomial calculus over fields of characteristic `≠ 2` is due to Buss, Grigoriev, Impagliazzo
and Pitassi (JCSS 2001), and for the Nullstellensatz to Grigoriev (FOCS 1998). Buss and
Nordström, Handbook of Satisfiability, §7.5.4, record this hardness qualitatively and describe the
`R`-operator method. The quantitative form `e(G) ≤ 2 d`, with the Ben-Sasson–Wigderson expansion,
is the form proved here; it is not taken from a checked source statement. The theorem numbers and
constants of the two original papers have not been checked against a copy. The proof uses the
invariant method with the change of variables `x ↦ (1 - y) / 2`. The invariant is the common
kernel of linear functionals indexed by sets `T` of at most `d` edges. Each functional sends a
monomial to the sign `(-1) ^ χ(U)` of the unique set `U` of fewer than `|V| / 3` vertices whose
edge cut is the symmetric difference of `T` and the set of odd-degree variables of the monomial,
or to `0` if there is no such `U`. The terms of a clause polynomial cancel in pairs, and `2 ≠ 0`
turns `2 S = 0` into `S = 0`.

[The expander corollary](../../CslibFrontier/Logics/Propositional/Algebraic/PolynomialCalculus/TseitinExpander.lean)
turns this into `h(G) |V| / 6 ≤ d` on rotation maps with edge expansion `h(G) > 0`. With
`RotationMap.expander` it gives `CNF.exists_forall_pc_refutableInDegree_le`. For every `n ≥ 2`,
this is an unsatisfiable formula with at most `120 n` variables, at most `2 ^ 120 · n` clauses
and at most `120` literals per clause. Every polynomial calculus refutation of it over every field
with `2 ≠ 0` has degree at least `n / 36000`. As in the resolution case, the expanders come from
a counting argument, so the formulas exist but have no explicit generator.

[The characteristic-2 upper bound](../../CslibFrontier/Logics/Propositional/Algebraic/Nullstellensatz/Tseitin.lean)
shows that `2 ≠ 0` cannot be dropped. In characteristic `2`, the clause polynomials of the parity
constraint at a vertex add up to the charge plus the sum of the incident variables
(`CNF.sum_toBoolPolys_parityOnEq`). By the handshake argument the clause polynomials of the whole
formula add up to `1`, so `CNF.ns_refutableInDegree_tseitinFormula_of_charP_two` gives a
Nullstellensatz refutation whose degree is the largest number of edges at a vertex. The
[tests](../../CslibFrontierTests/ProofComplexity/AlgebraicTseitin.lean) check the following instances:

- On the triangle, the bound rules out degree `0` over `ℚ` and over `ZMod 3`, and over `ZMod 2`
  the formula has a refutation of degree `2`.
- A triangle with an isolated charged vertex has `e(G) = 2` but a refutation of degree `0`, so
  connectivity is needed.
- An expander on `5000000` vertices has `e(G) > 240`. Its Tseitin formula has a refutation of
  degree `120` over `ZMod 2` but none over `ZMod 3`, so `2 ≠ 0` is needed.
- The hard formulas, instantiated over `ZMod 3`.

Run `scripts/build.sh CslibFrontierTests.ProofComplexity.AlgebraicTseitin` to check them. Not yet
formalized: the size–degree trade-off for polynomial calculus, which would turn the degree bound
into an exponential size lower bound for Tseitin formulas on expanders.

## Timestamped f-DAGs and local surgery

Import `CslibFrontier.Logics.Propositional.CSP.Edge.DAGPaths` for finite incidence DAGs, their
surgery and directed-path validity. `CSP.DAG` stores actual variable support, positional
constraint copies paired with timestamps, and occurrence-indexed oriented arcs. Isolated
nodes are retained. `DAG.IsFDAG` bundles base validity and all six conditions of KKR v6,
Definition 32, printed pp. 0:15–0:16: supported incidence, unique use of each original incidence,
variable indegree, distinct timestamps compatible with a topological order, local feasible
pair moves, and the full same-original-constraint no-shortcut condition. Finite rank ties can
be broken into an injective numbering. A two-port move cancels when its ports coincide.

For even delta-matroid constraints, `IsFDAG.delete_earliest_pair` proves Lemma 35 with its
leaf and two-arc degree hypotheses, including exact removal of those arcs. `reroot_earliest`
proves Lemma 37 when the earliest copy has one incoming leaf-root arc; it retains every
unselected outgoing child. Both preserve feasibility and no shortcuts after the pair flip.
Local common parity may be odd. These results operate on positional CSP lists; `EdgeInstance`
connects that extension to the source's distinct-constraint edge model.

`IsFDAG.valid_flip_of_pairedCopies` proves validity when each copy has exactly two incident
arcs, at least one incoming. `DirectedPath.valid_flip`, `valid_take` and `valid_flip_meeting`
specialize this argument to Corollary 36. A path may revisit an original constraint at different
timestamps; copied nodes do not recur. Every variable-ended prefix flip is valid. The bridge
`DirectedPath.isFWalk` additionally requires distinct endpoints and original internal-variable
consistency; these are not hidden in the DAG assumptions.

`IsFDAG.flip_walk_of_no_prefix_extension` proves Lemma 43 for an f-walk disjoint from the DAG's
variables, with the actual `Walk.take`/`snoc` nonextension test against every used arc, regardless
of orientation. Its direct local-exchange proof avoids the source proof's temporary smaller
timestamp and handles timestamp zero. See [DAG tests](../../CslibFrontierTests/EdgeCSPDAG.lean) for repeated
original constraints, exact deletion, extra-child rerooting, meeting paths, odd parity and failed
invariants. The fresh search below derives these DAG hypotheses from its actual execution;
whole-instance contraction/lifting is supplied below; the full planar endpoint remains open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

`CslibFrontier.Logics.Propositional.CSP.Edge.Walk.Operations` supplies disjoint linked-trail
concatenation, trail reversal and f-prefix inheritance. Reversal preserves the underlying
trail, but arbitrary f-walk reversal can fail even with even delta-matroid constraints.
The [operation tests](../../CslibFrontierTests/EdgeCSPWalkOperations.lean) exhibit that failure, overlapping
incidence rejection and why endpoint consistency needs a positive proper prefix.

## Fresh forest search and its three outcomes

Import `CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom` and
`CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Optimality`. `Forest.search sem f` executes
Algorithm 1's chronological forest growth without a supplied improving comparison. Its roots
are the actual defective variables. Expansions are newest first, timestamps count older
expansions from zero, and repeated original constraints retain distinct copied nodes. Each
continuation removes a selected incidence from the finite work list. The result is an exhausted
log, an augmentation meeting, or a blossom meeting; recursive contraction is a separate step.

`search_terminal_isFDAG` proves Lemma 34 for both the actual partial forest and its terminal
pruned graph, using only `EdgeInstance` and base-label validity. No even-delta-matroid premise
is needed here. Pruning removes all current-copy outgoing arcs before inserting the second
incoming port, while retaining the discovered variables as isolated supported nodes.
`scan_isFDAG` provides the corresponding partial-scan invariant.

For even delta-matroid constraints, three fresh-run endpoints use the instance hypotheses and
the actual result equation, deriving forest and event invariants internally:

- `search_exhausted_isOptimalLabeling` proves minimum defect count among all valid labelings.
  Its alternative counting proof combines local `IsEvenDeltaMatroid.card_disagree_le` with
  accounting over distinct occurring variables. It needs no finite universe of variable names,
  comparison labeling or supplied optimality certificate.
- `search_augment_correct` proves that the returned `m.walk` is augmenting, its flip is valid,
  and exactly two defects disappear. Prefix validity comes from the two directed ancestries;
  it does not assume that arbitrary f-walk reversal preserves validity.
- `search_blossom_correct` proves that the actual `m.blossomData` succeeds. Its preparatory flip
  is valid and preserves defect count, and its cycle satisfies `Walk.IsBlossom`. The
  Definition 39 interface includes a closed nonempty incidence trail, defective base,
  consistent internal variables, distinct copied steps and a complete timestamped f-DAG
  with feasibility and no shortcuts.

`Walk.DistinctCopies` requires one timestamp per step and no repeated copied constraint
(position, timestamp). Original constraints may recur at different timestamps.
`Trace.blossom_times_nodup` derives the stronger distinct-timestamp property for both actual
extractor outcomes. This makes explicit the two-arm geometry needed by Lemma 40 when it
invokes Corollary 36. A graph union alone can hide a four-port shared copy. The
[kernel-checked counterexample](../../CslibFrontierTests/EdgeCSPBlossomCopies.lean) satisfies
the former union-only conditions but has an invalid proper prefix; its original instance is
UNSAT while the corresponding table contraction is SAT. A positive actual-search test retains
a repeated original constraint at distinct times. Search programs and native codes are unchanged.

Both least-common-ancestor cases are covered. A variable ancestor is a defective root and needs
no preparation. At a constraint ancestor, the computed root path is flipped and the copied
constraint rerooted, retaining the other child ports. `blossom_metadata` and `blossom_isFDAG`
certify the actual stored pivot and timestamps. The preparation proof uses chronological prefix
transfer followed by Lemma 37; it is an alternative to the paper's repeated deletions.

These statements follow KKR v6, Algorithm 1 (printed p. 0:10), Lemma 34 (pp. 0:15–0:16),
Proposition 38 (p. 0:18), Definition 39/Lemma 41 (pp. 0:19–0:20), and Lemma 45
(pp. 0:22–0:23). Variables require only decidable equality; local common parity may be odd.
The reusable `Walk.Subpath`, `Walk.Visits` and `DAGPaths.Preparation` APIs support the actual
prefix/suffix arguments. `Walk.nodup_edges_snoc` is now public and used by `IsWalk.snoc`.
Import `CslibFrontier.Foundations.Data.BitString.DeltaMatroid.ExchangeBound` separately to use
the local disagreement-count lemma directly.

[Forest execution tests](../../CslibFrontierTests/EdgeCSPForest.lean),
[terminal tests](../../CslibFrontierTests/EdgeCSPForestTerminal.lean),
[event tests](../../CslibFrontierTests/EdgeCSPForestEvents.lean) and
[optimality tests](../../CslibFrontierTests/EdgeCSPForestOptimality.lean) cover both ancestor cases,
nonempty preparation, repeated constraints, timestamp zero, odd parity and sparse binary names.
The exhausted example with a connected feasible-pair graph still has two unavoidable defects.
These mathematical results compose with the native compiler and whole-instance contraction/lifting
below, followed by the complete native edge solver. The full planar dichotomy remains open;
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091) stays open.

## Native fresh forest search

Import `CslibFrontier.Computability.PolyTime.CSP.Edge.Forest.Spec` for the program, native
certificate, exact bridge and semantic specification. The namespace is
`Cslib.Complexity.CSP.EdgeForest`. `Input` contains an explicit `CSP Table Nat` and one
occurrence-bit buffer in constraint-then-port order. `encInput` frames the CSP before the
Boolean list. Original names, table arities and public output occurrence indices are binary;
internal work records use unary constraint/scope positions. Every clock traverses actual lists.

`computableInPolyTime_run` is an ordinary native polynomial-time certificate on the complete
encoded input, including malformed tables and arbitrary buffers. The outer clock is the actual
occurrence count plus one; stopped states freeze the first event. The full log remains in its
original encoded field, and final output conversion happens once after iteration.

`run_eq` requires only exact buffer width and identifies the complete output with the existing
`Forest.search`. `run_eq_none_iff` shows that width mismatch is the only rejection: `none` is not
an unsatisfiability answer. `code` and `decode` retain original roots, newest-first expansions,
partial meetings and implicit timestamps; external out-of-range indices are rejected.
`decode_run` recovers the exact typed source result from a correctly sized buffer. These
representation theorems assume no edge condition, validity or evenness.

`run_spec` adds the edge-instance condition, valid initial labels and even delta-matroid
constraints. It transfers the three mathematical guarantees to the actual decoded native result:
optimality, valid two-defect augmentation, or valid defect-count-preserving blossom preparation.
Decoded event tags alone establish none of these semantic claims. There is no improving comparison
input, contraction step or recursive solver in this routine.

`PolyTime.CSP.Edge.Buffer` holds the shared enumeration/label operations and certificates;
the existing `EdgeAugmenting` namespace and public imports remain available. The
[native forest tests](../../CslibFrontierTests/EdgeCSPForestNative.lean) cover all three outcomes,
partial meetings, repeated original constraints, scan order, malformed tables, width rejection,
invalid indices and names up to `2^250`. An end-to-end client derives a valid zero-defect labeling
from the actual decoded augmentation. The existing native augmentation regression suite remains
unchanged. The complete recursive solver appears below; geometric realization/recognition
and the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Whole-instance blossom contraction and lifting

Import `CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Optimality` for executable projection,
lifting and optimality transfer, and `.Size` for the recursion resource and row bounds.
All constructors use the original `CSP Table Nat` and positional occurrence labels.
`Blossom.contract f (Blossom.internal w)` processes each distinct touched original
constraint once, gathering **all** its internal ports even when the cycle visits that
constraint repeatedly. Outside ports keep their order. Untouched and nullary constraints
remain, and one fresh connector per touched constraint joins a new exactly-one relation.
Names come from an occurrence maximum plus constraint indices, without scanning a binary-name
interval. `valid_reference`, `edge_contract` and `even_contract` prove the required
model invariants. The central reference row is genuinely one-hot; all-zero connector labels
would fail exactly-one. Its single new connector defect replaces the blossom's old defect.

`projectAugmentation_spec` maps a genuine original augmentation to a valid contracted
improvement. `isOptimal_of_reference` proves that an optimal contracted reference implies
optimality of the prepared original labeling. Conversely, `liftComparison_spec` executes
`liftComparison f w g` for **any** improving valid contracted labeling `g`. It derives
an augmenting walk away from the new connector defect, restores the outside prefix, and
uses an accepted contracted row to construct the original exchange and shortest exit.
The result is valid and has exactly two fewer original defects. Outside values may change;
no comparison agreement, global model, solver or lifting provider is assumed. This is strict
improvement transfer, not equality with an arbitrarily better comparison's defect count.

For `b` distinct internal variables and `r` distinct touched original constraints,
`numVars(new)+b = numVars(old)+r`, `r ≤ b`, and positive-scope constraint count increases
by one. Thus `contractionMeasure_contract_lt` strictly decreases
`2*numVars−positiveCount`, including `r=b`; variable count alone need not decrease.
Nullaries do not contribute to `positiveCount`. Old row counts do not increase; the new
central relation has `r` rows of width `r`, so its Boolean row data is quadratic in `r`.
These are termination/storage facts; the complete native solver below supplies the runtime theorem.

The construction maps KKR v6 §5.3 (printed pp. 12–13), Observation 26/Corollary 27,
Definition 39/Lemma 40 and Lemmas 42–44 (pp. 19–22). The copied-step distinction is explicit;
the cut/completion attachment proof and finite bookkeeping are original alternatives.
[Contraction tests](../../CslibFrontierTests/EdgeCSPBlossomContraction.lean) and
[lifting tests](../../CslibFrontierTests/EdgeCSPBlossomLifting.lean) execute nonempty preparation,
repeated original constraints, grouped ports, honest one-hot references, `r=b` accounting,
sparse names up to `2^250`, forward projection and an actual optimal comparison whose outside
values change. The complete native solver follows. Recognition/geometric correspondence,
planar hardness and full
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091) remain open.

## Complete native even edge-CSP solver

Import `CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Endpoint`. In
`Cslib.Complexity.CSP.EdgeSolver`, `optimize` returns a finite minimum-defect occurrence buffer,
`solve` returns a satisfying buffer, and `decideSAT` is the total Boolean decision routine.
`optimize_spec` proves optimality; `solve_spec` proves validity, exact original occurrence width
and zero defects. The buffers use the existing `EdgeAugmenting.labeling`, with one bit for every
actual constraint/scope position.

`evenEdgeSAT_mem_P` proves ordinary native P membership using `encCSP encTable encNat`.
Its decision set is precisely the conjunction of `EdgeInstance`, actual
`EdgeInstance.EvenConstraints Table.sem`, and CSP satisfiability.
`decideSAT_eq_true_full` states that equivalence for every raw input. No model, optimizer,
comparison labeling, lifting provider or runtime certificate is supplied by the caller.

The internal `checkModel` scans stored rows and their actual coordinates to verify scope widths,
well-formed nonempty relations, common parity and symmetric exchange. Every occurring name must
appear twice in distinct constraints, and each scope must be repetition-free. Local parity may
be odd and may differ between constraints. Duplicate rows and duplicate constraints retain their
positions. Empty CSPs and true nullaries are included; empty/false relations, malformed rows,
wrong arities, repeated scope names and non-even relations are rejected. Thus `optimize = none`
means rejection outside the model. An accepted but unsatisfiable model still has an optimal
buffer; `solve = none` and `decideSAT = false` additionally cover that case.

One improvement performs a fresh search, then returns an augmentation, transfers an optimum,
or prepares and contracts one blossom. A recursive child returns one improvement or an optimum;
an improvement is lifted and returned immediately. At most `2*numVars` contractions occur per
improvement, followed by at most `numVars+1` outer rounds. The proof uses the strict
`2*numVars−positiveCount` measure, including contractions that preserve variable count.

`computableInPolyTime_optimize`, `computableInPolyTime_solve` and
`computableInPolyTime_decideSAT` cover every raw input. The finite native stack agrees exactly
with the semantic algorithm via `Program.optimize_eq` and `Program.decideSAT_eq`. Resource bounds
include complete stored rows, binary arities/names/positions, copied walks, parent frames,
status tags and clocks, including malformed inputs. Work loops traverse actual lists; neither a
binary variable name nor a declared arity funds enumeration. Old row counts do not increase;
the quadratic central exactly-one data and all stack frames are included in the polynomial bound.

For lifting certificates, import `CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.LiftingPolyTime`.
`NativeLifting.encLiftResult` names their optional occurrence-buffer encoding: `none` is empty;
`some bits` starts with `true`, then concatenates the framed one-bit Boolean encodings in
buffer order. The abbreviation unfolds to `encOption (encList encBool)` without changing bytes.

This completes the explicit-table edge algorithm of KKR v6, Theorem 21 (printed p. 8), Algorithm 1
(p. 10), Theorem 24 and §5.3 (pp. 11–13), using the proved search, contraction and lifting layers.
The one-improvement recursion organization and full framed-bit bookkeeping are original.
The shared `EdgeAugmenting.buffer_eq` now lives beside `labeling_map` in `Edge.Buffer`;
`recordAt_index`, `finish_eq` and `EdgeForest.poly_binaryIndex` are public for reuse.
Forest input projections use the generated encoding rules, including in the solver certificates.

[Solver tests](../../CslibFrontierTests/EdgeCSPSolver.lean) give complete ordinary-import clients,
including SAT/UNSAT units, nonempty blossom preparation, repeated original constraint copies,
changed outside comparison values, `r=b`, multiple improvements, every model guard and sparse
names up to `2^250`. [Buffer-only tests](../../CslibFrontierTests/EdgeCSPSolverBuffer.lean) check the
shared width bridge. The guide checks the native P endpoint, all-raw solver certificate,
optimality theorem and concrete decisions. Geometric realization/recognition, ordered planar
hardness transfer and final dichotomy assembly remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Finite crossover gadget semantics

Import `CslibFrontier.Logics.Propositional.CSP.Planar.Crossover` for Dvořák–Kupec, ICALP 2015,
§4, printed pp. 440–441, Figure 1. `BitString.cross` equates opposite ports in cyclic order;
`nearCross` additionally permits `0001` and `1110`. `IsStandardizedInconsistent` requires
self-complementarity, inclusion of CROSS, and the source's upper restriction. Its exact
classification has eight shapes, selected by three optional complementary tuple pairs.

The actual four-constraint `Crossover.figureOneAStandardized` is a `PPGadget` with three
auxiliaries. Its target is NEAR-CROSS exactly when the input relation contains `0001` or
`0010`, and CROSS otherwise. The actual two-constraint `Crossover.figureOneB` uses one auxiliary
and defines CROSS from NEAR-CROSS. Numbered scope positions match the source's diagram;
width-guarded interpretations reject malformed scopes. [Crossover clients](../../CslibFrontierTests/PlanarCrossover.lean)
check every standardized shape, both first-gadget outcomes, explicit witnesses and rejected
boundary tuples, while retaining the existing CNF crossover tests.

These Figure 1 results concern finite relation semantics. Geometric realization and substitution,
a hardness theorem and a new native runtime certificate remain part of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Ordered normalization from a cyclic exchange failure

Import `CslibFrontier.Logics.Propositional.CSP.Planar.Normalization`. For any arity `n`,
`Normalization.exists_construction` takes a nonempty self-complementary relation
`R : Set (Fin n → Bool)` whose `cyclicDifferenceRelation R` is not an even delta-matroid.
It proves `4 ≤ n` and supplies a `Construction R`. Nonemptiness is essential: failure caused
solely by an empty relation supplies no exchange witness. This is an original reconstruction
of the combinatorial argument omitted from Dvořák–Kupec, ICALP 2015, §4, printed p. 440,
Lemma 6; it does not yet prove that lemma's planar-expressibility conclusion.

The construction chooses a feasible twist and a cyclic starting port, then records a finite
`Program n 4`. The only reductions are adjacent identification, including the last-to-first
edge, and a cap at arity at least six that identifies old ports 1 and 3 and hides old port 2.
The latter retains free order `0,1,4,…`. Adjacent identification conditions the removed cyclic
difference to zero; the cap conditions old differences 1 and 2 to agree. The exact formulas
in `BitString.CyclicDifference.Boundary` rule out new forbidden pairs during the descent.
Cyclic rotations preserve orientation; no arbitrary port permutation is used.

For coordinate proofs, use `capDifferencePort_eq_zero_iff`, `capDifferencePort_ne_one`,
`capDifferencePort_ne_two` and `three_le_val_capDifferencePort`. These state that the retained
differences preserve zero, omit both hidden coordinates, and send every nonzero input to an
index at least three. Clients can use these facts
without unfolding the coordinate map.

`Construction.target` is standardized in the final four-port order. `Construction.gadget`
executes the trace on an actual `PPGadget` over two symbols: the original `R` and binary
disequality. Its initial body contains one `R` literal and one or two disequalities per port.
Subsequent steps only relabel scopes; every cap adds one fresh auxiliary. No constants or
equality symbol are added. `Construction.body_bounds` gives at most `1+2n` constraints and
`5n` total scope occurrences; `Construction.numAux_bound` gives at most `3n-4` allocated
auxiliaries, including unused labels. `Program.reductions_bound` counts nonrotation operations,
not the length of an arbitrary trace.

`CSP.PrimitivePositive.Operations` supplies the reusable `PPGadget.relabelFree` and
`PPGadget.substitute` operations, preserving exact scope widths and existential semantics.
The [normalization tests](../../CslibFrontierTests/PlanarNormalization.lean) exercise failed-exchange
families at arities 6, 8 and 12, repeated caps, a feasible-quartet finish, proper-support
compression, rotation, wraparound deletion, actual auxiliary witnesses and empty/nullary guards.
The guide composes the construction with its gadget and size bounds using ordinary imports.

These are combinatorial and finite-semantic bounds. Relation decisions and a chosen construction
are fixed-relation data; no uniform native runtime or binary encoded-size bound is asserted.
Geometric realization of the recorded operations, ordered planar substitution, hardness and
completion of the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Original-language gadgets for the nonselfdual branch

Import `CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree.Gadget`.
`NonSelfDual.exists_oneHotGadget` gives an actual `PPGadget arity sem
(BitString.oneHotRelation (Fin 3))` when the language has none of the six common Schaefer
polymorphisms and unary complement is also not a common polymorphism. Different language
relations may witness these failures; their arities are unrestricted. Pins and disequality
are constructed internally, rather than added to the alphabet.
`RelationMinor.exists_disequalityGadget` needs only absence of the six Schaefer operations,
so it also applies to self-complementary languages.

`RelationMinor.Construction` records finite ordered recipes. Its atom, projection, adjacent
equality/disequality deletion, cofactor, single-coordinate flip, cyclic rotation and binary
intersection constructors retain their intermediate relations and enabling constructions.
`Construction.gadget` executes this tree over the original alphabet. The reusable
`PPGadget.atom`, `conj`, `retarget` and port operations preserve exact scope widths and
existential semantics. Conjunction appends bodies with disjoint auxiliary blocks, including
when the same gadget is used several times. `NonSelfDual.triangleGadget` appends the ternary
body and three NAND bodies on ports `(0,1)`, `(1,2)`, `(2,0)`, with fresh auxiliaries for
each occurrence. Survivor order is retained by projection; a cyclic rotation changes only
the starting port.

The constants descent follows Dvořák–Kupec, ICALP 2015, §2, printed pp. 437–438, Lemma 3.
The arbitrary-arity parity and majority minor proofs reconstruct the argument omitted from
Lemma 4, printed pp. 438–439; they are identified as original reconstructions. Unary pin
relations are distinct from unary constant operations. The [minor and triangle tests](../../CslibFrontierTests/PlanarNonSelfDual.lean),
[rotation tests](../../CslibFrontierTests/PlanarNonSelfDualRotation.lean) and
[interpreter tests](../../CslibFrontierTests/PlanarConstructionGadget.lean) cover actual witnesses,
rejection, fresh auxiliaries, nullary atoms and malformed widths. In particular, the interpreter
tests derive the gadgets from a single one-in-three symbol without primitive pins or disequality.

These results prove finite primitive-positive semantics. The selected witnesses are fixed-language
data; no uniform preprocessing cost is asserted. The recorded recipes and concrete bodies support
subsequent geometric proofs, but do not establish ordered planar substitution, a native reduction
or planar hardness. Those obligations and the full planar dichotomy remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Three resolution representations

| Representation | What it supplies | Cost |
|---|---|---|
| [CNF.Derives](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution.lean#L100) | Inductive proposition generated by input clauses and pivot resolution | No explicit size. |
| [CNF.IsProof](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Proof.lean#L107) | A finite ordered list whose lines are justified by inputs or earlier lines | Number of lines; maximum distinct-literal width. |
| [CNF.Derivation](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TreeLike.lean#L85) | Type-valued tree with input leaves and binary resolution nodes | Tree-node count, width and depth. |

The resolvent removes opposite pivot literals and concatenates the remaining lists. There is no primitive weakening rule; list-level subtleties are handled by lemmas. Soundness and refutation completeness relate the derivability proposition to unsatisfiability. Explicit proof representations then support quantitative theorems.

A tree-like derivation yields a decision tree that finds a clause falsified by the input assignment. Conversely, a suitable clause-search decision tree yields a resolution refutation with at most `2 leaves - 1` nodes. Sharing in a line proof need not survive this tree conversion, which explains why tree-like and general resolution complexity must remain separate.

## Major lower bounds and interpolation

[The pigeonhole development](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Pigeonhole.lean) formalizes Haken's exponential lower bound for `PHP^(n+1)_n`, using a simplified Beame–Pitassi-style argument. Its explicit finite endpoint gives at least `2^floor(n/24)` proof lines. Source documentation explains the critical-assignment measure and greedy restriction sequence. The result also lower-bounds tree-like resolution through the line/tree bridge.

[The tree-like pigeonhole module](../../CslibFrontier/Logics/Propositional/Resolution/TreeLikePigeonhole.lean) proves a much stronger bound for tree-like refutations: `2 ^ Ω(n log n)`, for every number of pigeons `m > n`. This is Theorem 2 of Beyersdorff, Galesi and Lauria ([beyersdorffgalesilauria10]), which gives a simpler proof of the lower bound in Dantchev and Riis's result that tree-like size is `2 ^ Θ(n log n)` for all `m > n`. Import `CslibFrontier.Logics.Propositional.Resolution.TreeLikePigeonhole`. `CNF.Derivation.pow_le_size_pigeonhole h` gives at least `(n + 1 - h) ^ h` nodes for every `h`, and `pow_half_le_size_pigeonhole` specializes it to BGL's `(n / 2 + 1) ^ (n / 2)`. `CNF.pow_lt_two_mul_leafCount_pigeonhole` turns the bound into more than `(n + 1 - h) ^ h / 2` leaves for DPLL search trees. Only the explicit bound for each `h` is formalized; the asymptotic `2 ^ Ω(n log n)` is not stated in Lean. The parameter `h` mildly generalizes BGL's fixed threshold `n / 2` and, informally, gives `n ^ ((1 - o(1)) n)` for `h ≈ n - n / ln n`.

The method lives in [the Prover–Delayer module](../../CslibFrontier/Logics/Propositional/Resolution/ProverDelayer.lean). `Clause.FalsifiedBy ρ c` says that a partial assignment `ρ : V → Option Bool` sets every literal of `c` to false. `CNF.Derivation.potential_le_size` takes a potential `μ` that splits at every unset variable (`μ ρ ≤ μ ρ[v ↦ 0] + μ ρ[v ↦ 1]`) and is at most `1` where a clause of the formula is falsified. It then bounds every tree-like derivation of a clause falsified by `ρ` below by `μ ρ` nodes. This is BGL's Theorem 1 in potential form, with no explicit game: a Delayer strategy that scores `p` points gives such a potential with value `⌈2 ^ p⌉` at the empty assignment.

The [checked examples](../../CslibFrontierTests/ProofComplexity/TreeLikePigeonhole.lean) cover a falsified and a non-falsified clause, a two-valued potential for `x ∧ ¬x`, and a five-node refutation of `PHP^2_1`. They instantiate the bound for `PHP^5_4` and `PHP^100_4`, show that `h = 7` beats `h = n / 2` at `n = 10`, and compare with Haken's bound at `n = 48`. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.TreeLikePigeonhole`.

[The Ben-Sasson–Wigderson tradeoff](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/SizeWidth.lean) says that a CNF of initial width k on N variables with an s-line refutation has a refutation of width at most `k + 2 sqrt(2 N log s) + 2`. The contrapositive form yields an exponential line lower bound from a width lower bound. These constants and the logarithm/real square-root convention are explicit in the theorem.

[The Tseitin-expander result](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) combines a graph-expansion width lower bound with that tradeoff. It gives a family of linear-variable, constant-width unsatisfiable CNFs requiring exponentially many proof lines. The expansion witnesses are obtained nonconstructively from counting, and the source explicitly says so: existence of a hard family is proved, while an efficient explicit expander/formula generator is not supplied by that endpoint.

[The cut space of a multigraph](../../CslibFrontier/Foundations/Combinatorics/Multigraph/CutSpace.lean) holds the edge-cut algebra that Tseitin lower bounds beyond resolution (polynomial calculus, SOS) are meant to use. Import `CslibFrontier.Foundations.Combinatorics.Multigraph.CutSpace`. `Multigraph.edgeCut_symmDiff` sends a symmetric difference of vertex sets to the symmetric difference of their edge cuts, and `Multigraph.edgeCut_singleton` identifies the cut of one vertex with its edges other than self-loops. On a connected multigraph, `Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty` says that only `∅` and the set of all vertices have empty cuts. `Multigraph.three_mul_card_lt_of_card_edgeCut_lt` is the expansion dichotomy: a set of at most two thirds of the vertices that fewer than `e(G)` edges leave has fewer than a third of them. The [checked examples](../../CslibFrontierTests/Foundations/Combinatorics/Multigraph/CutSpace.lean) show that connectivity and the two-thirds hypothesis cannot be dropped; check them with `scripts/build.sh CslibFrontierTests.Foundations.Combinatorics.Multigraph.CutSpace`.

Interpolation modules extract circuits separating the two sides of a refuted conjunction. Monotone extraction supports clique/coloring lower-bound applications, and a separate polynomial-time file addresses encoded extraction. The distinction between semantic existence of an interpolant and a native efficient extraction algorithm follows the same design pattern as circuits and finite-model logic. See [interpolation](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation.lean), [monotone extraction](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/MonotoneExtraction.lean) and [native extraction](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/PolyTime.lean).

[Semantic derivations](../../CslibFrontier/Logics/Propositional/SemanticDerivation.lean) formalize Krajíček's communication route to interpolation, which is not tied to one proof system. Import `CslibFrontier.Logics.Propositional.SemanticDerivation`. A line is a set of assignments, and `IsSemanticRefutation (initSets 𝒜 ℬ) D` says that each of the `k` lines of `D` is either a cylinder over an initial set, everything, or contains the intersection of two earlier lines, and that some line is `∅`. `IsSemanticRefutation.exists_dagProtocol` turns such a refutation into a dag-like Karchmer–Wigderson protocol with `k` inner nodes and communication `2 t`. This requires two per-line costs to be at most `t`: deciding whether the mixed assignment `(v, q, r)` lies in each line, and finding a coordinate at each `𝒜`-cylinder. For shared variables of type `Fin n`, `exists_circuit` and `exists_monotone_circuit` then give a separating circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates. The `_of_commComplexity_le` forms state this for lines with Krajíček's `CC` and `MCC_U` at most `t`; the monotone form assumes the models of `𝒜` are upward closed. This sharpens the bounds of Theorem 5.1, `(k + 2 n) · 2 ^ O(t)` and, in the monotone case, `(k + n) · 2 ^ O(t)`: the `2 n` answer nodes of the source's protocol are leaves here and cost nothing. `lt_of_forall_lt_size` is the transfer to line lower bounds. Only the monotone case for the `𝒜` side is stated. Cutting planes is the first proof-system client (see below); resolution refutations are not yet translated into semantic refutations. The [checked examples](../../CslibFrontierTests/ProofComplexity/SemanticDerivation.lean) apply every form to a three-line refutation of `x₀ = 1` against `x₀ = 0`; check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.SemanticDerivation`.

## Clause space

Import `CslibFrontier.Logics.Propositional.Resolution.SpaceWidth` for the definitions and the inequality, `CslibFrontier.Logics.Propositional.Resolution.TseitinSpace` for the Tseitin corollaries, `CslibFrontier.Logics.Propositional.Resolution.TreeLikeSpace` for tree-like refutations and DPLL trees, `CslibFrontier.Logics.Propositional.Resolution.PigeonholeSpace` for Duplicator strategies and the extended pigeonhole bounds, or `CslibFrontier.Logics.Propositional.Resolution.WidePigeonholeSpace` for the exact clause space of the wide pigeonhole formula.

[Configuration-style resolution](../../CslibFrontier/Logics/Propositional/Resolution/Space.lean) follows Esteban and Torán. It keeps a `Finset` of clauses in memory, and each move (`ConfigMove`) changes it by one of three rules (`CNF.ConfigStep`): download a clause of the formula, add the resolvent of two clauses in memory, or erase a clause. The resolution rule is that of `CNF.IsProof`, with no weakening. `CNF.configLTS φ s` is the cslib `LTS` of these moves, restricted to configurations of at most `s` clauses. It follows the same pattern as the pebbling library's `Cslib.Pebbling.blackPebbleGame`.

`CNF.RefutableInSpace φ s` holds when some `MTr` run from `∅` reaches a configuration containing `[]`. Space counts distinct clauses, and time (the number of moves) is not bounded. Clauses are lists, but this does not change the least space compared with clauses as sets: mapping clauses to their literal sets never increases space, and a refutation on sets lifts by fixing one list per set. The module proves the basic properties:

- soundness: `RefutableInSpace.not_satisfiable`;
- space is at most size: `RefutableInSize.refutableInSpace`;
- completeness: `exists_refutableInSpace_iff_not_satisfiable`;
- `RefutableInSpace.three_le`: space is at least `3` unless `[] ∈ φ`.

[The space–width module](../../CslibFrontier/Logics/Propositional/Resolution/SpaceWidth.lean) proves the Atserias–Dalmau inequality (their Theorem 3) in the form of Theorem 1 of Filmus, Lauria, Mikša, Nordström and Vinyals (STACS 2014), whose constant `s + k - 3` it uses. That paper labels the bound "Theorem 1 ([2])", attributing it to Atserias and Dalmau's journal paper, whose own statement is not quoted here because its symbols do not extract. `RefutableInSpace.refutableInWidth` says that if every clause has width at most `k`, clause space `s` gives a refutation of width `s + k - 3`, with truncated subtraction. Unlike that paper, the theorem does not assume `[] ∉ φ`. The contrapositive `RefutableInSpace.add_four_le` turns a width lower bound `¬ RefutableInWidth w` into the space bound `w + 4 ≤ s + k`.

The proof works for any Duplicator strategy. `DuplicatorStrategy.add_three_le` says that if Duplicator wins the existential `p`-pebble game on a formula whose clauses have width at most `k`, every refutation needs clause space `s` with `p + 3 ≤ s + k`. This is their Lemma 5 with the constant that yields Filmus et al.'s; the source's own constant is not quoted. `add_four_le` applies it to the strategy that Atserias and Dalmau's Lemma 2 builds from `¬ RefutableInWidth w` (below), when no clause has width `w + 1`. Otherwise `w < k`, and `RefutableInSpace.three_le` is enough.

[The existential pebble module](../../CslibFrontier/Logics/Propositional/Resolution/ExistentialPebble.lean) exports the game and its characterization of width. Import `CslibFrontier.Logics.Propositional.Resolution.ExistentialPebble`. A partial assignment is a total assignment `σ` read on a finite set `d`, and `CNF.Falsifies σ d c` says that every literal of `c` is on a variable of `d` and false under `σ`. `CNF.DuplicatorStrategy φ k` is Atserias and Dalmau's Definition 2: a nonempty family of such assignments on at most `k` variables that falsify no clause of `φ`, closed under restriction, and extendable to any variable from fewer than `k` variables. `DuplicatorStrategy.not_refutableInWidth` is their Lemma 3 in the library's width convention: a strategy with `w + 1` pebbles rules out `RefutableInWidth w`. Conversely, `DuplicatorStrategy.ofNotRefutableInWidth` is their Lemma 2: if no clause has width exactly `w + 1` and there is no refutation of width `w`, the partial assignments on at most `w + 1` variables that falsify no clause derivable within width `w` form a strategy with `w + 1` pebbles. Wider clauses cannot be falsified on `w + 1` variables. Together they give their Theorem 2 as `DuplicatorStrategy.nonempty_iff_not_refutableInWidth`, for formulas without clauses of width `w + 1`. Those clauses must be excluded: `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀ ∧ ¬x₁ ∧ ¬x₂` has no refutation of width `2`, but Spoiler wins with `3` pebbles. `DuplicatorStrategy.exists_extend_union` extends a position on `d` to `d ∪ e` when `|d| + |e|` is at most the number of pebbles. The source's side conditions and pebble counts are not quoted, because its symbols do not extract. The game has nothing to do with the black pebble game of `CslibFrontier/Computability/Pebbling`.

[The pigeonhole space module](../../CslibFrontier/Logics/Propositional/Resolution/PigeonholeSpace.lean) applies it to Atserias and Dalmau's Section 5 example. Import `CslibFrontier.Logics.Propositional.Resolution.PigeonholeSpace`.

- [The extended pigeonhole formula](../../CslibFrontier/Logics/Propositional/Pigeonhole/Extension.lean) `CNF.pigeonholeExt m n` (`EPHP^m_n`) replaces each width-`n` pigeon clause of `PHP^m_n` with a chain of start, step and stop clauses of width at most `3`. The chain runs through variables "pigeon `i` sits in a hole `≥ j`". `satisfiable_pigeonholeExt_iff` says it is satisfiable exactly when `m ≤ n`.
- `CNF.pigeonholeExtStrategy m n` is Duplicator's strategy on `EPHP^m_{n+1}` with `n + 1` pebbles: the partial assignments that agree with a placement of pigeons that is injective on the pebbled pigeons.
- So with `n + 1` holes there is no refutation of width `n` (`not_refutableInWidth_pigeonholeExt`). Stated per hole count, every refutation of `EPHP^m_n` has width at least `n` (`le_of_refutableInWidth_pigeonholeExt`) and clause space at least `n` (`le_of_refutableInSpace_pigeonholeExt`, through `RefutableInSpace.add_four_le` with `k = 3`). The number of pigeons is arbitrary.

The mathematical symbols of the available copy of Atserias and Dalmau's paper do not extract. So neither their exact clauses nor the pebble count of their Lemma 6 is quoted; the encoding, the strategy and these constants are ours. Alekhnovich, Ben-Sasson, Razborov and Wigderson also proved pigeonhole space lower bounds; their paper was not inspected.

[The wide pigeonhole module](../../CslibFrontier/Logics/Propositional/Resolution/WidePigeonholeSpace.lean) gives the exact clause space of `PHP^m_n` itself. Import `CslibFrontier.Logics.Propositional.Resolution.WidePigeonholeSpace`. [Torán's survey][toran04] (Section 4) states resolution space exactly `n + 1` for `m > n`, whatever the number of pigeons. It credits this to Torán's CSL 1999 paper, which was not inspected, so the proofs are reconstructions. The survey's numbers are for a pebble game that may shift a pebble from a premise to the resolvent. Both bounds here are proved directly for `CNF.configLTS`, which keeps both premises, and the value is `n + 2`, one extra clause:

- `CNF.add_two_le_of_refutableInSpace_pigeonhole`: for `0 < n`, every refutation in clause space `s` has `n + 2 ≤ s`. The proof is an invariant on configurations: they are implied by a partial matching (`Cslib.Circuits.BipartiteMatching.IsMatching`; every matching containing it satisfies each clause) except perhaps for one pigeon clause. A clause implied by a matching is implied by at most one of its pairs, so with at most `n` clauses a hole is free for the exceptional pigeon clause, and no matching implies `[]`.
- `CNF.refutableInSpace_pigeonhole`: for `n < m`, a refutation in clause space `n + 2`. An explicit DPLL tree queries each pigeon in the free holes, then the later pigeons in the hole found. It has rank at most `n`, and `DecisionTree.FindsFalsifiedClause.refutableInSpace` turns a DPLL tree of rank `r` into clause space `r + 2`. This uses the rank bound of `DecisionTree.FindsFalsifiedClause.exists_derivation_rank_le`.
- `CNF.refutableInSpace_pigeonhole_iff` combines the two for `0 < n < m`.

The clauses of `PHP^m_n` have width `n`, so the Atserias–Dalmau inequality gives nothing for it. With no holes, `PHP^m_0` contains the empty clause for `m ≥ 1` and is refutable in clause space `1`. The [checked examples](../../CslibFrontierTests/ProofComplexity/WidePigeonholeSpace.lean) give clause space exactly `3` for `PHP^2_1`, exactly `7` for `PHP^1000_5`, and exactly `5` for every `PHP^m_3` with `m > 3`. They also refute `PHP^1_0` in clause space `1` and `x ∧ ¬x` from a rank-`1` DPLL tree. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.WidePigeonholeSpace`.

[The Tseitin module](../../CslibFrontier/Logics/Propositional/Resolution/TseitinSpace.lean) combines this with the width bound of Ben-Sasson and Wigderson:

- `Tseitin.minBalancedCut_le_of_refutableInSpace` gives `e(G) ≤ s + k - 3` on a connected multigraph whose vertices have at most `k` non-loop edges;
- `Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace` gives `h(G) |V| / 3 + 3 ≤ s + |D|` on a rotation map with `h(G) > 0`;
- `CNF.exists_forall_refutableInSpace_le` is a family with explicit constants. For `n ≥ 4392000` it has at most `120 n` variables, `2 ^ 120 · n` clauses of width at most `120`, and every refutation in clause space `s` has `n ≤ 36000 s`. It shares its setup with the size family of the Tseitin-expander module through `Tseitin.exists_expander_tseitinFormula`. That lemma gives the Tseitin formula of the `120`-regular expander on `n ≥ 2` vertices with its explicit constants: connectivity, degree at most `120`, `e(G) ≥ n / 18000`, at most `120 n` variables and `2 ^ 120 · n` clauses, clauses with at most `120` literals (so of width at most `120`), and unsatisfiability. Its graph, and that of the sum-of-squares family below, comes from `Multigraph.exists_expander` in [the multigraph-expander module](../../CslibFrontier/Foundations/Combinatorics/Expander/MultigraphExistence.lean): a connected multigraph on `Fin n` with at most `120 n` edges, degree at most `120` and `e(G) ≥ n / 18000`.

As with the size bound, the expanders come from a counting argument.

[The tree-like module](../../CslibFrontier/Logics/Propositional/Resolution/TreeLikeSpace.lean) proves Esteban and Torán's bound: clause space is at most logarithmic in tree-like size. The statement is taken from Torán's survey (Bulletin of the EATCS 83, 2004, Theorem 9), which states `tree-size(F) ≥ 2 ^ space(F) - 1`. The original paper was not inspected. The survey's pebble game (Definition 7, identified with its space by Lemma 8) lets an inference shift a pebble from a premise to the resolvent, so its space is at most one less than clause space here. `CNF.configLTS` keeps both premises, so every bound here is one larger:

- `Derivation.strahler` is the Horton–Strahler number of a tree-like derivation, the height of the largest complete binary tree embedded in it. It is the Ehrenfeucht–Haussler rank `Cslib.DecisionTree.rank` of the derivation's decision tree `Derivation.toDecisionTree` (`Derivation.strahler_eq_rank_toDecisionTree`). `Derivation.two_pow_strahler_add_one_le` gives `2 ^ (r + 1) ≤ S + 1` for a derivation of `S` nodes, from `DecisionTree.two_pow_rank_le_leafCount` (a tree of rank `r` has at least `2 ^ r` leaves).
- `Derivation.refutableInSpace` gives clause space `r + 2`: derive the premise of larger number first and keep it. This matches the black pebbling price `h + 2` of the complete binary tree of height `h ≥ 1` in `CslibFrontier/Computability/Pebbling/BinaryTree.lean`.
- `DecisionTree.FindsFalsifiedClause.refutableInSpace` gives clause space `r + 2` from a DPLL tree of Ehrenfeucht–Haussler rank `r`, through `DecisionTree.FindsFalsifiedClause.exists_derivation_rank_le` (in `Resolution/TreeLike.lean`): the tree-like refutation built from a DPLL tree has decision tree of rank at most that of the DPLL tree.
- `Derivation.refutableInSpace_log` gives clause space `log₂ (S + 1) + 1`. Its contrapositive, `Derivation.two_pow_le_size_add_one`, turns `¬ RefutableInSpace s` into `2 ^ s ≤ S + 1`; `x ∧ ¬x` attains it.
- `CNF.refutableInSpace_of_not_satisfiable` refutes every unsatisfiable formula on `n` variables in clause space `n + 2`, the survey's `n + 1`. It splits on a variable (`CNF.exists_derivation_strahler_le`), lifting tree-like refutations of the restrictions with `Derivation.exists_of_restrict`.

The [checked examples](../../CslibFrontierTests/ProofComplexity/Space.lean) refute `x ∧ ¬x` in space `3` and show that space `2` is impossible. They also give a five-line refutation that erasure keeps in space `3`, and a formula with a width-`3` clause on which the inequality is attained: `k = s = 3`, width `3` and not `2`. On the same formula Spoiler wins with `3` pebbles, so Lemma 2 needs its width hypothesis, while its width-`3` clause does not prevent the `2`-pebble strategy that Lemma 2 gives from the absence of width-`1` refutations. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.Space`. The [tree-like examples](../../CslibFrontierTests/ProofComplexity/TreeLikeSpace.lean) compute Strahler numbers, show that `x ∧ ¬x` attains both the Esteban–Torán bound and the bound `n + 2`, and turn the Tseitin space bound into tree-like size at least `2 ^ 121 - 1`. On a unit-propagation chain with a 7-node refutation, the Strahler bound gives the optimal space `3` where the logarithmic bound gives `4`. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.TreeLikeSpace`. The [pigeonhole examples](../../CslibFrontierTests/ProofComplexity/PigeonholeSpace.lean) build Duplicator strategies from satisfying assignments and with no pebble, and show there is none for `x ∧ ¬x` with one pebble. They also check that `EPHP^3_2` is refutable but not in width `1`, and that `EPHP^6_5` is refutable but needs clause space `5`. Lemma 2 rebuilds a `4`-pebble strategy on `EPHP^m_4` from its width bound, and `add_three_le` gives the space bound from the pigeonhole strategy directly. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.PigeonholeSpace`.

Not yet formalized:

- clause space of random `k`-CNFs;
- total and variable space;
- time–space trade-offs and pebbling formulas;
- the polynomial-calculus analogue, degree versus space, which is open.

## Cutting planes

Import `CslibFrontier.Logics.Propositional.CuttingPlanes.Separation` for everything below except
interpolation, or the smaller modules `CuttingPlanes`, `CuttingPlanes.Resolution` and
`CuttingPlanes.Pigeonhole` under `CslibFrontier.Logics.Propositional`. Interpolation is in
`CslibFrontier.Logics.Propositional.CuttingPlanes.Interpolation`.

[Cutting planes](../../CslibFrontier/Logics/Propositional/CuttingPlanes.lean) is the line-based proof system on integer linear inequalities over 0/1 variables. `Cslib.Logic.PL.Ineq V` has finitely supported coefficients `V →₀ ℤ` and an integer bound and means `∑ aᵥ xᵥ ≥ bound`; inequalities form an additive group, and `Ineq.Holds σ I` evaluates `I` under an assignment `σ : V → Bool`. `CuttingPlanes.IsProof Γ ls` lists a proof from the set `Γ` from its last line to its first. A line is a member of `Γ`, an axiom `xᵥ ≥ 0` (`Ineq.nonneg`) or `-xᵥ ≥ -1` (`Ineq.leOne`), the sum of two earlier lines, an earlier line times a positive natural number, or an earlier line divided by a positive `c` that divides every coefficient. In the last case `Ineq.div` rounds the bound up. Size is the number of lines (`DerivableInSize`, and `RefutableInSize` for deriving `Ineq.contra`, which is `0 ≥ 1`). Coefficient sizes are not measured. `IsProof.holds` gives soundness. A clause translates to `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) ≥ 1` over its *distinct* literals (`Clause.toIneq`, with `Clause.holds_toIneq_iff`), and `CNF.toIneqs φ` collects these inequalities.

To build a derivation, combine the `DerivableInSize` lemmas `hyp`, `nonneg`, `leOne`, `literal`, `add`, `smul`, `div`, `add_sum` and `sum`. Each lemma states its exact line count. Two lemmas help identify the resulting line: `Ineq.div_eq_of` recognizes a rounded division, and the `coeff_*`/`bound_*` simp lemmas, `ext`, `abel` or `module` compute the sums. `DerivableInSize.extend` replays a derivation from `Δ` on top of an existing proof containing the lines of `Δ`.

[The simulation module](../../CslibFrontier/Logics/Propositional/CuttingPlanes/Resolution.lean) translates each resolution step into at most `2 w₁ + 2 w₂` cutting-planes lines, where `wᵢ` are the widths of the two premises. Resolution here has no weakening and its resolvent is a union, so literals occurring in only one premise must be added as axioms before dividing by two. Textbook constant-cost simulations assume weakening. Hence `CNF.IsProof.cuttingPlanes` gives `(4 w + 1) s` lines for an `s`-line, width-`w` resolution proof. `CNF.RefutableInSize.cuttingPlanes` gives `(8 N + 1) s` lines for a CNF on `N` variables, using `CNF.IsProof.width_le`. `CuttingPlanes.exists_refutableInSize_iff_not_satisfiable` gives completeness.

[The pigeonhole module](../../CslibFrontier/Logics/Propositional/CuttingPlanes/Pigeonhole.lean) proves the Cook–Coullard–Turán upper bound. For `n < m`, `CuttingPlanes.refutableInSize_pigeonhole` gives a refutation of `PHP^m_n` in at most `(n + 1) (m + 1)²` lines. With Haken's bound above, [the separation module](../../CslibFrontier/Logics/Propositional/CuttingPlanes/Separation.lean) gives `two_pow_le_of_forall_refutableInSize_pigeonhole`: any map `f` that turns `s`-line cutting-planes refutations of `PHP^{n+1}_n` into `f s`-line resolution refutations satisfies `2^(n/24) ≤ f ((n + 1) (n + 2)²)`. `not_exists_polynomiallyBounded_refutableInSize_pigeonhole` states the corresponding non-polynomial conclusion. These are line-count statements about the given proof representations. They are not p-simulations between `ProofSystem` instances, which would also charge encodings and translation time. Tree-like cutting planes are not defined, so the fact that the pigeonhole refutation is tree-like is noted in the source but not stated in Lean.

[The interpolation module](../../CslibFrontier/Logics/Propositional/CuttingPlanes/Interpolation.lean) proves Krajíček's feasible interpolation for cutting planes (Theorem 6.4). Alice's system `ΓA` is a set of inequalities over `Fin n ⊕ Y` and Bob's `ΓB` a set over `Fin n ⊕ Z`, with `Y` and `Z` finite. A refutation is an `IsProof` from their images under `Ineq.relabel (Sum.map id Sum.inl)` and `Ineq.relabel (Sum.map id Sum.inr)` in `Fin n ⊕ (Y ⊕ Z)` that contains `Ineq.contra`. `IsProof.isSemanticRefutation` turns it into a semantic refutation with as many lines. Deciding a line costs `⌈log₂ (2 M |Y| + 1)⌉ + 1` bits when its `y`-coefficients are at most `M` (`ecomplexity_memRight_holds_le`). Binary search at an inequality of `ΓA` with shared coefficients at most `M₀` costs `⌈log₂ n⌉ (⌈log₂ (2 M₀ n + 1)⌉ + 1)` bits (`ecomplexity_search_holds_le`, built on `Protocol.exists_search_lt`). For `t` at least both costs, `IsProof.exists_circuit` gives a circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates, where `k` is the number of lines. The circuit is true on every `u` with `ΓA(u, q)` for some `q` and false on every `v` with `ΓB(v, r)` for some `r`. `IsProof.exists_monotone_circuit` gives a monotone circuit when the shared coefficients of `ΓA` are nonnegative. The `_of_abs_coeff_le` forms take Krajíček's single bound `M` on every coefficient of the refutation; `2 ^ t` is then `(M N) ^ O(1) (M n) ^ O(log n)`, as in the source. The separate bounds `M₀` and `M` matter for clause translations, where `M₀ = 1`. Not yet stated: the monotone case in which the shared variables occur in `ΓB` with nonpositive coefficients only, which needs the `ℬ`-monotone semantic theorem, and the clique–colouring lower bound of Corollary 7.3. The circuits are non-uniform; no extraction algorithm is given. The [interpolation examples](../../CslibFrontierTests/ProofComplexity/CuttingPlanesInterpolation.lean) refute `{y ≥ 1, x₀ - y ≥ 0}` against `{-x₀ ≥ 0}` through the private variable `y` and check that the interpolant computes `x₀`. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.CuttingPlanesInterpolation`.

The [checked examples](../../CslibFrontierTests/ProofComplexity/CuttingPlanes.lean) include a three-line refutation of `x ∧ ¬x`, a rounding step that cuts off the fractional point `(1/4, 1/4)`, and a case showing that division without the divisibility condition derives `0 ≥ 1` from the satisfiable `x ≥ 1`. They also cover soundness on a satisfiable CNF, a translated resolution refutation, and the pigeonhole and separation instances. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.CuttingPlanes`.

## Frege proofs

Import `CslibFrontier.Logics.Propositional.Frege.Resolution` for everything below, or
`CslibFrontier.Logics.Propositional.Frege` for the proof system alone.

[The Frege module](../../CslibFrontier/Logics/Propositional/Frege.lean) fixes one Hilbert-style proof system. Cook and Reckhow [cookreckhow79][cookreckhow79] require a Frege system to have finitely many sound schemes and rules that are also implicationally complete. This system is complete by the standard argument for its classical axiomatization, but the library does not prove that yet ([#3069](https://github.com/cslib-community/cslib-frontier/issues/3069)). Formulas are cslib's `Cslib.Logic.PL.Proposition` over the atoms `WithBot V` (`Cslib.Logic.PL.Frege.Formula`), with cslib's `⊥`, the atom `⊥`, read as falsity, and cslib's `Proposition.neg φ = φ → ⊥`. `Formula.eval σ` evaluates a formula under `σ : V → Bool`, because cslib's propositions carry no Boolean semantics. `IsAxiom` lists the schemes K, S and double-negation elimination for `→` and `⊥`, together with introduction and elimination schemes for `∧` and `∨`; modus ponens is the only rule. `IsProof Γ L` lists a proof from the hypotheses `Γ` from its last line to its first, as resolution and cutting planes do, and its size is the number of lines. `DerivableInSize Γ φ n` says that `φ` has a proof of at most `n` lines, as for cutting planes. `IsProof.eval` gives soundness.

Two lemmas build proofs with explicit line counts. `IsProof.cut` replays a proof from `Γ ++ Δ` on top of a proof from `Γ` that already contains the formulas of `Δ`, adding at most as many lines as the replayed proof has, so later steps can reuse earlier lines. `IsProof.deduction` is the deduction theorem with linear overhead. A proof from `Γ ++ Δ` becomes a proof from `Γ` that contains `Δ ⇒ φ` (`Formula.imps`) for each line `φ`, with at most `10 (|Δ| + 1)` lines per original line. Discharging the hypotheses one at a time would instead multiply the size by a constant for each hypothesis.

[The simulation module](../../CslibFrontier/Logics/Propositional/Frege/Resolution.lean) translates a clause into `¬ℓ₁ → ⋯ → ¬ℓₖ → ⊥` over its distinct literals (`Clause.toFormula`, with `Clause.eval_toFormula`). `Frege.derivableInSize_toFormula_resolvent` derives the formula of a resolvent from the formulas of its premises in at most `stepBound w = 10 (2 w + 1) (42 w + 23)` lines, where `w` is the larger premise width. The pivot need not occur in either premise. `CNF.IsProof.frege` turns an `s`-line resolution proof of width at most `w` into a Frege proof of at most `stepBound w * s` lines that contains the formula of every line. `CNF.RefutableInSize.frege` turns an `s`-line refutation of a CNF on `N` variables into a Frege proof of `⊥` of at most `stepBound (2 N) * s` lines. `CNF.exists_frege_refutation_iff_not_satisfiable` combines this with resolution completeness and Frege soundness: Frege refutes exactly the unsatisfiable CNFs.

These are line counts. Each translated line has `O(w)` connectives, but formula size is not measured, and none of these results is a p-simulation between `ProofSystem` instances. The library does not yet have implicational completeness of Frege, machine-level p-simulations, the mutual p-simulation of Frege systems or Extended Frege; [#3069](https://github.com/cslib-community/cslib-frontier/issues/3069) tracks them.

The [checked examples](../../CslibFrontierTests/ProofComplexity/Frege.lean) include a five-line proof of `p → p` built from the constructors, clause formulas and their semantics, a translated refutation of `x ∧ ¬x`, soundness on a satisfiable CNF, and one resolution step on width-10 clauses. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.Frege`.

## Foundations for algebraic degree lower bounds

Two lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../CslibFrontier/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `1, …, deg r + 1` are nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../CslibFrontier/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, s` are nonzero. The tests ([inclusion matrices](../../CslibFrontierTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../CslibFrontierTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped. Run `scripts/build.sh CslibFrontierTests.Foundations.Combinatorics.InclusionMatrix CslibFrontierTests.Foundations.BooleanAnalysis.AffineDegree` to check them.

## Sum-of-squares

Import `CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.TseitinExpander` for the equational system and the parity lower bounds, or the smaller modules `SumOfSquares.Basic`, `SumOfSquares.Parity` and `SumOfSquares.Tseitin` under `CslibFrontier.Logics.Propositional.Algebraic`. Import `SumOfSquares.Pigeonhole` for Positivstellensatz refutations with inequalities, or the smaller modules `SumOfSquares.Positivstellensatz` and `SumOfSquares.CNF`.

[The basic module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Basic.lean) defines sum-of-squares (Positivstellensatz) refutations over an ordered commutative ring `R`. `SOS.Refutation F d` refutes the equations `f = 0`, `f ∈ F` (a list of `MvPolynomial σ R`) by an identity `∑ᵢ gᵢ fᵢ + ∑ₖ cₖ sₖ² = -1` with weights `cₖ ≥ 0` in `R`. Degree is counted per term: every product `gᵢ fᵢ` has total degree at most `d` and every `2 deg sₖ ≤ d`. Over `ℝ` or `ℚ`, or any ring in which every nonnegative element is a sum of squares, the weights can be absorbed into the squares without raising the degree; over a general ordered ring they make the proof system stronger. `SOS.RefutableInDegree F d` says such a refutation exists (`refutableInDegree_iff`, `Refutation.refutableInDegree`). Boolean or `±1` axioms are not built in; an encoding lists them in `F`. `SOS.PseudoExpectation F d` is a linear map `Ẽ` with `Ẽ 1 = 1`, `Ẽ (s²) ≥ 0` for `2 deg s ≤ d`, and `Ẽ (q f) = 0` for `f ∈ F` and `deg (q f) ≤ d`. These follow [Barak and Steurer][barak-steurer16], lecture "The sos algorithm over general domains": Definition 1 and the remark after Theorem 2 for refutations, and Definitions 5 and 7 for pseudo-expectations. The pseudo-expectation condition here asks `Ẽ (q f) = 0` for every multiplier `q`, not only for sums of squares. `PseudoExpectation.not_refutableInDegree` is the easy direction of the duality (Theorem 8 of that lecture with `f = -1`; Theorem 19 of the lecture "Mathematical definitions"): over a strictly ordered ring, a degree-`d` pseudo-expectation rules out degree-`d` refutations. `PseudoExpectation.ofEval` is evaluation at a common zero, and `RefutableInDegree.not_exists_eval_eq_zero` is soundness. To build an explicit refutation, use `RefutableInDegree.of_list` with a list of pairs `(g, f)`. The converse of the duality (hyperplane separation) is not formalized.

[Parity systems](../../CslibFrontier/Logics/Propositional/ParitySystem.lean) are lists of equations `⊕_{i ∈ S} xᵢ = b` with `S : Finset σ`. `ParitySystem.Derives P w S b` is width-`w` derivation: start from `0 = 0` and the equations of `P`, and sum two derived equations by symmetric difference, keeping every line, axioms included, at most `w` variables wide. Schoenebeck's Definition 10 does not bound the axioms, so "no width-`w` derivation of `0 = 1`" is a weaker hypothesis here and the lower bounds are correspondingly stronger. [The Tseitin parity module](../../CslibFrontier/Logics/Propositional/ParitySystem/Tseitin.lean) (`CslibFrontier.Logics.Propositional.ParitySystem.Tseitin`) adds `ParitySystem.tseitin ends χ`, the Tseitin parity system of a multigraph, and `holds_tseitin_iff_eval_tseitinFormula` matches it with `CNF.tseitinFormula`; the core module does not import the Tseitin CNF.

[The parity module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Parity.lean) gives the `±1` encoding `ParitySystem.toPolys R P`: `∏_{i ∈ S} Xᵢ - (-1)^b` for every equation and `Xᵢ² - 1` for every variable. `exists_eval_eq_zero_iff` says its common zeros in a strictly ordered field are the satisfying assignments. `ParitySystem.pseudoExpectation` is the construction of [Schoenebeck][schoenebeck08], Lemma 13, defined whenever `¬ P.Derives d ∅ true`. It sends `∏_{i ∈ T} Xᵢ` to `(-1)^c` if `⊕_T x = c` is derivable in width `d`, and to `0` otherwise (`parityValue`, `pseudoExpectation_prod_X`). General monomials are first reduced modulo `Xᵢ² = 1` through `Finsupp.oddSupport`. Positive semidefiniteness is `sum_sum_mul_parityValue_nonneg`: the classes of "`A ∆ B` is derivable" split the moment matrix into rank-one blocks. `not_sos_refutableInDegree_toPolys` is the resulting lower bound: no width-`d` derivation of `0 = 1` implies no SOS refutation of degree at most `d`. This is a statement about the sum-of-squares proof system with this pseudo-expectation. Schoenebeck's Lasserre vector solution is not constructed. The author's copy consulted (December 2008) states Lemma 13 for the `w/2`-th round of Lasserre, and round `r` constrains moments of degree up to `2 r`; versions of the paper differ on this constant, as recorded in the source entry.

[The Tseitin module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Tseitin.lean) shows `not_derives_tseitin_empty_true`: below width `e(G)` (`Multigraph.minBalancedCut`), derivations from a Tseitin system on a connected multigraph stay among cuts of sets smaller than a third of the vertices, so they never reach `0 = 1`. Grigoriev's theorem follows. `Tseitin.minBalancedCut_le_of_sos_refutableInDegree` says that a degree-`d` refutation of the `±1` encoding of a Tseitin system on a connected multigraph has `e(G) ≤ d`, over every strictly ordered commutative ring. [The expander module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/TseitinExpander.lean) gives `h(G) |V| / 3 ≤ d` for rotation maps (`Tseitin.edgeExpansion_mul_card_div_three_le_of_sos_refutableInDegree`). Its family `ParitySystem.exists_forall_sos_refutableInDegree_le` has, for `n ≥ 2`, `n` equations of at most `120` variables on at most `120 n` variables, and every refutation has `n ≤ 18000 d`. The linear bound is Grigoriev's; the constants `120` and `18000` come from the library's expanders (`RotationMap.expander`, `RotationMap.le_edgeExpansion_expander`, edge expansion at least `1 / 6000`), not from the source. The expanders are obtained non-constructively. Barak and Steurer's lecture "Higher-degree integrality gaps", Lemma 24, states the Tseitin case for `(1 + ε)`-vertex-expanding `d`-regular graphs with all charges `1` and the `0/1` encoding (degree `n / 4`). The theorem here measures expansion by `e(G)`, allows any multigraph and charges, and uses the `±1` encoding. Random `3`-XOR (Barak and Steurer, Theorem 2), Grigoriev's knapsack bound and the `0/1` encoding are not treated. [Grigoriev's paper][grigoriev01] was not consulted, so its locator is unverified. The relevant statements were checked against Schoenebeck's Lemma 13 and Barak and Steurer's lecture "Higher-degree integrality gaps", Lemmas 7 and 24 and Theorem 2.

[The Positivstellensatz module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Positivstellensatz.lean) (namespace `Cslib.Logic.PL.SOS.Psatz`) adds inequality constraints. `Psatz.Refutation I E d` refutes `f ≥ 0` for `f ∈ I` and `g = 0` for `g ∈ E` (sets of polynomials) by an identity `∑ⱼ hⱼ gⱼ + ∑ₖ cₖ sₖ² ∏_{f ∈ Sₖ} f = -1`, with finite `Sₖ ⊆ I` and `cₖ ≥ 0`. A summand is a `Psatz.Summand` (`factors`, `weight`, `base`). Degree is counted per summand: every `hⱼ gⱼ` has total degree at most `d`, and every summand has formal degree `2 deg sₖ + ∑_{f ∈ Sₖ} deg f` (`Summand.degree`) at most `d`. The formal degree bounds the total degree (`Summand.totalDegree_toPoly_le`). Over a domain the two are equal for nonzero summands (`Summand.totalDegree_toPoly`). This is [Barak and Steurer][barak-steurer16], lecture "The sos algorithm over general domains", Definition 1, with equations added as multiples `h g` of any sign, as in `SOS.Refutation`. `Psatz.PseudoExpectation I E d` asks `Ẽ (s² ∏_{f ∈ S} f) ≥ 0` for finite `S ⊆ I` of formal degree at most `d` (Definition 7 with `ℓ = 0`), and `PseudoExpectation.not_refutableInDegree` is the easy duality. `RefutableInDegree.not_exists_eval` is soundness. Build refutations with `RefutableInDegree.of_sum` from finite families of equation terms and summands. `SOS.RefutableInDegree.psatz` and `Psatz.refutableInDegree_empty_iff` identify the equational system with the case `I = ∅`, and `SOS.PseudoExpectation.psatz` carries pseudo-expectations over.

[The CNF module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/CNF.lean) encodes a CNF through its cutting-planes inequalities. `Ineq.toPoly` sends `∑ᵥ aᵥ xᵥ ≥ b` to `∑ᵥ aᵥ Xᵥ - b`. `Psatz.cnfIneqs φ` contains the polynomials of `Clause.toIneq` for the clauses of `φ`, together with the box constraints `Xᵥ` and `1 - Xᵥ`. `Psatz.booleanAxioms V R` contains `Xᵥ² - Xᵥ`. This is the translation (2.4)–(2.6) of [Grigoriev, Hirsch and Pasechnik][grigorievhirschpasechnik02], with the Boolean axioms as equations. `Psatz.exists_feasible_iff` says that over a strictly ordered ring the common solutions are the satisfying assignments, and `not_satisfiable_of_refutableInDegree` is soundness for CNFs. In degree `1` the Boolean axioms impose nothing (`eq_zero_of_totalDegree_mul_le_one`). So a fractional point of the box that satisfies the clause inequalities is a degree-`1` pseudo-expectation (`degreeOnePseudoExpectation`), and it rules out degree-`1` refutations (`not_refutableInDegree_one_of_eval_nonneg`).

[The pigeonhole module](../../CslibFrontier/Logics/Propositional/Algebraic/SumOfSquares/Pigeonhole.lean) proves `Psatz.refutableInDegree_two_pigeonhole`: for `m > n`, `PHP^m_n` has a refutation of degree `2` over every strictly ordered commutative ring. The identity is `∑ᵢ Pᵢ + ∑ⱼ (1 - ∑ᵢ xᵢⱼ)² + ∑ⱼ ∑_{i ≠ i'} xᵢⱼ Hᵢᵢ'ⱼ + (m - n - 1) + (m - 2) ∑ᵢⱼ (xᵢⱼ² - xᵢⱼ) = -1`, with pigeon inequalities `Pᵢ = ∑ⱼ xᵢⱼ - 1` and hole inequalities `Hᵢᵢ'ⱼ = 1 - xᵢⱼ - xᵢ'ⱼ`. For `m = n + 1` it is Example 2.1 of Grigoriev, Hirsch and Pasechnik, stated there as a static `LS₊` proof; the summand `m - n - 1` covers `m > n + 1`. Over a strictly ordered field and for `n ≥ 2`, the point `xᵢⱼ = 1 / n` satisfies every inequality (`eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole`), so there is no refutation of degree `1` (`not_refutableInDegree_one_pigeonhole`). `refutableInDegree_pigeonhole_iff` combines both: for `n ≥ 2`, a refutation of degree at most `d` exists exactly when `n < m` and `2 ≤ d`. Separately, resolution refutations of `PHP^{n+1}_n` have size at least `2^(n/24)` (`CNF.two_pow_le_of_refutableInSize_pigeonhole`). These are two facts about two different proof systems. The module bounds degree only, and it makes no claim about refutation size or about simulations. The Positivstellensatz calculus (the dynamic, derivation-based system), the converse duality and size measures are not formalized.

The [Positivstellensatz examples](../../CslibFrontierTests/ProofComplexity/Positivstellensatz.lean) check the following. `PHP³₂` has a degree-`2` refutation over `ℤ` and `ℚ`, none of degree `1` over `ℚ`, and refutability in degree `d` exactly when `2 ≤ d`. Its degree-`1` pseudo-expectation, evaluation at `1/2`, is fractional, so `Psatz.PseudoExpectation` is inhabited for an unsatisfiable system. `PHP²₁` has an explicit degree-`1` refutation, so `n ≥ 2` is needed. `PHP¹₀` has a degree-`0` refutation, and the satisfiable `PHP²₂` has none of any degree. The equation `1 = 0` gives a refutation with `I = ∅`. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.Positivstellensatz`.

The [checked examples](../../CslibFrontierTests/ProofComplexity/SumOfSquares.lean) treat the triangle with one charged vertex. It is unsatisfiable, width-`2` derivations reach `0 = 1`, and Schoenebeck's pseudo-expectation of degree `1` exists, so `SOS.PseudoExpectation` is inhabited for an unsatisfiable system. There is no refutation of degree `1`. An explicit refutation of degree `2`, with one square of weight `2`, shows that `e(G) ≤ d` is attained. With two charged vertices the system is satisfiable, and point evaluation rules out refutations of every degree. On `K₄`, Schoenebeck's pseudo-expectation of degree `3` exists, so there is no refutation of degree `3`. Check them with `scripts/build.sh CslibFrontierTests.ProofComplexity.SumOfSquares`.

## Known Limitations

This chapter covers resolution and clause space, cutting planes, semantic derivations, Frege proofs, Nullstellensatz certificates and polynomial calculus (including refutations over the Boolean cube and two degree lower bounds, for subset sum and Tseitin formulas), sum-of-squares and their syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[barak-steurer16]: ../sources.md#barak-steurer16
[beyersdorffgalesilauria10]: ../sources.md#beyersdorffgalesilauria10
[complexitylib]: ../sources.md#complexitylib
[cookreckhow79]: ../sources.md#cookreckhow79
[grigoriev01]: ../sources.md#grigoriev01
[grigorievhirschpasechnik02]: ../sources.md#grigorievhirschpasechnik02
[impagliazzopudlaksgall99]: ../sources.md#impagliazzopudlaksgall99
[mosertardos10]: ../sources.md#mosertardos10
[schoenebeck08]: ../sources.md#schoenebeck08
[toran04]: ../sources.md#toran04
