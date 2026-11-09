# Propositional models and resolution proof complexity

Complexitylib represents propositional syntax as concrete finite data and distinguishes satisfiability, derivability and resource-bounded proof objects. This supports reductions, model counting and lower bounds without identifying a proof's length with the time needed to find it. [complexitylib][complexitylib]

## CNF, CSP and quantified formulas

[CNF](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CNF.lean#L67) is a list of clauses, each a list of signed variables. Ordering and repeated occurrences are retained. Several useful sizes coexist: clause count, literal-occurrence count, distinct-variable support, maximum clause width and serialized bit length. In a fixed-width SAT theorem the stated width convention must be checked; in resolution, width is explicitly the number of distinct literals.

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
use `MaxTwoSAT_npComplete`. An instance `(φ, K)` is encoded by `encPair encCNF encNat`, so the
target `K` is binary. Every clause has at most two literals, unit clauses included, and clauses
are counted with multiplicity: `(φ, K) ∈ MaxTwoSAT` when some assignment satisfies at least `K`
entries of the list `φ`. The [checked examples](../../CslibFrontierTests/MaxTwoSAT.lean) cover the
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
induction, `sum_prod_shapes_le`. The model counts resamplings; it does not charge for sampling or
for detecting occurring events. Theorems 1.3 (the parallel version) and 1.4 (the deterministic
version) and the lopsided form are not formalized. The
[checked examples](../../CslibFrontierTests/MoserTardos.lean) give one fair coin, where the bound is
`x / (1 - x) = 1`, two dependent events on three coins that meet the hypothesis with equality, an
impossible event with `x = 0`, two complementary events for which no `x` satisfies the
hypothesis, and a concrete valid log on a fixed table whose witness tree is computed by `decide`
and passes its check. Check them with
`scripts/build.sh CslibFrontierTests.MoserTardos`.

Support-based CNF model counting counts assignments to variables that occur. Declared-universe counting instead fixes a larger variable set and can include free choices for unused variables. The library supplies relabeling and exact gadget-counting bridges, so a reduction claiming preservation of counts must specify which convention it preserves. This distinction is particularly relevant to dense relabeling and the [native fixed-width counting endpoint](../machines-and-classes/native-counting.md).

[Constraint](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CSP.lean#L69) has a relation alphabet and constraints consisting of a relation label plus a variable list. Semantics evaluates the label on the corresponding list of domain values. Arity is not enforced by the relation's type; a fixed-arity interpretation is an additional condition. Boolean/CNF translations and partition-function clients instantiate this generic semantic interface.

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
`Cslib.Complexity.CSP.computableInPolyTime_validArity` in `PolyTime.CSP.Boolean`.

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

The ordinary solvers are also reusable: `HornSAT.mem_P`, `DualHornSAT.mem_P` and
`XORSAT.satisfiable_mem_P`. Horn syntax counts positive occurrences, so two copies of a positive
literal violate the syntax condition; repeated negatives and opposite-polarity tautologies are
supported. Forward chaining reaches the least-model candidate in `numVars + 1` passes, storing
filtered occurrences rather than an array indexed by the largest name. Affine equations are
variable lists paired with Boolean right-hand sides; repeated variables cancel in the Boolean
ring. Dense Gaussian elimination preserves row count and weakly decreases its complete framed
state encoding at each column. See the [Horn solver tests](../../CslibFrontierTests/HornSAT.lean)
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
These mathematical prerequisites provide no planar embedding algorithm, edge-CSP solver or
planar complexity dichotomy yet. The full remaining objective is [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

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
malformed widths, repeated rows, contraction cases and framed size calculations. These operation lemmas provide the executable and quantitative layer; the mathematical closure
is supplied separately below. Whole-blossom correctness still remains unproved.

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

These are finite encoding and numerical-verification results. Geometric realization, identifying
the outer face across disconnected components, bare-instance recognition/construction, planar
duality and the edge solver remain open. Exact relation-arity and satisfiability guards are
separate: a false nullary relation passes the port-order check. Rejection of a supplied toroidal
rotation does not prove that its graph is nonplanar. The full objective remains
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
certificates remain those of `PolyTime.CSP.Table`. Whole-instance blossom contraction/lifting,
solver correctness, native solver cost and the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

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
augmentation or a blossom. Whole-blossom contraction/lifting, the full solver and planar
dichotomy remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

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
Whole-blossom contraction/lifting and the full solver remain open.

The reusable scan lives in `CSP.Occurrence.Enumeration`: `incidenceList` and
`occurrences_eq_map_incidenceList` connect typed occurrences to the existing ordered record list.
`PolyTime.CSP.Occurrence` supplies `encOccurrenceRecord` and
`computableInPolyTime_occurrences` without importing graph construction. Both incidence graphs
and the native augmentation compiler use that same enumeration and certificate.

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
whole-blossom contraction/lifting and the full planar endpoint remain open under
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
These mathematical results compose with the native compiler below. Whole-blossom
contraction/lifting and the complete solver/dichotomy remain outside this layer;
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
unchanged. Full recursive solving, geometric realization/recognition and the planar dichotomy
remain open under [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

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
or planar hardness. Those obligations and the full solver/dichotomy remain open under
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
- `CNF.exists_forall_refutableInSpace_le` is a family with explicit constants. For `n ≥ 4392000` it has at most `120 n` variables, `2 ^ 120 · n` clauses of width at most `120`, and every refutation in clause space `s` has `n ≤ 36000 s`. It shares its setup with the size family of the Tseitin-expander module through `Tseitin.exists_expander_tseitinFormula`. That lemma gives the Tseitin formula of the `120`-regular expander on `n ≥ 2` vertices with its explicit constants: connectivity, degree at most `120`, `e(G) ≥ n / 18000`, at most `120 n` variables and `2 ^ 120 · n` clauses, clauses with at most `120` literals (so of width at most `120`), and unsatisfiability.

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

Two Boolean-analysis lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../CslibFrontier/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `n!` is nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../CslibFrontier/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, #U` are nonzero. The tests ([inclusion matrices](../../CslibFrontierTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../CslibFrontierTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped.

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

This section inventories resolution, including clause space, cutting planes, semantic derivations, Frege proofs, sum-of-squares and their syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[barak-steurer16]: ../sources.md#barak-steurer16
[beyersdorffgalesilauria10]: ../sources.md#beyersdorffgalesilauria10
[complexitylib]: ../sources.md#complexitylib
[cookreckhow79]: ../sources.md#cookreckhow79
[grigoriev01]: ../sources.md#grigoriev01
[grigorievhirschpasechnik02]: ../sources.md#grigorievhirschpasechnik02
[mosertardos10]: ../sources.md#mosertardos10
[schoenebeck08]: ../sources.md#schoenebeck08
[toran04]: ../sources.md#toran04
