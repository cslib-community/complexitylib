# Propositional models and resolution proof complexity

Complexitylib represents propositional syntax as concrete finite data and distinguishes satisfiability, derivability and resource-bounded proof objects. This supports reductions, model counting and lower bounds without identifying a proof's length with the time needed to find it. [complexitylib][complexitylib]

## CNF, CSP and quantified formulas

[CNF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CNF.lean#L67) is a list of clauses, each a list of signed variables. Ordering and repeated occurrences are retained. Several useful sizes coexist: clause count, literal-occurrence count, distinct-variable support, maximum clause width and serialized bit length. In a fixed-width SAT theorem the stated width convention must be checked; in resolution, width is explicitly the number of distinct literals.

The [ClauseSet](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/ClauseSet/Basic.lean#L55) representation instead uses finite sets of finite sets of literals, so order and repetitions disappear. Its occurrence measure counts clauses mentioning a variable. List/set conversions preserve satisfying assignments but need separate size/occurrence lemmas. This is the representation used by the sparsification development.

For ordinary disjunction with exactly three distinct variables per clause, import
`Complexity.Computability.Complexity.Problems.EUThreeSAT` and use `EUThreeSAT_npComplete`.
The bounded-occurrence variant behaves differently: `EUThreeSATThree.mem_P` checks syntax,
because every valid formula is satisfiable. For not-all-equal semantics, import
`Complexity.Computability.Complexity.Problems.NAEThreeSAT`. Here `CNF.evalNAE` requires a true
and a false literal in each clause. **NAE EU3SAT** has exactly three distinct variables per clause
and is proved NP-complete by `NAEEUThreeSAT_npComplete`. **NAE3SAT** permits width at most three;
**NAE3SAT-3** also bounds total occurrences per variable by three, and is proved NP-complete by
`NAEThreeSATThree_npComplete`. The latter permits binary clauses. See the
[checked examples](../../ComplexityTests/NAEAndEUThreeSAT.lean) for the complete import context,
satisfiable and unsatisfiable instances, and applications of these endpoints. Run
`scripts/build.sh ComplexityTests.NAEAndEUThreeSAT` from the repository root to check them;
successful compilation confirms the displayed theorem types and examples.

For sparse exact `k`-CNFs, import `Complexity.Logics.Propositional.CNF.Moser.Probability`.
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
constant of this encoding. These count resamplings, not machine time. The
[checked examples](../../ComplexityTests/Moser.lean) include a concrete run, its log and the
recovered tape; check them with `scripts/build.sh ComplexityTests.Moser`.

Support-based CNF model counting counts assignments to variables that occur. Declared-universe counting instead fixes a larger variable set and can include free choices for unused variables. The library supplies relabeling and exact gadget-counting bridges, so a reduction claiming preservation of counts must specify which convention it preserves. This distinction is particularly relevant to dense relabeling and the [native fixed-width counting endpoint](../machines-and-classes/native-counting.md).

[Constraint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CSP.lean#L69) has a relation alphabet and constraints consisting of a relation label plus a variable list. Semantics evaluates the label on the corresponding list of domain values. Arity is not enforced by the relation's type; a fixed-arity interpretation is an additional condition. Boolean/CNF translations and partition-function clients instantiate this generic semantic interface.

[QBF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/QBF.lean#L76) uses named-variable Boolean quantifiers. Evaluating an existential or universal binder updates the assignment with both possible values and ORs or ANDs the results. Arithmetization and native/interactive-proof completeness clients live in their corresponding sections. This formula syntax does not by itself assert a resource bound for evaluation.

## Boolean Schaefer dichotomy

Import `Complexity.Computability.Complexity.Problems.CSP.Schaefer` for the full Boolean
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

[The full checked client](../../ComplexityTests/Schaefer.lean) exercises every tractable arm,
a concrete NAE hard language, arbitrary fixed arities, sparse labels and an empty alphabet.
[Horn/dual-Horn clients](../../ComplexityTests/CSPHorn.lean) give AND-only and OR-only languages
and malformed/repeated-scope examples. [Affine clients](../../ComplexityTests/CSPAffine.lean)
cover cancellation, sparse labels, empty/nullary relations and actual compiler/solver runs.
[The initial contract examples](../../ComplexityTests/BooleanCSP.lean) and
[constant/majority clients](../../ComplexityTests/CSPTractability.lean) remain useful entry points.

For the structural APIs, `Cslib.Logic.IsPolymorphism` combines satisfying tuples coordinatewise.
It is preserved by conjunction, substitution (including repeated variables), existential projection
and composition. Its operation index may be empty; this general nullary notion is distinct from
the unary constants in the criterion. For every finite coordinate type, majority preservation is equivalent to a
2CNF definition (`PL.isPolymorphism_majority_iff_exists_twoCNF`), AND/OR preservation to a
Horn/dual-Horn definition (`PL.isPolymorphism_and_iff_exists_hornCNF`,
`PL.isPolymorphism_or_iff_exists_dualHornCNF`), and ternary parity preservation to an affine
system (`PL.isPolymorphism_parity_iff_exists_affineSystem`). These definitions need no auxiliary
variables and include empty/nullary relations. See the [majority examples](../../ComplexityTests/MajorityCNF.lean).

The ordinary solvers are also reusable: `HornSAT.mem_P`, `DualHornSAT.mem_P` and
`XORSAT.satisfiable_mem_P`. Horn syntax counts positive occurrences, so two copies of a positive
literal violate the syntax condition; repeated negatives and opposite-polarity tautologies are
supported. Forward chaining reaches the least-model candidate in `numVars + 1` passes, storing
filtered occurrences rather than an array indexed by the largest name. Affine equations are
variable lists paired with Boolean right-hand sides; repeated variables cancel in the Boolean
ring. Dense Gaussian elimination preserves row count and weakly decreases its complete framed
state encoding at each column. See the [Horn solver tests](../../ComplexityTests/HornSAT.lean)
and [XOR solver tests](../../ComplexityTests/XORSAT.lean).

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
of general equality elimination. See [clone examples](../../ComplexityTests/BooleanClone.lean),
[gadget examples](../../ComplexityTests/CSPGadget.lean) and
[hardness examples](../../ComplexityTests/SchaeferHardness.lean).

`CSPSAT.exists_linear_size_reduction_from_threeSAT` supplies one reduction with native
polynomial-time computation, correctness and the bound
$n' + m' \le C_\Gamma m \le C_\Gamma(n + m)$. Here `numVars` counts distinct occurring
variables, `length` counts clauses or constraints, and the constant depends only on the fixed
target language. The bound holds for every raw CNF, including malformed and empty inputs.
`CSP.length_replaceGadgets` and `CSP.vars_length_replaceGadgets` give exact sums of template
constraint and occurrence counts; distinct variables are bounded by occurrences. The guarded
compiler retains a uniform linear bound because an invalid input is nonempty. These are
combinatorial size bounds; neither linear running time nor linear binary encoding length is
asserted. See the [checked size clients](../../ComplexityTests/SchaeferSize.lean).

The result is the Boolean dichotomy; symmetric and larger-domain dichotomies are outside its scope.

## Planar Boolean CSP prerequisites

`Complexity.Foundations.Data.BitString.CyclicDifference` defines ordered cyclic differences:
`cyclicDifference x i` is `x i ^^ x (finRotate n i)`. Its image is exactly the even-parity
tuples, and `cyclicIntegral` constructs an inverse by prefix parity. The fiber theorem
`cyclicDifference_eq_iff` says that two tuples have the same differences precisely when they
are equal or complementary. Consequently, `mem_cyclicDifferenceRelation_iff` recovers any
`IsSelfComplementary` relation from its difference relation. Empty and nullary relations are
included. These are the tuple and relation transformations of Kazda–Kolmogorov–Rolínek,
arXiv:1602.03124v6, Definitions 13–14, printed p. 0:6.

Import `Complexity.Foundations.Data.BitString.DeltaMatroid.Operations` for relational
`BitString.IsDeltaMatroid` and `BitString.IsEvenDeltaMatroid`. The exchange axiom is one-sided:
for feasible `x,y` disagreeing at `i`, some disagreeing coordinate `j` makes
`flipOn {i,j} x` feasible. A delta-matroid is nonempty. Evenness means that all feasible tuples
have the same parity, which may be odd; it forces `j ≠ i`. Twists and coordinate equivalences
preserve these properties, and feasible tuples are connected by feasible two-coordinate flips.
The four-coordinate lemmas isolate local exchange consequences used by the paper's blossom
proof; they do not prove its full forest or whole-blossom contraction invariants.

[Difference tests](../../ComplexityTests/CyclicDifference.lean) show that ternary NAE maps to
an even delta-matroid of three weight-two tuples. [Exchange tests](../../ComplexityTests/DeltaMatroid.lean)
include odd exactly-one relations, the empty-coordinate case, and failures of exchange/evenness.
These mathematical prerequisites provide no planar embedding algorithm, edge-CSP solver or
planar complexity dichotomy yet. The full remaining objective is [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Occurrences, explicit tables and ordered incidence rotations

`Complexity.Logics.Propositional.CSP.Occurrence` indexes arguments by constraint position and
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
See [occurrence and incidence tests](../../ComplexityTests/CSPOccurrence.lean).

`Complexity.Computability.PolyTime.CSP.Table` supplies `CSP.Table` as an explicit, potentially
infinite relation alphabet for the same CSP lists. Arity is binary; accepted rows are doubly
framed Boolean lists, including duplicate rows. Width errors reject every row. The local
`Table.contract` retains rows with zero or one deviation from a feasible reference on selected
internal positions, projects outside positions in their original order, and appends the connector
bit. Its row count cannot increase; at least two distinct in-range internal positions imply
strict width decrease and nonincrease of the full encoded table size. `Table.exactlyOne`
constructs the new connector relation in native polynomial time from a scope list: the list's
length pays for quadratic output. There is no polynomial-output claim from a binary arity alone.
The zero-connector relation is empty. [Table tests](../../ComplexityTests/CSPTable.lean) cover
malformed widths, repeated rows, contraction cases and framed size calculations. These operation lemmas provide the executable and quantitative layer; the mathematical closure
is supplied separately below. Whole-blossom correctness still remains unproved.

`Problems.Graph.RotationSystem` represents edge ends by edge-list position and a Boolean side.
Loops have two distinct ends, and parallel edges retain separate positions. Vertex rotations
have exactly one cycle per nonempty endpoint fiber. Face orbits use reversal followed by inverse
rotation and include fixed-point orbits. `Problems.CSP.RotationSystem` maps ordered arguments to
these ends and states `RespectsArgumentOrder`: the rotation at a constraint follows cyclic scope
order. Mirroring a ternary constraint can violate that order. Nullary constraints have no argument
ends, so this order condition is vacuous for them. See [graph rotation tests](../../ComplexityTests/RotationSystem.lean)
and [constraint-order tests](../../ComplexityTests/CSPRotationSystem.lean).

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
indices; only actual list lengths fund iteration. See the [graph certificate tests](../../ComplexityTests/RotationCertificate.lean)
and [ordered CSP certificate tests](../../ComplexityTests/CSPRotationCertificate.lean).

These are finite encoding and numerical-verification results. Geometric realization, identifying
the outer face across disconnected components, bare-instance recognition/construction, planar
duality and the edge solver remain open. Exact relation-arity and satisfiability guards are
separate: a false nullary relation passes the port-order check. Rejection of a supplied toroidal
rotation does not prove that its graph is nonplanar. The full objective remains
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Delta-matroid composition and local contraction closure

`Complexity.Foundations.Data.BitString.DeltaMatroid.Composition` proves direct products,
elimination of equal coordinate pairs, and relational composition. `IsDeltaMatroid.comp` and
`IsEvenDeltaMatroid.comp` join relations on `ι ⊕ κ` and `κ ⊕ τ` along the finite shared `κ`
coordinates, then remove those coordinates. Both require a nonempty composed relation:
nonempty inputs alone do not guarantee compatible shared values. Empty external coordinate
types are allowed. The proof uses successive one-sided exchanges, without assuming simultaneous
exchange. This maps Proposition 6 and its parity corollary in Kazda–Kolmogorov–Rolínek,
arXiv:1602.03124v6, printed pp. 0:4–0:5, with output nonemptiness made explicit.

`Complexity.Logics.Propositional.CSP.Table.DeltaMatroid` connects this mathematics to the actual
guarded table semantics. `Table.isEvenDeltaMatroid_contract` requires the original declared-arity
table relation to be even and `Table.canContract table reference positions = true`. The latter
supplies the feasible reference and distinct in-range internal positions; the reference witnesses
nonemptiness of the output internally. The proof preserves outside-coordinate order and the
final connector, using composition with a proved star gadget that permits zero internal changes
or one internal change paired with a true connector. No blossom or solver hypothesis appears.
Unlike strict width decrease, closure requires no lower bound of two on the selected positions.

`Table.isEvenDeltaMatroid_exactlyOne` proves closure for every nonempty connector scope, with odd
common parity. The empty-scope relation is rejected under the nonempty delta-matroid convention.
[Composition and contraction tests](../../ComplexityTests/DeltaMatroidComposition.lean) cover
incompatible shared coordinates, empty external coordinates, arbitrary scope lengths, ordered
outside ports, empty selections, nullary tables, and malformed guards. Native operation and size
certificates remain those of `PolyTime.CSP.Table`. Whole-instance blossom contraction/lifting,
solver correctness, native solver cost and the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Prefix-valid walks and augmentation

Import `Complexity.Logics.Propositional.CSP.Edge.Augmenting` for Boolean occurrence-label
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

[Augmenting-walk tests](../../ComplexityTests/EdgeCSPWalk.lean) include doubled equality
constraints, actual returned paths, odd unsatisfiable units, repeated constraint positions,
empty/nullary cases, sparse labels, and a trail whose final flip is valid but an intermediate
prefix is invalid. The routine takes an improving comparison labeling as input: finding that
labeling, or finding an augmenting walk without it, still needs the DAG/forest/blossom search.
Its native runtime certificate and the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Finite crossover gadget semantics

Import `Complexity.Logics.Propositional.CSP.Planar.Crossover` for Dvořák–Kupec, ICALP 2015,
§4, printed pp. 440–441, Figure 1. `BitString.cross` equates opposite ports in cyclic order;
`nearCross` additionally permits `0001` and `1110`. `IsStandardizedInconsistent` requires
self-complementarity, inclusion of CROSS, and the source's upper restriction. Its exact
classification has eight shapes, selected by three optional complementary tuple pairs.

The actual four-constraint `Crossover.figureOneAStandardized` is a `PPGadget` with three
auxiliaries. Its target is NEAR-CROSS exactly when the input relation contains `0001` or
`0010`, and CROSS otherwise. The actual two-constraint `Crossover.figureOneB` uses one auxiliary
and defines CROSS from NEAR-CROSS. Numbered scope positions match the source's diagram;
width-guarded interpretations reject malformed scopes. [Crossover clients](../../ComplexityTests/PlanarCrossover.lean)
check every standardized shape, both first-gadget outcomes, explicit witnesses and rejected
boundary tuples, while retaining the existing CNF crossover tests.

These are finite relation semantics. They do not prove planar embedding/substitution,
normalization from a failed delta-matroid condition (the source's omitted Lemma 6 proof),
a hardness theorem or a new native runtime certificate. These obligations remain part of
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Three resolution representations

| Representation | What it supplies | Cost |
|---|---|---|
| [CNF.Derives](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution.lean#L100) | Inductive proposition generated by input clauses and pivot resolution | No explicit size. |
| [CNF.IsProof](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Proof.lean#L107) | A finite ordered list whose lines are justified by inputs or earlier lines | Number of lines; maximum distinct-literal width. |
| [CNF.Derivation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TreeLike.lean#L85) | Type-valued tree with input leaves and binary resolution nodes | Tree-node count, width and depth. |

The resolvent removes opposite pivot literals and concatenates the remaining lists. There is no primitive weakening rule; list-level subtleties are handled by lemmas. Soundness and refutation completeness relate the derivability proposition to unsatisfiability. Explicit proof representations then support quantitative theorems.

A tree-like derivation yields a decision tree that finds a clause falsified by the input assignment. Conversely, a suitable clause-search decision tree yields a resolution refutation with at most `2 leaves - 1` nodes. Sharing in a line proof need not survive this tree conversion, which explains why tree-like and general resolution complexity must remain separate.

## Major lower bounds and interpolation

[The pigeonhole development](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Pigeonhole.lean) formalizes Haken's exponential lower bound for `PHP^(n+1)_n`, using a simplified Beame–Pitassi-style argument. Its explicit finite endpoint gives at least `2^floor(n/24)` proof lines. Source documentation explains the critical-assignment measure and greedy restriction sequence. The result also lower-bounds tree-like resolution through the line/tree bridge.

[The Ben-Sasson–Wigderson tradeoff](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/SizeWidth.lean) says that a CNF of initial width k on N variables with an s-line refutation has a refutation of width at most `k + 2 sqrt(2 N log s) + 2`. The contrapositive form yields an exponential line lower bound from a width lower bound. These constants and the logarithm/real square-root convention are explicit in the theorem.

[The Tseitin-expander result](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) combines a graph-expansion width lower bound with that tradeoff. It gives a family of linear-variable, constant-width unsatisfiable CNFs requiring exponentially many proof lines. The expansion witnesses are obtained nonconstructively from counting, and the source explicitly says so: existence of a hard family is proved, while an efficient explicit expander/formula generator is not supplied by that endpoint.

Interpolation modules extract circuits separating the two sides of a refuted conjunction. Monotone extraction supports clique/coloring lower-bound applications, and a separate polynomial-time file addresses encoded extraction. The distinction between semantic existence of an interpolant and a native efficient extraction algorithm follows the same design pattern as circuits and finite-model logic. See [interpolation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation.lean), [monotone extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/MonotoneExtraction.lean) and [native extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/PolyTime.lean).

## Cutting planes

Import `Complexity.Logics.Propositional.CuttingPlanes.Separation` for everything below, or the
smaller modules `CuttingPlanes`, `CuttingPlanes.Resolution` and `CuttingPlanes.Pigeonhole`
under `Complexity.Logics.Propositional`.

[Cutting planes](../../Complexity/Logics/Propositional/CuttingPlanes.lean) is the line-based proof system on integer linear inequalities over 0/1 variables. `Cslib.Logic.PL.Ineq V` has finitely supported coefficients `V →₀ ℤ` and an integer bound and means `∑ aᵥ xᵥ ≥ bound`; inequalities form an additive group, and `Ineq.Holds σ I` evaluates `I` under an assignment `σ : V → Bool`. `CuttingPlanes.IsProof Γ ls` lists a proof from the set `Γ` from its last line to its first. A line is a member of `Γ`, an axiom `xᵥ ≥ 0` (`Ineq.nonneg`) or `-xᵥ ≥ -1` (`Ineq.leOne`), the sum of two earlier lines, an earlier line times a positive natural number, or an earlier line divided by a positive `c` that divides every coefficient. In the last case `Ineq.div` rounds the bound up. Size is the number of lines (`DerivableInSize`, and `RefutableInSize` for deriving `Ineq.contra`, which is `0 ≥ 1`). Coefficient sizes are not measured. `IsProof.holds` gives soundness. A clause translates to `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) ≥ 1` over its *distinct* literals (`Clause.toIneq`, with `Clause.holds_toIneq_iff`), and `CNF.toIneqs φ` collects these inequalities.

To build a derivation, combine the `DerivableInSize` lemmas `hyp`, `nonneg`, `leOne`, `literal`, `add`, `smul`, `div`, `add_sum` and `sum`. Each lemma states its exact line count. Two lemmas help identify the resulting line: `Ineq.div_eq_of` recognizes a rounded division, and the `coeff_*`/`bound_*` simp lemmas, `ext`, `abel` or `module` compute the sums. `DerivableInSize.extend` replays a derivation from `Δ` on top of an existing proof containing the lines of `Δ`.

[The simulation module](../../Complexity/Logics/Propositional/CuttingPlanes/Resolution.lean) translates each resolution step into at most `2 w₁ + 2 w₂` cutting-planes lines, where `wᵢ` are the widths of the two premises. Resolution here has no weakening and its resolvent is a union, so literals occurring in only one premise must be added as axioms before dividing by two. Textbook constant-cost simulations assume weakening. Hence `CNF.IsProof.cuttingPlanes` gives `(4 w + 1) s` lines for an `s`-line, width-`w` resolution proof. `CNF.RefutableInSize.cuttingPlanes` gives `(8 N + 1) s` lines for a CNF on `N` variables, using `CNF.IsProof.width_le`. `CuttingPlanes.exists_refutableInSize_iff_not_satisfiable` gives completeness.

[The pigeonhole module](../../Complexity/Logics/Propositional/CuttingPlanes/Pigeonhole.lean) proves the Cook–Coullard–Turán upper bound. For `n < m`, `CuttingPlanes.refutableInSize_pigeonhole` gives a refutation of `PHP^m_n` in at most `(n + 1) (m + 1)²` lines. With Haken's bound above, [the separation module](../../Complexity/Logics/Propositional/CuttingPlanes/Separation.lean) gives `two_pow_le_of_forall_refutableInSize_pigeonhole`: any map `f` that turns `s`-line cutting-planes refutations of `PHP^{n+1}_n` into `f s`-line resolution refutations satisfies `2^(n/24) ≤ f ((n + 1) (n + 2)²)`. `not_exists_polynomiallyBounded_refutableInSize_pigeonhole` states the corresponding non-polynomial conclusion. These are line-count statements about the given proof representations. They are not p-simulations between `ProofSystem` instances, which would also charge encodings and translation time. Tree-like cutting planes are not defined, so the fact that the pigeonhole refutation is tree-like is noted in the source but not stated in Lean.

The [checked examples](../../ComplexityTests/ProofComplexity/CuttingPlanes.lean) include a three-line refutation of `x ∧ ¬x`, a rounding step that cuts off the fractional point `(1/4, 1/4)`, and a case showing that division without the divisibility condition derives `0 ≥ 1` from the satisfiable `x ≥ 1`. They also cover soundness on a satisfiable CNF, a translated resolution refutation, and the pigeonhole and separation instances. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.CuttingPlanes`.

## Foundations for algebraic degree lower bounds

Two Boolean-analysis lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../Complexity/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `n!` is nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../Complexity/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, #U` are nonzero. The tests ([inclusion matrices](../../ComplexityTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../ComplexityTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped.

## Known Limitations

This section inventories resolution, cutting planes and their syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[complexitylib]: ../sources.md#complexitylib
