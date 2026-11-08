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
The complete explicit-table edge solver is documented below. Planar embedding recognition,
geometric realization and the full complexity dichotomy remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

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
malformed widths, repeated rows, contraction cases and framed size calculations. These operation
lemmas supply executable operations and quantitative bounds. Mathematical closure and
whole-instance correctness are documented separately below.

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

These are finite encoding and numerical-verification results; the indexed duality and lifting
theorems below extend their mathematical interface. Geometric realization, identifying the outer
face across disconnected components and bare-instance recognition/construction remain open.
The complete explicit-table edge solver is documented below. Exact relation-arity and satisfiability guards are
separate: a false nullary relation passes the port-order check. Rejection of a supplied toroidal
rotation does not prove that its graph is nonplanar. The full objective remains
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Indexed duality and Boolean difference lifting

Import `Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Dual`,
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

The [dual and lifting tests](../../ComplexityTests/RotationDual.lean) check actual bridge, loop
and digon dual data; a toroidal obstruction; disconnected point/edge mixtures; duplicate
vertex declarations; names of size `2^100`; and the endpoint guard. The generic
`Matrix.endpointIncidence` API is in
`Complexity.Foundations.LinearAlgebra.Matrix.EndpointIncidence`; loops contribute twice and
cancel over `ZMod 2`, while parallel column positions stay distinct. Finite permutation orbit
transport is shared through `Complexity.Foundations.GroupTheory.Perm.Doubled`.

These are combinatorial duality and lifting results, reconstructing the graph prerequisite in
Dvořák–Kupec, §3, printed p. 439. The checked compiler below supplies the native
supplied-certificate CSP reduction, followed by the complete native edge solver below.
Geometric realization, bare rotation recognition and final planar assembly remain open
under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Face boundaries and closed-passage intersection parity

Import `Complexity.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity`.
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

The [complete regression clients](../../ComplexityTests/RotationIntersection.lean) include
bridges, singleton loop faces, parallel digons, degree-eight multiple passages, disconnected
sparse names and empty supports. The interlaced two-loop torus has odd intersection parity
and fails the genus hypothesis. The [scoped audit](../../ComplexityTests/RotationIntersectionAudit.lean)
checks stored declarations and environment linters. These are original finite-map proofs;
they do not establish drawing operations, geometric realization, Hanani–Tutte, recognition
or the full planar dichotomy. The checked guide's “Face Boundaries and Intersection Parity”
section gives complete generic applications.

## Ordered incidence-to-polygon rotations

Import `Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler`.
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

The [primal rotation tests](../../ComplexityTests/CSPPrimalRotation.lean) cover unary loops,
repeated arguments and identical constraints, sparse `2^100` labels, disconnected/empty bodies,
malformed declared arity, the nullary guard, and an ordered toroidal example where both
numerical predicates fail. General face-quotient cardinality facts are in
`Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts`; dense vertex
counts reuse the existing component-vertex set API. Incidence endpoint declaration now lives
at its source in `Problems.CSP.Incidence`, with its name and certificate clients preserved.

This reconstructs the finite maps behind Dvořák–Kupec's ordered face model, printed p. 434.
`polygonGraph` is an explicit list construction; abstract rotation/equivalence inverses are
proof data. The supplied-certificate compiler below supplies a native executable stage.
Geometric realization, bare recognition and the complete
planar CSP reduction/solver remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Checked cyclic-difference edge compiler

Import `Complexity.Computability.PolyTime.CSP.CyclicDifference.Spec` for
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
these counts alone are not its runtime certificate. The [compiler tests](../../ComplexityTests/CSPCyclicCompiler.lean)
execute SAT/UNSAT NAE examples, long boundaries, nullaries, malformed and toroidal rotations,
and binary labels/indices up to `2^250`.

The compiler reuses the now-public runtime helpers `orbitBool_polyTime`,
`faceTable_polyTime` and `argumentNextIndex_polyTime`, preserving their statements,
proofs and local automation. This implements the supplied numerical-certificate stage of
Dvořák–Kupec §3, printed pp. 439–440, Lemma 5/Corollary 4/Theorem 2; bounded scans and
parity-chain implementation are original. The complete explicit-table solver below supplies
the edge algorithm. Geometric realization, bare recognition and the full planar dichotomy remain
open under
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
certificates remain those of `PolyTime.CSP.Table`. The whole-instance mathematical layer appears below;
the complete native solver appears below. The full planar dichotomy remains open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

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
prefix is invalid. This routine takes an improving comparison labeling as input. The fresh
forest search below instead starts from the base labeling alone and stops at exhaustion,
augmentation or a blossom. The contraction/lifting entry below supplies the mathematical
next step, followed by the complete native edge solver. The planar dichotomy remains open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

For explicit tables, import `Complexity.Computability.PolyTime.CSP.Edge.Augmenting`.
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
answer. [Native augmentation tests](../../ComplexityTests/EdgeCSPAugmentingNative.lean) exercise
returned paths, both phases, width rejection, empty/nullary constraints and sparse binary names.
The supplied improving comparison remains necessary for this two-phase routine. The fresh search
below has no comparison input, and its native compiler is documented separately below.
The whole-instance mathematical layer and complete native edge solver are documented below.

The reusable scan lives in `CSP.Occurrence.Enumeration`: `incidenceList` and
`occurrences_eq_map_incidenceList` connect typed occurrences to the existing ordered record list.
`PolyTime.CSP.Occurrence` supplies `encOccurrenceRecord` and
`computableInPolyTime_occurrences` without importing graph construction. Both incidence graphs
and the native augmentation compiler use that same enumeration and certificate.

## Timestamped f-DAGs and local surgery

Import `Complexity.Logics.Propositional.CSP.Edge.DAGPaths` for finite incidence DAGs, their
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
timestamp and handles timestamp zero. See [DAG tests](../../ComplexityTests/EdgeCSPDAG.lean) for repeated
original constraints, exact deletion, extra-child rerooting, meeting paths, odd parity and failed
invariants. The fresh search below derives these DAG hypotheses from its actual execution;
whole-instance contraction/lifting is supplied below; the full planar endpoint remains open under
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

`Complexity.Logics.Propositional.CSP.Edge.Walk.Operations` supplies disjoint linked-trail
concatenation, trail reversal and f-prefix inheritance. Reversal preserves the underlying
trail, but arbitrary f-walk reversal can fail even with even delta-matroid constraints.
The [operation tests](../../ComplexityTests/EdgeCSPWalkOperations.lean) exhibit that failure, overlapping
incidence rejection and why endpoint consistency needs a positive proper prefix.

## Fresh forest search and its three outcomes

Import `Complexity.Algorithms.Lean.EdgeCSP.Forest.Blossom` and
`Complexity.Algorithms.Lean.EdgeCSP.Forest.Optimality`. `Forest.search sem f` executes
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
[kernel-checked counterexample](../../ComplexityTests/EdgeCSPBlossomCopies.lean) satisfies
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
Import `Complexity.Foundations.Data.BitString.DeltaMatroid.ExchangeBound` separately to use
the local disagreement-count lemma directly.

[Forest execution tests](../../ComplexityTests/EdgeCSPForest.lean),
[terminal tests](../../ComplexityTests/EdgeCSPForestTerminal.lean),
[event tests](../../ComplexityTests/EdgeCSPForestEvents.lean) and
[optimality tests](../../ComplexityTests/EdgeCSPForestOptimality.lean) cover both ancestor cases,
nonempty preparation, repeated constraints, timestamp zero, odd parity and sparse binary names.
The exhausted example with a connected feasible-pair graph still has two unavoidable defects.
These mathematical results compose with the native compiler and whole-instance contraction/lifting
below, followed by the complete native edge solver. The full planar dichotomy remains open;
[#3091](https://github.com/cslib-community/complexitylib/issues/3091) stays open.

## Native fresh forest search

Import `Complexity.Computability.PolyTime.CSP.Edge.Forest.Spec` for the program, native
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
[native forest tests](../../ComplexityTests/EdgeCSPForestNative.lean) cover all three outcomes,
partial meetings, repeated original constraints, scan order, malformed tables, width rejection,
invalid indices and names up to `2^250`. An end-to-end client derives a valid zero-defect labeling
from the actual decoded augmentation. The existing native augmentation regression suite remains
unchanged. The complete recursive solver appears below; geometric realization/recognition
and the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Whole-instance blossom contraction and lifting

Import `Complexity.Algorithms.Lean.EdgeCSP.Blossom.Optimality` for executable projection,
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
[Contraction tests](../../ComplexityTests/EdgeCSPBlossomContraction.lean) and
[lifting tests](../../ComplexityTests/EdgeCSPBlossomLifting.lean) execute nonempty preparation,
repeated original constraints, grouped ports, honest one-hot references, `r=b` accounting,
sparse names up to `2^250`, forward projection and an actual optimal comparison whose outside
values change. The complete native solver follows. Recognition/geometric correspondence,
planar hardness and full
[#3091](https://github.com/cslib-community/complexitylib/issues/3091) remain open.

## Complete native even edge-CSP solver

Import `Complexity.Computability.PolyTime.CSP.Edge.Solver.Endpoint`. In
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

This completes the explicit-table edge algorithm of KKR v6, Theorem 21 (printed p. 8), Algorithm 1
(p. 10), Theorem 24 and §5.3 (pp. 11–13), using the proved search, contraction and lifting layers.
The one-improvement recursion organization and full framed-bit bookkeeping are original.
The shared `EdgeAugmenting.buffer_eq` now lives beside `labeling_map` in `Edge.Buffer`;
`recordAt_index`, `finish_eq` and the narrow `EdgeForest` projection/index certificates are public
for reuse, with their existing local automation preserved.

[Solver tests](../../ComplexityTests/EdgeCSPSolver.lean) give complete ordinary-import clients,
including SAT/UNSAT units, nonempty blossom preparation, repeated original constraint copies,
changed outside comparison values, `r=b`, multiple improvements, every model guard and sparse
names up to `2^250`. [Buffer-only tests](../../ComplexityTests/EdgeCSPSolverBuffer.lean) check the
shared width bridge. The guide checks the native P endpoint, all-raw solver certificate,
optimality theorem and concrete decisions. Geometric realization/recognition, ordered planar
hardness transfer and final dichotomy assembly remain open under
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

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

These Figure 1 results concern finite relation semantics. Geometric realization and substitution,
a hardness theorem and a new native runtime certificate remain part of
[#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Ordered normalization from a cyclic exchange failure

Import `Complexity.Logics.Propositional.CSP.Planar.Normalization`. For any arity `n`,
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
The [normalization tests](../../ComplexityTests/PlanarNormalization.lean) exercise failed-exchange
families at arities 6, 8 and 12, repeated caps, a feasible-quartet finish, proper-support
compression, rotation, wraparound deletion, actual auxiliary witnesses and empty/nullary guards.
The guide composes the construction with its gadget and size bounds using ordinary imports.

These are combinatorial and finite-semantic bounds. Relation decisions and a chosen construction
are fixed-relation data; no uniform native runtime or binary encoded-size bound is asserted.
Geometric realization of the recorded operations, ordered planar substitution, hardness and
completion of the full planar dichotomy remain open under [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

## Original-language gadgets for the nonselfdual branch

Import `Complexity.Logics.Propositional.CSP.Planar.OneInThree.Gadget`.
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
relations are distinct from unary constant operations. The [minor and triangle tests](../../ComplexityTests/PlanarNonSelfDual.lean),
[rotation tests](../../ComplexityTests/PlanarNonSelfDualRotation.lean) and
[interpreter tests](../../ComplexityTests/PlanarConstructionGadget.lean) cover actual witnesses,
rejection, fresh auxiliaries, nullary atoms and malformed widths. In particular, the interpreter
tests derive the gadgets from a single one-in-three symbol without primitive pins or disequality.

These results prove finite primitive-positive semantics. The selected witnesses are fixed-language
data; no uniform preprocessing cost is asserted. The recorded recipes and concrete bodies support
subsequent geometric proofs, but do not establish ordered planar substitution, a native reduction
or planar hardness. Those obligations and the full planar dichotomy remain open under
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
