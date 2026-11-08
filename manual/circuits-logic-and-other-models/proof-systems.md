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
constant of this encoding. These count resamplings, not machine time. The existential Local Lemma
for the same formulas is `CNF.IsExactDistinct.satisfiable_of_exp_mul_le` in
`Complexity.Logics.Propositional.CNF.LocalLemma`: `Moser.degree φ i ≤ d` for every clause and
`Real.exp 1 * (d + 1) ≤ 2 ^ k` give satisfiability, with no algorithm. Its constant is better, but
it does not say how to find the assignment. Fortnow's Kolmogorov-complexity form of the
compression argument is in `Complexity.Logics.Propositional.CNF.Moser.Kolmogorov`. There the
complexity is `ecomplexity` for the explicit decoder `Moser.descriptionMethod φ k L`, not for a
universal machine. Under `3 ≤ k`, `CNF.IsExactDistinct k φ` and `degree φ i < 2 ^ (k - 3)`,
`Moser.not_exhausts_of_length_sub_le_ecomplexity` shows that a tape word `y` of length `n + t k`
whose complexity for `Moser.descriptionMethod φ k (k - 3)` is at least `n + t k - c` does not use
up a budget of `t > m + c` resamplings. The
[checked examples](../../ComplexityTests/Moser.lean) include a concrete run, its log, the
recovered tape and its description, and a formula where only the existential bound applies;
check them with `scripts/build.sh ComplexityTests.Moser`.

The general Moser–Tardos theorem for the variable form of the Local Lemma is in
`Complexity.Probability.MoserTardos` [mosertardos10]. The setting is finitely many independent
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
`(label, depth)` pairs in `Complexity.Probability.MoserTardos.Witness`. Lemma 2.1 is
`proper_witness`, the coupling `check_witness`, `measure_check_eq_prod` and, combined,
`table_witness_le`. Here `Proper` is the level independence proved inside Lemma 2.1(i), which
implies the paper's properness. The paper's Galton–Watson counting is replaced by a depth
induction, `sum_prod_shapes_le`. The model counts resamplings; it does not charge for sampling or
for detecting occurring events. Theorems 1.3 (the parallel version) and 1.4 (the deterministic
version) and the lopsided form are not formalized. The
[checked examples](../../ComplexityTests/MoserTardos.lean) give one fair coin, where the bound is
`x / (1 - x) = 1`, two dependent events on three coins that meet the hypothesis with equality, an
impossible event with `x = 0`, two complementary events for which no `x` satisfies the
hypothesis, and a concrete valid log on a fixed table whose witness tree is computed by `decide`
and passes its check. Check them with
`scripts/build.sh ComplexityTests.MoserTardos`.

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
proof; they do not prove its forest or contraction invariants.

[Difference tests](../../ComplexityTests/CyclicDifference.lean) show that ternary NAE maps to
an even delta-matroid of three weight-two tuples. [Exchange tests](../../ComplexityTests/DeltaMatroid.lean)
include odd exactly-one relations, the empty-coordinate case, and failures of exchange/evenness.
These mathematical prerequisites provide no planar embedding algorithm, edge-CSP solver or
planar complexity dichotomy yet. The full remaining objective is [#3091](https://github.com/cslib-community/complexitylib/issues/3091).

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

[The cut space of a multigraph](../../Complexity/Foundations/Combinatorics/Multigraph/CutSpace.lean) holds the edge-cut algebra that Tseitin lower bounds beyond resolution (polynomial calculus, SOS) are meant to use. Import `Complexity.Foundations.Combinatorics.Multigraph.CutSpace`. `Multigraph.edgeCut_symmDiff` sends a symmetric difference of vertex sets to the symmetric difference of their edge cuts, and `Multigraph.edgeCut_singleton` identifies the cut of one vertex with its edges other than self-loops. On a connected multigraph, `Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty` says that only `∅` and the set of all vertices have empty cuts. `Multigraph.three_mul_card_lt_of_card_edgeCut_lt` is the expansion dichotomy: a set of at most two thirds of the vertices that fewer than `e(G)` edges leave has fewer than a third of them. The [checked examples](../../ComplexityTests/Foundations/Combinatorics/Multigraph/CutSpace.lean) show that connectivity and the two-thirds hypothesis cannot be dropped; check them with `scripts/build.sh ComplexityTests.Foundations.Combinatorics.Multigraph.CutSpace`.

Interpolation modules extract circuits separating the two sides of a refuted conjunction. Monotone extraction supports clique/coloring lower-bound applications, and a separate polynomial-time file addresses encoded extraction. The distinction between semantic existence of an interpolant and a native efficient extraction algorithm follows the same design pattern as circuits and finite-model logic. See [interpolation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation.lean), [monotone extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/MonotoneExtraction.lean) and [native extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/PolyTime.lean).

[Semantic derivations](../../Complexity/Logics/Propositional/SemanticDerivation.lean) formalize Krajíček's communication route to interpolation, which is not tied to one proof system. Import `Complexity.Logics.Propositional.SemanticDerivation`. A line is a set of assignments, and `IsSemanticRefutation (initSets 𝒜 ℬ) D` says that each of the `k` lines of `D` is either a cylinder over an initial set, everything, or contains the intersection of two earlier lines, and that some line is `∅`. `IsSemanticRefutation.exists_dagProtocol` turns such a refutation into a dag-like Karchmer–Wigderson protocol with `k` inner nodes and communication `2 t`. This requires two per-line costs to be at most `t`: deciding whether the mixed assignment `(v, q, r)` lies in each line, and finding a coordinate at each `𝒜`-cylinder. For shared variables of type `Fin n`, `exists_circuit` and `exists_monotone_circuit` then give a separating circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates. The `_of_commComplexity_le` forms state this for lines with Krajíček's `CC` and `MCC_U` at most `t`; the monotone form assumes the models of `𝒜` are upward closed. This sharpens the bounds of Theorem 5.1, `(k + 2 n) · 2 ^ O(t)` and, in the monotone case, `(k + n) · 2 ^ O(t)`: the `2 n` answer nodes of the source's protocol are leaves here and cost nothing. `lt_of_forall_lt_size` is the transfer to line lower bounds. Only the monotone case for the `𝒜` side is stated. Cutting planes is the first proof-system client (see below); resolution refutations are not yet translated into semantic refutations. The [checked examples](../../ComplexityTests/ProofComplexity/SemanticDerivation.lean) apply every form to a three-line refutation of `x₀ = 1` against `x₀ = 0`; check them with `scripts/build.sh ComplexityTests.ProofComplexity.SemanticDerivation`.

## Clause space

Import `Complexity.Logics.Propositional.Resolution.SpaceWidth` for the definitions and the inequality, `Complexity.Logics.Propositional.Resolution.TseitinSpace` for the Tseitin corollaries, `Complexity.Logics.Propositional.Resolution.TreeLikeSpace` for tree-like refutations, or `Complexity.Logics.Propositional.Resolution.PigeonholeSpace` for Duplicator strategies and the pigeonhole bounds.

[Configuration-style resolution](../../Complexity/Logics/Propositional/Resolution/Space.lean) follows Esteban and Torán. It keeps a `Finset` of clauses in memory, and each move (`ConfigMove`) changes it by one of three rules (`CNF.ConfigStep`): download a clause of the formula, add the resolvent of two clauses in memory, or erase a clause. The resolution rule is that of `CNF.IsProof`, with no weakening. `CNF.configLTS φ s` is the cslib `LTS` of these moves, restricted to configurations of at most `s` clauses. It follows the same pattern as the pebbling library's `Cslib.Pebbling.blackPebbleGame`.

`CNF.RefutableInSpace φ s` holds when some `MTr` run from `∅` reaches a configuration containing `[]`. Space counts distinct clauses, and time (the number of moves) is not bounded. Clauses are lists, but this does not change the least space compared with clauses as sets: mapping clauses to their literal sets never increases space, and a refutation on sets lifts by fixing one list per set. The module proves the basic properties:

- soundness: `RefutableInSpace.not_satisfiable`;
- space is at most size: `RefutableInSize.refutableInSpace`;
- completeness: `exists_refutableInSpace_iff_not_satisfiable`;
- `RefutableInSpace.three_le`: space is at least `3` unless `[] ∈ φ`.

[The space–width module](../../Complexity/Logics/Propositional/Resolution/SpaceWidth.lean) proves the Atserias–Dalmau inequality (their Theorem 3) in the form of Theorem 1 of Filmus, Lauria, Mikša, Nordström and Vinyals (STACS 2014), whose constant `s + k - 3` it uses; Atserias and Dalmau's own constant is not claimed. `RefutableInSpace.refutableInWidth` says that if every clause has width at most `k`, clause space `s` gives a refutation of width `s + k - 3`, with truncated subtraction. Unlike that paper, the theorem does not assume `[] ∉ φ`. The contrapositive `RefutableInSpace.add_four_le` turns a width lower bound `¬ RefutableInWidth w` into the space bound `w + 4 ≤ s + k`.

The proof works for any Duplicator strategy. `DuplicatorStrategy.add_three_le` says that if Duplicator wins the existential `p`-pebble game on a formula whose clauses have width at most `k`, every refutation needs clause space `s` with `p + 3 ≤ s + k`. This is their Lemma 5 with the constant that yields Filmus et al.'s; the source's own constant is not quoted. `add_four_le` applies it to the strategy that Atserias and Dalmau's Lemma 2 builds from `¬ RefutableInWidth w` (below), when every clause has width at most `w`. Otherwise `w < k`, and `RefutableInSpace.three_le` is enough.

[The existential pebble module](../../Complexity/Logics/Propositional/Resolution/ExistentialPebble.lean) exports the game and its characterization of width. Import `Complexity.Logics.Propositional.Resolution.ExistentialPebble`. A partial assignment is a total assignment `σ` read on a finite set `d`, and `CNF.Falsifies σ d c` says that every literal of `c` is on a variable of `d` and false under `σ`. `CNF.DuplicatorStrategy φ k` is Atserias and Dalmau's Definition 2: a nonempty family of such assignments on at most `k` variables that falsify no clause of `φ`, closed under restriction, and extendable to any variable from fewer than `k` variables. `DuplicatorStrategy.not_refutableInWidth` is their Lemma 3 in the library's width convention: a strategy with `w + 1` pebbles rules out `RefutableInWidth w`. Conversely, `DuplicatorStrategy.ofNotRefutableInWidth` is their Lemma 2: if every clause has width at most `w` and there is no refutation of width `w`, the partial assignments on at most `w + 1` variables that falsify no clause derivable within width `w` form a strategy with `w + 1` pebbles. Together they give their Theorem 2 as `DuplicatorStrategy.nonempty_iff_not_refutableInWidth`, for formulas whose clauses have width at most `w`. The hypothesis on the clauses is needed: `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀ ∧ ¬x₁ ∧ ¬x₂` has no refutation of width `2`, but Spoiler wins with `3` pebbles. The source's side conditions and pebble counts are not quoted, because its symbols do not extract. The game has nothing to do with the black pebble game of `Complexity/Computability/Pebbling`.

[The pigeonhole space module](../../Complexity/Logics/Propositional/Resolution/PigeonholeSpace.lean) applies it to Atserias and Dalmau's Section 5 example. Import `Complexity.Logics.Propositional.Resolution.PigeonholeSpace`.

- [The extended pigeonhole formula](../../Complexity/Logics/Propositional/Pigeonhole/Extension.lean) `CNF.pigeonholeExt m n` (`EPHP^m_n`) replaces each width-`n` pigeon clause of `PHP^m_n` with a chain of start, step and stop clauses of width at most `3`. The chain runs through variables "pigeon `i` sits in a hole `≥ j`". `satisfiable_pigeonholeExt_iff` says it is satisfiable exactly when `m ≤ n`.
- `CNF.pigeonholeExtStrategy m n` is Duplicator's strategy on `EPHP^m_{n+1}` with `n + 1` pebbles: the partial assignments that agree with a placement of pigeons that is injective on the pebbled pigeons.
- So with `n + 1` holes there is no refutation of width `n` (`not_refutableInWidth_pigeonholeExt`). Stated per hole count, every refutation of `EPHP^m_n` has width at least `n` (`le_of_refutableInWidth_pigeonholeExt`) and clause space at least `n` (`le_of_refutableInSpace_pigeonholeExt`, through `RefutableInSpace.add_four_le` with `k = 3`). The number of pigeons is arbitrary.

The mathematical symbols of the available copy of Atserias and Dalmau's paper do not extract. So neither their exact clauses nor the pebble count of their Lemma 6 is quoted; the encoding, the strategy and these constants are ours. The clause space of the wide formula `PHP^m_n` itself, proved by Alekhnovich, Ben-Sasson, Razborov and Wigderson, is not treated, and their paper was not inspected.

[The Tseitin module](../../Complexity/Logics/Propositional/Resolution/TseitinSpace.lean) combines this with the width bound of Ben-Sasson and Wigderson:

- `Tseitin.minBalancedCut_le_of_refutableInSpace` gives `e(G) ≤ s + k - 3` on a connected multigraph whose vertices have at most `k` non-loop edges;
- `Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace` gives `h(G) |V| / 3 + 3 ≤ s + |D|` on a rotation map with `h(G) > 0`;
- `CNF.exists_forall_refutableInSpace_le` is a family with explicit constants. For `n ≥ 4392000` it has at most `120 n` variables, `2 ^ 120 · n` clauses of width at most `120`, and every refutation in clause space `s` has `n ≤ 36000 s`. It shares its setup with the size family of the Tseitin-expander module through `Tseitin.exists_expander_tseitinFormula`. That lemma gives the Tseitin formula of the `120`-regular expander on `n ≥ 2` vertices with its explicit constants: connectivity, degree at most `120`, `e(G) ≥ n / 18000`, and the variable and clause counts.

As with the size bound, the expanders come from a counting argument.

[The tree-like module](../../Complexity/Logics/Propositional/Resolution/TreeLikeSpace.lean) proves Esteban and Torán's bound: clause space is at most logarithmic in tree-like size. The statement is taken from Torán's survey (Bulletin of the EATCS 83, 2004, Theorem 9), which states `tree-size(F) ≥ 2 ^ space(F) - 1`. The original paper was not inspected. The survey's pebble game (Definition 7, identified with its space by Lemma 8) lets an inference shift a pebble from a premise to the resolvent, so its space is at most one less than clause space here. `CNF.configLTS` keeps both premises, so every bound here is one larger:

- `Derivation.strahler` is the Horton–Strahler number of a tree-like derivation, the height of the largest complete binary tree embedded in it. It is the Ehrenfeucht–Haussler rank `Cslib.DecisionTree.rank` of the derivation's decision tree `Derivation.toDecisionTree` (`Derivation.strahler_eq_rank_toDecisionTree`). `Derivation.two_pow_strahler_add_one_le` gives `2 ^ (r + 1) ≤ S + 1` for a derivation of `S` nodes, from `DecisionTree.two_pow_rank_le_leafCount` (a tree of rank `r` has at least `2 ^ r` leaves).
- `Derivation.refutableInSpace` gives clause space `r + 2`: derive the premise of larger number first and keep it. This matches the black pebbling price `h + 2` of the complete binary tree of height `h ≥ 1` in `Complexity/Computability/Pebbling/BinaryTree.lean`.
- `Derivation.refutableInSpace_log` gives clause space `log₂ (S + 1) + 1`. Its contrapositive, `Derivation.two_pow_le_size_add_one`, turns `¬ RefutableInSpace s` into `2 ^ s ≤ S + 1`; `x ∧ ¬x` attains it.
- `CNF.refutableInSpace_of_not_satisfiable` refutes every unsatisfiable formula on `n` variables in clause space `n + 2`, the survey's `n + 1`. It splits on a variable (`CNF.exists_derivation_strahler_le`), lifting tree-like refutations of the restrictions with `Derivation.exists_of_restrict`.

The [checked examples](../../ComplexityTests/ProofComplexity/Space.lean) refute `x ∧ ¬x` in space `3` and show that space `2` is impossible. They also give a five-line refutation that erasure keeps in space `3`, and a formula with a width-`3` clause on which the inequality is attained: `k = s = 3`, width `3` and not `2`. On the same formula Spoiler wins with `3` pebbles, so Lemma 2 needs its width hypothesis. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.Space`. The [tree-like examples](../../ComplexityTests/ProofComplexity/TreeLikeSpace.lean) compute Strahler numbers, show that `x ∧ ¬x` attains both the Esteban–Torán bound and the bound `n + 2`, and turn the Tseitin space bound into tree-like size at least `2 ^ 121 - 1`. On a unit-propagation chain with a 7-node refutation, the Strahler bound gives the optimal space `3` where the logarithmic bound gives `4`. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.TreeLikeSpace`. The [pigeonhole examples](../../ComplexityTests/ProofComplexity/PigeonholeSpace.lean) build Duplicator strategies from satisfying assignments and with no pebble, and show there is none for `x ∧ ¬x` with one pebble. They also check that `EPHP^3_2` is refutable but not in width `1`, and that `EPHP^6_5` is refutable but needs clause space `5`. Lemma 2 rebuilds a `4`-pebble strategy on `EPHP^m_4` from its width bound, and `add_three_le` gives the space bound from the pigeonhole strategy directly. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.PigeonholeSpace`.

Not yet formalized:

- clause space of the wide pigeonhole formula and of random `k`-CNFs;
- total and variable space;
- time–space trade-offs and pebbling formulas;
- the polynomial-calculus analogue, degree versus space, which is open.

## Cutting planes

Import `Complexity.Logics.Propositional.CuttingPlanes.Separation` for everything below except
interpolation, or the smaller modules `CuttingPlanes`, `CuttingPlanes.Resolution` and
`CuttingPlanes.Pigeonhole` under `Complexity.Logics.Propositional`. Interpolation is in
`Complexity.Logics.Propositional.CuttingPlanes.Interpolation`.

[Cutting planes](../../Complexity/Logics/Propositional/CuttingPlanes.lean) is the line-based proof system on integer linear inequalities over 0/1 variables. `Cslib.Logic.PL.Ineq V` has finitely supported coefficients `V →₀ ℤ` and an integer bound and means `∑ aᵥ xᵥ ≥ bound`; inequalities form an additive group, and `Ineq.Holds σ I` evaluates `I` under an assignment `σ : V → Bool`. `CuttingPlanes.IsProof Γ ls` lists a proof from the set `Γ` from its last line to its first. A line is a member of `Γ`, an axiom `xᵥ ≥ 0` (`Ineq.nonneg`) or `-xᵥ ≥ -1` (`Ineq.leOne`), the sum of two earlier lines, an earlier line times a positive natural number, or an earlier line divided by a positive `c` that divides every coefficient. In the last case `Ineq.div` rounds the bound up. Size is the number of lines (`DerivableInSize`, and `RefutableInSize` for deriving `Ineq.contra`, which is `0 ≥ 1`). Coefficient sizes are not measured. `IsProof.holds` gives soundness. A clause translates to `∑_{v ∈ C} xᵥ + ∑_{¬v ∈ C} (1 - xᵥ) ≥ 1` over its *distinct* literals (`Clause.toIneq`, with `Clause.holds_toIneq_iff`), and `CNF.toIneqs φ` collects these inequalities.

To build a derivation, combine the `DerivableInSize` lemmas `hyp`, `nonneg`, `leOne`, `literal`, `add`, `smul`, `div`, `add_sum` and `sum`. Each lemma states its exact line count. Two lemmas help identify the resulting line: `Ineq.div_eq_of` recognizes a rounded division, and the `coeff_*`/`bound_*` simp lemmas, `ext`, `abel` or `module` compute the sums. `DerivableInSize.extend` replays a derivation from `Δ` on top of an existing proof containing the lines of `Δ`.

[The simulation module](../../Complexity/Logics/Propositional/CuttingPlanes/Resolution.lean) translates each resolution step into at most `2 w₁ + 2 w₂` cutting-planes lines, where `wᵢ` are the widths of the two premises. Resolution here has no weakening and its resolvent is a union, so literals occurring in only one premise must be added as axioms before dividing by two. Textbook constant-cost simulations assume weakening. Hence `CNF.IsProof.cuttingPlanes` gives `(4 w + 1) s` lines for an `s`-line, width-`w` resolution proof. `CNF.RefutableInSize.cuttingPlanes` gives `(8 N + 1) s` lines for a CNF on `N` variables, using `CNF.IsProof.width_le`. `CuttingPlanes.exists_refutableInSize_iff_not_satisfiable` gives completeness.

[The pigeonhole module](../../Complexity/Logics/Propositional/CuttingPlanes/Pigeonhole.lean) proves the Cook–Coullard–Turán upper bound. For `n < m`, `CuttingPlanes.refutableInSize_pigeonhole` gives a refutation of `PHP^m_n` in at most `(n + 1) (m + 1)²` lines. With Haken's bound above, [the separation module](../../Complexity/Logics/Propositional/CuttingPlanes/Separation.lean) gives `two_pow_le_of_forall_refutableInSize_pigeonhole`: any map `f` that turns `s`-line cutting-planes refutations of `PHP^{n+1}_n` into `f s`-line resolution refutations satisfies `2^(n/24) ≤ f ((n + 1) (n + 2)²)`. `not_exists_polynomiallyBounded_refutableInSize_pigeonhole` states the corresponding non-polynomial conclusion. These are line-count statements about the given proof representations. They are not p-simulations between `ProofSystem` instances, which would also charge encodings and translation time. Tree-like cutting planes are not defined, so the fact that the pigeonhole refutation is tree-like is noted in the source but not stated in Lean.

[The interpolation module](../../Complexity/Logics/Propositional/CuttingPlanes/Interpolation.lean) proves Krajíček's feasible interpolation for cutting planes (Theorem 6.4). Alice's system `ΓA` is a set of inequalities over `Fin n ⊕ Y` and Bob's `ΓB` a set over `Fin n ⊕ Z`, with `Y` and `Z` finite. A refutation is an `IsProof` from their images under `Ineq.relabel (Sum.map id Sum.inl)` and `Ineq.relabel (Sum.map id Sum.inr)` in `Fin n ⊕ (Y ⊕ Z)` that contains `Ineq.contra`. `IsProof.isSemanticRefutation` turns it into a semantic refutation with as many lines. Deciding a line costs `⌈log₂ (2 M |Y| + 1)⌉ + 1` bits when its `y`-coefficients are at most `M` (`ecomplexity_memRight_holds_le`). Binary search at an inequality of `ΓA` with shared coefficients at most `M₀` costs `⌈log₂ n⌉ (⌈log₂ (2 M₀ n + 1)⌉ + 1)` bits (`ecomplexity_search_holds_le`, built on `Protocol.exists_search_lt`). For `t` at least both costs, `IsProof.exists_circuit` gives a circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates, where `k` is the number of lines. The circuit is true on every `u` with `ΓA(u, q)` for some `q` and false on every `v` with `ΓB(v, r)` for some `r`. `IsProof.exists_monotone_circuit` gives a monotone circuit when the shared coefficients of `ΓA` are nonnegative. The `_of_abs_coeff_le` forms take Krajíček's single bound `M` on every coefficient of the refutation; `2 ^ t` is then `(M N) ^ O(1) (M n) ^ O(log n)`, as in the source. The separate bounds `M₀` and `M` matter for clause translations, where `M₀ = 1`. Not yet stated: the monotone case in which the shared variables occur in `ΓB` with nonpositive coefficients only, which needs the `ℬ`-monotone semantic theorem, and the clique–colouring lower bound of Corollary 7.3. The circuits are non-uniform; no extraction algorithm is given. The [interpolation examples](../../ComplexityTests/ProofComplexity/CuttingPlanesInterpolation.lean) refute `{y ≥ 1, x₀ - y ≥ 0}` against `{-x₀ ≥ 0}` through the private variable `y` and check that the interpolant computes `x₀`. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.CuttingPlanesInterpolation`.

The [checked examples](../../ComplexityTests/ProofComplexity/CuttingPlanes.lean) include a three-line refutation of `x ∧ ¬x`, a rounding step that cuts off the fractional point `(1/4, 1/4)`, and a case showing that division without the divisibility condition derives `0 ≥ 1` from the satisfiable `x ≥ 1`. They also cover soundness on a satisfiable CNF, a translated resolution refutation, and the pigeonhole and separation instances. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.CuttingPlanes`.

## Frege proofs

Import `Complexity.Logics.Propositional.Frege.Resolution` for everything below, or
`Complexity.Logics.Propositional.Frege` for the proof system alone.

[The Frege module](../../Complexity/Logics/Propositional/Frege.lean) fixes one Hilbert-style proof system. Cook and Reckhow [cookreckhow79][cookreckhow79] require a Frege system to have finitely many sound schemes and rules that are also implicationally complete. This system is complete by the standard argument for its classical axiomatization, but the library does not prove that yet ([#3069](https://github.com/cslib-community/complexitylib/issues/3069)). Formulas are cslib's `Cslib.Logic.PL.Proposition` over the atoms `WithBot V` (`Cslib.Logic.PL.Frege.Formula`), with cslib's `⊥`, the atom `⊥`, read as falsity, and cslib's `Proposition.neg φ = φ → ⊥`. `Formula.eval σ` evaluates a formula under `σ : V → Bool`, because cslib's propositions carry no Boolean semantics. `IsAxiom` lists the schemes K, S and double-negation elimination for `→` and `⊥`, together with introduction and elimination schemes for `∧` and `∨`; modus ponens is the only rule. `IsProof Γ L` lists a proof from the hypotheses `Γ` from its last line to its first, as resolution and cutting planes do, and its size is the number of lines. `DerivableInSize Γ φ n` says that `φ` has a proof of at most `n` lines, as for cutting planes. `IsProof.eval` gives soundness.

Two lemmas build proofs with explicit line counts. `IsProof.cut` replays a proof from `Γ ++ Δ` on top of a proof from `Γ` that already contains the formulas of `Δ`, adding at most as many lines as the replayed proof has, so later steps can reuse earlier lines. `IsProof.deduction` is the deduction theorem with linear overhead. A proof from `Γ ++ Δ` becomes a proof from `Γ` that contains `Δ ⇒ φ` (`Formula.imps`) for each line `φ`, with at most `10 (|Δ| + 1)` lines per original line. Discharging the hypotheses one at a time would instead multiply the size by a constant for each hypothesis.

[The simulation module](../../Complexity/Logics/Propositional/Frege/Resolution.lean) translates a clause into `¬ℓ₁ → ⋯ → ¬ℓₖ → ⊥` over its distinct literals (`Clause.toFormula`, with `Clause.eval_toFormula`). `Frege.derivableInSize_toFormula_resolvent` derives the formula of a resolvent from the formulas of its premises in at most `stepBound w = 10 (2 w + 1) (42 w + 23)` lines, where `w` is the larger premise width. The pivot need not occur in either premise. `CNF.IsProof.frege` turns an `s`-line resolution proof of width at most `w` into a Frege proof of at most `stepBound w * s` lines that contains the formula of every line. `CNF.RefutableInSize.frege` turns an `s`-line refutation of a CNF on `N` variables into a Frege proof of `⊥` of at most `stepBound (2 N) * s` lines. `CNF.exists_frege_refutation_iff_not_satisfiable` combines this with resolution completeness and Frege soundness: Frege refutes exactly the unsatisfiable CNFs.

These are line counts. Each translated line has `O(w)` connectives, but formula size is not measured, and none of these results is a p-simulation between `ProofSystem` instances. The library does not yet have implicational completeness of Frege, machine-level p-simulations, the mutual p-simulation of Frege systems or Extended Frege; [#3069](https://github.com/cslib-community/complexitylib/issues/3069) tracks them.

The [checked examples](../../ComplexityTests/ProofComplexity/Frege.lean) include a five-line proof of `p → p` built from the constructors, clause formulas and their semantics, a translated refutation of `x ∧ ¬x`, soundness on a satisfiable CNF, and one resolution step on width-10 clauses. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.Frege`.

## Foundations for algebraic degree lower bounds

Two Boolean-analysis lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../Complexity/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `n!` is nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../Complexity/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, #U` are nonzero. The tests ([inclusion matrices](../../ComplexityTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../ComplexityTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped.

## Sum-of-squares

Import `Complexity.Logics.Propositional.Algebraic.SumOfSquares.TseitinExpander` for everything below, or the smaller modules `SumOfSquares.Basic`, `SumOfSquares.Parity` and `SumOfSquares.Tseitin` under `Complexity.Logics.Propositional.Algebraic`.

[The basic module](../../Complexity/Logics/Propositional/Algebraic/SumOfSquares/Basic.lean) defines sum-of-squares (Positivstellensatz) refutations over an ordered commutative ring `R`. `SOS.Refutation F d` refutes the equations `f = 0`, `f ∈ F` (a list of `MvPolynomial σ R`) by an identity `∑ᵢ gᵢ fᵢ + ∑ₖ cₖ sₖ² = -1` with weights `cₖ ≥ 0` in `R`. Degree is counted per term: every product `gᵢ fᵢ` has total degree at most `d` and every `2 deg sₖ ≤ d`. Over `ℝ` or `ℚ`, or any ring in which every nonnegative element is a sum of squares, the weights can be absorbed into the squares without raising the degree; over a general ordered ring they make the proof system stronger. `SOS.RefutableInDegree F d` says such a refutation exists (`refutableInDegree_iff`, `Refutation.refutableInDegree`). Boolean or `±1` axioms are not built in; an encoding lists them in `F`. `SOS.PseudoExpectation F d` is a linear map `Ẽ` with `Ẽ 1 = 1`, `Ẽ (s²) ≥ 0` for `2 deg s ≤ d`, and `Ẽ (q f) = 0` for `f ∈ F` and `deg (q f) ≤ d`. These follow [Barak and Steurer][barak-steurer16], lecture "The sos algorithm over general domains": Definition 1 and the remark after Theorem 2 for refutations, and Definitions 5 and 7 for pseudo-expectations. The pseudo-expectation condition here asks `Ẽ (q f) = 0` for every multiplier `q`, not only for sums of squares. `PseudoExpectation.not_refutableInDegree` is the easy direction of the duality (Theorem 8 of that lecture with `f = -1`; Theorem 19 of the lecture "Mathematical definitions"): over a strictly ordered ring, a degree-`d` pseudo-expectation rules out degree-`d` refutations. `PseudoExpectation.ofEval` is evaluation at a common zero, and `RefutableInDegree.not_exists_eval_eq_zero` is soundness. To build an explicit refutation, use `RefutableInDegree.of_list` with a list of pairs `(g, f)`. The converse of the duality (hyperplane separation) is not formalized.

[Parity systems](../../Complexity/Logics/Propositional/ParitySystem.lean) are lists of equations `⊕_{i ∈ S} xᵢ = b` with `S : Finset σ`. `ParitySystem.Derives P w S b` is width-`w` derivation: start from `0 = 0` and the equations of `P`, and sum two derived equations by symmetric difference, keeping every line, axioms included, at most `w` variables wide. Schoenebeck's Definition 10 does not bound the axioms, so "no width-`w` derivation of `0 = 1`" is a weaker hypothesis here and the lower bounds are correspondingly stronger. [The Tseitin parity module](../../Complexity/Logics/Propositional/ParitySystem/Tseitin.lean) (`Complexity.Logics.Propositional.ParitySystem.Tseitin`) adds `ParitySystem.tseitin ends χ`, the Tseitin parity system of a multigraph, and `holds_tseitin_iff_eval_tseitinFormula` matches it with `CNF.tseitinFormula`; the core module does not import the Tseitin CNF.

[The parity module](../../Complexity/Logics/Propositional/Algebraic/SumOfSquares/Parity.lean) gives the `±1` encoding `ParitySystem.toPolys R P`: `∏_{i ∈ S} Xᵢ - (-1)^b` for every equation and `Xᵢ² - 1` for every variable. `exists_eval_eq_zero_iff` says its common zeros in a strictly ordered field are the satisfying assignments. `ParitySystem.pseudoExpectation` is the construction of [Schoenebeck][schoenebeck08], Lemma 13, defined whenever `¬ P.Derives d ∅ true`. It sends `∏_{i ∈ T} Xᵢ` to `(-1)^c` if `⊕_T x = c` is derivable in width `d`, and to `0` otherwise (`parityValue`, `pseudoExpectation_prod_X`). General monomials are first reduced modulo `Xᵢ² = 1` through `Finsupp.oddSupport`. Positive semidefiniteness is `sum_sum_mul_parityValue_nonneg`: the classes of "`A ∆ B` is derivable" split the moment matrix into rank-one blocks. `not_sos_refutableInDegree_toPolys` is the resulting lower bound: no width-`d` derivation of `0 = 1` implies no SOS refutation of degree at most `d`. This is a statement about the sum-of-squares proof system with this pseudo-expectation. Schoenebeck's Lasserre vector solution is not constructed. The author's copy consulted (December 2008) states Lemma 13 for the `w/2`-th round of Lasserre, and round `r` constrains moments of degree up to `2 r`; versions of the paper differ on this constant, as recorded in the source entry.

[The Tseitin module](../../Complexity/Logics/Propositional/Algebraic/SumOfSquares/Tseitin.lean) shows `not_derives_tseitin_empty_true`: below width `e(G)` (`Multigraph.minBalancedCut`), derivations from a Tseitin system on a connected multigraph stay among cuts of sets smaller than a third of the vertices, so they never reach `0 = 1`. Grigoriev's theorem follows. `Tseitin.minBalancedCut_le_of_sos_refutableInDegree` says that a degree-`d` refutation of the `±1` encoding of a Tseitin system on a connected multigraph has `e(G) ≤ d`, over every strictly ordered commutative ring. [The expander module](../../Complexity/Logics/Propositional/Algebraic/SumOfSquares/TseitinExpander.lean) gives `h(G) |V| / 3 ≤ d` for rotation maps (`Tseitin.edgeExpansion_mul_card_div_three_le_of_sos_refutableInDegree`). Its family `ParitySystem.exists_forall_sos_refutableInDegree_le` has, for `n ≥ 2`, `n` equations of at most `120` variables on at most `120 n` variables, and every refutation has `n ≤ 18000 d`. The linear bound is Grigoriev's; the constants `120` and `18000` come from the library's expanders (`RotationMap.expander`, `RotationMap.le_edgeExpansion_expander`, edge expansion at least `1 / 6000`), not from the source. The expanders are obtained non-constructively. Barak and Steurer's lecture "Higher-degree integrality gaps", Lemma 24, states the Tseitin case for `(1 + ε)`-vertex-expanding `d`-regular graphs with all charges `1` and the `0/1` encoding (degree `n / 4`). The theorem here measures expansion by `e(G)`, allows any multigraph and charges, and uses the `±1` encoding. Random `3`-XOR (Barak and Steurer, Theorem 2), Grigoriev's knapsack bound and the `0/1` encoding are not treated. [Grigoriev's paper][grigoriev01] was not consulted, so its locator is unverified. The relevant statements were checked against Schoenebeck's Lemma 13 and Barak and Steurer's lecture "Higher-degree integrality gaps", Lemmas 7 and 24 and Theorem 2.

The [checked examples](../../ComplexityTests/ProofComplexity/SumOfSquares.lean) treat the triangle with one charged vertex. It is unsatisfiable, width-`2` derivations reach `0 = 1`, and Schoenebeck's pseudo-expectation of degree `1` exists, so `SOS.PseudoExpectation` is inhabited for an unsatisfiable system. There is no refutation of degree `1`. An explicit refutation of degree `2`, with one square of weight `2`, shows that `e(G) ≤ d` is attained. With two charged vertices the system is satisfiable, and point evaluation rules out refutations of every degree. On `K₄`, Schoenebeck's pseudo-expectation of degree `3` exists, so there is no refutation of degree `3`. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.SumOfSquares`.

## Known Limitations

This section inventories resolution, including clause space, cutting planes, semantic derivations, Frege proofs, sum-of-squares and their syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[barak-steurer16]: ../sources.md#barak-steurer16
[complexitylib]: ../sources.md#complexitylib
[cookreckhow79]: ../sources.md#cookreckhow79
[grigoriev01]: ../sources.md#grigoriev01
[mosertardos10]: ../sources.md#mosertardos10
[schoenebeck08]: ../sources.md#schoenebeck08
