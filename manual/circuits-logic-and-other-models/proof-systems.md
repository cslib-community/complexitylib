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

[Semantic derivations](../../Complexity/Logics/Propositional/SemanticDerivation.lean) formalize Krajíček's communication route to interpolation, which is not tied to one proof system. Import `Complexity.Logics.Propositional.SemanticDerivation`. A line is a set of assignments, and `IsSemanticRefutation (initSets 𝒜 ℬ) D` says that each of the `k` lines of `D` is either a cylinder over an initial set, everything, or contains the intersection of two earlier lines, and that some line is `∅`. `IsSemanticRefutation.exists_dagProtocol` turns such a refutation into a dag-like Karchmer–Wigderson protocol with `k` inner nodes and communication `2 t`. This requires two per-line costs to be at most `t`: deciding whether the mixed assignment `(v, q, r)` lies in each line, and finding a coordinate at each `𝒜`-cylinder. For shared variables of type `Fin n`, `exists_circuit` and `exists_monotone_circuit` then give a separating circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates. The `_of_commComplexity_le` forms state this for lines with Krajíček's `CC` and `MCC_U` at most `t`; the monotone form assumes the models of `𝒜` are upward closed. This sharpens the bounds of Theorem 5.1, `(k + 2 n) · 2 ^ O(t)` and, in the monotone case, `(k + n) · 2 ^ O(t)`: the `2 n` answer nodes of the source's protocol are leaves here and cost nothing. `lt_of_forall_lt_size` is the transfer to line lower bounds. Only the monotone case for the `𝒜` side is stated. Cutting planes is the first proof-system client (see below); resolution refutations are not yet translated into semantic refutations. The [checked examples](../../ComplexityTests/ProofComplexity/SemanticDerivation.lean) apply every form to a three-line refutation of `x₀ = 1` against `x₀ = 0`; check them with `scripts/build.sh ComplexityTests.ProofComplexity.SemanticDerivation`.

## Clause space

Import `Complexity.Logics.Propositional.Resolution.SpaceWidth` for the definitions and the inequality, or `Complexity.Logics.Propositional.Resolution.TseitinSpace` for the Tseitin corollaries.

[Configuration-style resolution](../../Complexity/Logics/Propositional/Resolution/Space.lean) follows Esteban and Torán. It keeps a `Finset` of clauses in memory, and each move (`ConfigMove`) changes it by one of three rules (`CNF.ConfigStep`): download a clause of the formula, add the resolvent of two clauses in memory, or erase a clause. The resolution rule is that of `CNF.IsProof`, with no weakening. `CNF.configLTS φ s` is the cslib `LTS` of these moves, restricted to configurations of at most `s` clauses. It follows the same pattern as the pebbling library's `Cslib.Pebbling.blackPebbleGame`.

`CNF.RefutableInSpace φ s` holds when some `MTr` run from `∅` reaches a configuration containing `[]`. Space counts distinct clauses, and time (the number of moves) is not bounded. The module proves the basic properties:

- soundness: `RefutableInSpace.not_satisfiable`;
- space is at most size: `RefutableInSize.refutableInSpace`;
- completeness: `exists_refutableInSpace_iff_not_satisfiable`;
- `RefutableInSpace.three_le`: space is at least `3` unless `[] ∈ φ`.

[The space–width module](../../Complexity/Logics/Propositional/Resolution/SpaceWidth.lean) proves the Atserias–Dalmau inequality in the form of Theorem 1 of Filmus, Lauria, Mikša, Nordström and Vinyals (STACS 2014). `RefutableInSpace.refutableInWidth` says that if every clause has width at most `k`, clause space `s` gives a refutation of width `s + k - 3`, with truncated subtraction. Unlike that paper, the theorem does not assume `[] ∉ φ`. The contrapositive `RefutableInSpace.add_four_le` turns a width lower bound `¬ RefutableInWidth w` into the space bound `w + 4 ≤ s + k`.

The proof keeps Atserias and Dalmau's Duplicator strategy, the partial assignments that falsify no clause derivable within width `w`, as private definitions. The game itself is not exported, and neither is the converse characterization of width.

[The Tseitin module](../../Complexity/Logics/Propositional/Resolution/TseitinSpace.lean) combines this with the width bound of Ben-Sasson and Wigderson:

- `Tseitin.minBalancedCut_le_of_refutableInSpace` gives `e(G) ≤ s + k - 3` on a connected multigraph whose vertices have at most `k` non-loop edges;
- `Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace` gives `h(G) |V| / 3 + 3 ≤ s + |D|` on a rotation map with `h(G) > 0`;
- `CNF.exists_forall_refutableInSpace_le` is a family with explicit constants. For `n ≥ 4392000` it has at most `120 n` variables, `2 ^ 120 · n` clauses of width at most `120`, and every refutation in clause space `s` has `n ≤ 36000 s`.

As with the size bound, the expanders come from a counting argument.

The [checked examples](../../ComplexityTests/ProofComplexity/Space.lean) refute `x ∧ ¬x` in space `3` and show that space `2` is impossible. They also give a five-line refutation that erasure keeps in space `3`, and a formula with a width-`3` clause on which the inequality is attained: `k = s = 3`, width `3` and not `2`. Check them with `scripts/build.sh ComplexityTests.ProofComplexity.Space`.

Not yet formalized:

- the Esteban–Torán bound of clause space by the logarithm of tree-like size;
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

## Foundations for algebraic degree lower bounds

Two Boolean-analysis lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../Complexity/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `n!` is nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../Complexity/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, #U` are nonzero. The tests ([inclusion matrices](../../ComplexityTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../ComplexityTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped.

## Known Limitations

This section inventories resolution, including clause space, cutting planes, semantic derivations and their syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[complexitylib]: ../sources.md#complexitylib
