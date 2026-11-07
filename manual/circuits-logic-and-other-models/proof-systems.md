# Propositional models and proof complexity

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

## Algebraic proof systems

Nullstellensatz (NS) certificates and Polynomial Calculus (PC) proofs use coefficients in a
commutative semiring `R`, in the namespaces `Cslib.Logic.PL.NS` and `Cslib.Logic.PL.PC`.
The caller supplies all input axioms for the chosen encoding and basis. Standard Boolean and
complementary axioms such as `x² - x` and `x + x̄ - 1` require a ring. In the two proof modules,
`NS.IsProof.eval_eq_zero` and `PC.IsProof.eval_eq_zero` show that every proved polynomial vanishes
at any common zero of the inputs. Their `exists_eval_ne_zero` lemmas
require `Nontrivial R` and show that a refutable system has no common zero.
[NS proof module](../../Complexity/Logics/Propositional/Algebraic/Nullstellensatz/Proof.lean),
[PC proof module](../../Complexity/Logics/Propositional/Algebraic/PolynomialCalculus/Proof.lean).

The computable `NS.size` is the sum of products of input and multiplier support sizes, exactly
the standard NS size `∑ᵢ ‖pᵢ‖ ‖fᵢ‖` in de Rezende et al., §8.1 (STOC 2021, p. 217), where
`‖p‖` counts nonzero monomials. `PC.size` sums support sizes across all proof lines, counting
repeated lines separately. `NS.degree` bounds sums of input and multiplier total degrees for
nonzero multipliers. A nonzero multiplier of a zero input still contributes its degree.
`PC.degree` is the maximum total degree of a proof line. Both degrees return `0` on empty data.
The lemmas `NS.degree_le_iff` and `PC.degree_le_iff` recover the term and line bounds. These
measures concern formal polynomials, so a Boolean or other basis change needs its own resource
comparison. [de Rezende et al.](https://www.ias.edu/sites/default/files/deRezendeGoNoPiRoSo_Automating.pdf)

Under `Nontrivial R`, `PC.exists_isProof_of_ns` translates an NS refutation of size at most `s`
and total degree at most `d` into one PC refutation of size at most `s² + (d + 1)s` and total
degree at most `d`. Fact 8.1 (p. 218) addresses arbitrary target polynomials and block degree
over fields.
[NS-to-PC simulation](../../Complexity/Logics/Propositional/Algebraic/PolynomialCalculus/Nullstellensatz.lean).

For input total degrees at most `d₀`, `PC.RefutableInSize.of_ns` gives PC size at most
`(d₀ + 1)s² + s` from NS size at most `s`, under the same nontriviality assumption. Its auxiliary
gap-truncation bound `NS.IsProof.exists_degree_le_mul_size`, proved here, first supplies a
replacement NS certificate of no larger size and degree at most `d₀` times the original size.
The replacement discards high-degree cancellation and multipliers of zero inputs.

Over every commutative semiring, `NS.exists_isProof_of_pc` gives a certificate for every PC
proof line, without a size or degree bound.
[PC-to-NS conversion](../../Complexity/Logics/Propositional/Algebraic/Nullstellensatz/PolynomialCalculus.lean).

The clause-only CNF arithmetization uses `Literal.toPolyAssignment` to assign each literal its
Boolean truth value in the coefficient semiring. Over a ring, positive and negative coordinates
are `a` and `1 - a`. A clause polynomial multiplies the coordinates of complementary literals,
so `x ∨ ¬y` becomes `x̄ · y`. The identity `Clause.eval_toPoly` gives value `0` for a satisfied
clause and `1` for a falsified clause. With `Nontrivial R`,
`CNF.eval_eq_true_iff_forall_eval_toPoly_eq_zero` characterizes satisfaction by the vanishing of
every clause polynomial at that same Boolean assignment. Arbitrary literal coordinates can give
a spurious solution to contradictory unit clauses.
[Pointwise CNF encoding](../../Complexity/Logics/Propositional/Algebraic/CNF.lean).

### Refutations over the Boolean cube

[The Boolean-cube layer](../../Complexity/Logics/Propositional/Algebraic/Boolean.lean) reuses
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
[`NS.exists_isProof_of_sum`](../../Complexity/Logics/Propositional/Algebraic/Nullstellensatz/Combination.lean)
turns a finite combination of inputs into a certificate with the same degree bound, and
[`PC.IsProof.mono`](../../Complexity/Logics/Propositional/Algebraic/PolynomialCalculus/Invariant.lean)
enlarges the input list.

[The Boolean CNF encoding](../../Complexity/Logics/Propositional/Algebraic/CNF/Boolean.lean)
substitutes `X v` for the positive literal coordinate and `1 - X v` for the negative one in
`Clause.toPoly`. So `Clause.toBoolPoly` is the standard product encoding in the original
variables: `x ∨ ¬y` becomes `(1 - x) · y`. With `1` read as true, the clause polynomial is `0`
at a satisfying point and `1` at a falsifying point (`Clause.eval_toBoolPoly`), and
`CNF.isBoolSolution_toBoolPolys_iff` identifies Boolean solutions with satisfying assignments.
Because the Boolean axioms are inputs, contradictory unit clauses have no spurious solution.
`CNF.not_satisfiable_of_ns` and `CNF.not_satisfiable_of_pc` give soundness. Over a field,
`CNF.ns_refutableInDegree_iff` and `CNF.pc_refutableInDegree_iff` give refutability in degree
`card V + w`, for clauses of at most `w` literals, exactly when the formula is unsatisfiable.

[The subset-sum lower bound](../../Complexity/Logics/Propositional/Algebraic/SubsetSum.lean) is
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
[tests](../../ComplexityTests/ProofComplexity/Algebraic.lean) check the following instances:

- An explicit degree-2 Nullstellensatz refutation of `1/2 - x`, which has no degree-1
  polynomial calculus refutation.
- `x₁ + x₂ + x₃ + x₄ = 5` over `ℚ` and over `ZMod 7`, refutable in degree 5 but not in degree 2.
- `x₁ + x₂ + x₃ = m` over the field with nine elements, for `m` outside `0, 1, 2, 3`, refutable
  in degree 4 but not in degree 2, although `3!` vanishes there.
- The instance with no variables, refutable in degree 0, which shows that `n ≥ 1` is needed.
- `v ∧ ¬v`, refuted in degree 1, and the satisfiable formula `v`, which has no refutation.

Run `scripts/build.sh ComplexityTests.ProofComplexity.Algebraic` from the repository root to
check them. Not yet formalized: the matching upper bound of Theorem 4.2, the size lower bounds of
the same paper, pigeonhole degree lower bounds, the simulation of bounded-width resolution by
polynomial calculus, and sum-of-squares.

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

## Foundations for algebraic degree lower bounds

Two Boolean-analysis lemmas from the subset-sum degree lower bound of Impagliazzo, Pudlák and Sgall (Theorem 5.1) are available before the algebraic proof systems themselves. Lemma 5.2 of that paper is [`BitString.totalDegree_affine_mul`](../../Complexity/Foundations/BooleanAnalysis/AffineDegree.lean). It concerns `L = m - ∑ c i * x i` with every `c i` nonzero and a nonzero function `r` on the cube with `2 * deg r < n`: the product `L * r` has multilinear degree exactly `deg r + 1`. The source proves it over `ℝ`; the formal statement needs only a field in which `1, …, deg r + 1` are nonzero. Its proof compares subset Möbius coefficients (`BitString.subsetMobius_bitVal_mul`) and applies Gottlieb's full-rank theorem for inclusion matrices ([`Finset.eq_zero_of_sum_powersetCard_eq_zero`](../../Complexity/Foundations/Combinatorics/InclusionMatrix.lean)), proved over any field in which `1, …, s` are nonzero. The tests ([inclusion matrices](../../ComplexityTests/Foundations/Combinatorics/InclusionMatrix.lean), [affine degree](../../ComplexityTests/Foundations/BooleanAnalysis/AffineDegree.lean)) show that the field hypothesis, `t + s ≤ #U` and `2 * deg r < n` cannot be dropped.

## Known Limitations

This chapter covers propositional syntax, resolution, algebraic proof predicates over the Boolean cube and one algebraic degree lower bound. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[complexitylib]: ../sources.md#complexitylib
