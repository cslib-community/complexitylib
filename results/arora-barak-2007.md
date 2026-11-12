# Arora–Barak draft coverage audit

Audit and checked client: Christian Reitwiessner, with Codex assistance.

This is a growing statement-level audit under [#4711](https://github.com/cslib-community/cslib-frontier/issues/4711),
not a completeness claim for the book or library. Its source is the
[public web draft dated 2007-01-08](https://theory.cs.princeton.edu/complexity/book.pdf)
(489 PDF pages; SHA-256 `da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2`).
Numbers and printed pages below belong to that draft, not the published edition.
The initial automatic extraction found 245 distinct numbered result headings across chapters
1–22; only the chapter-specific records below have been checked to the stated extent.

The results registry remains [Entries.lean](../CslibFrontierResults/Entries.lean). This audit
records absent endpoints, model differences and source problems that a positive-result registry
cannot express by pointing at a theorem. A nearby theorem is not counted as full coverage.

## Chapter 14: algebraic computation models

Snapshot: `b33272859bedf13f13abe0a6e841a56b41807d5f` on 2026-11-12, with CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All eight numbered result headings in the chapter
were checked against the extracted draft text, including the two claims under 14.7.
Library inspection covers the arithmetic circuit modules linked below and neighboring model
modules; searches also checked pinned CSLib and Mathlib for the named algebraic models and
results. Negative search results are qualified: they are not proofs of semantic absence from
every possible general theorem. No whole-library semantic or axiom-dependency audit is claimed.
Here $\kappa(S)$ denotes the draft's component count, not the number of points in $S$.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 14.7, determinant part | 258 / 274 | **Source issue; nearby infrastructure.** The literal arbitrary-circuit claim fails the degree check below. Determinant membership in VP and a permanent-to-determinant construction do not establish a corrected formula-universality theorem. |
| 14.7, permanent part | 258 / 274 | **Partial; source conventions need correction.** Permanent membership, formula simulation and a single-entry selector gadget are present. Full completeness remains [#321](https://github.com/cslib-community/cslib-frontier/issues/321). |
| 14.11 | 259 / 275 | **Endpoint not located.** Depth $O(n^5)$ algebraic computation trees for real subset sum; ordinary binary subset-sum reductions are a different model. |
| 14.14 | 260 / 276 | **Endpoint not located.** At least $n!$ components of the real element-distinctness region. This is a topology result, independent of building a machine model. |
| 14.15 (Ben-Or) | 260 / 276 | **Endpoint not located; model convention needed.** The draft bound is $C(W)=\Omega(\log\max\{\kappa(W),\kappa(\mathbb R^n\setminus W)\}-n)$. Tree operations, branch costs and the component-count convention must be fixed first. |
| 14.16 | 261 / 277 | **Endpoint not located; depends on the tree model.** At depth $d$, at most $2^d$ projected pieces given by at most $d$ degree-two constraints with $d$ auxiliary variables, before the stated disequality-elimination step. Existing polynomial syntax alone does not supply this path translation. |
| 14.18 (Milnor–Thom consequence) | 261 / 277 | **Endpoint not located.** The displayed bound is $\kappa(S)\le D(2D-1)^{n+h-1}$ for degree-$D$ constraints in $n$ variables, with $m$ equalities and $h$ inequalities, independent of $m$. Exact constraint/degree hypotheses need a precise source formulation; this is a general mathematics prerequisite for 14.15. |
| 14.23 (BSS) | 264 / 280 | **Endpoint not located; model convention needed.** Completeness of the specified binary-coefficient common-root problem for the binary-input part of nondeterministic complex computation. Polynomial-calculus/Nullstellensatz proof systems do not prove this computational claim. |
| 14.25 | 265 / 281 | **Endpoint not located; source proof needs repair.** Mandelbrot undecidability for the chapter's complex-machine model. The draft's dimension argument cannot be accepted as a general claim about countable unions of semialgebraic sets. |

### What the existing algebraic API establishes

All names in this paragraph are in `Cslib.Circuits.Arithmetic`, except the two explicitly
qualified `Cslib.Circuits.Formula` results.

- [Determinant.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant.lean):
  `exists_circuit_det` bounds the gate count by $3n^4+4$ over a commutative ring;
  `detFamily_mem_VP` supplies membership in circuit-based VP. These are algorithms for the
  determinant, not simulations of every small circuit by a small determinant.
- [DeterminantalComplexity.lean](../CslibFrontier/Computability/Circuit/Arithmetic/DeterminantalComplexity.lean):
  `isProjection_permanent_det_two_pow_sub_one` represents the size-$n$ permanent by a determinant
  of dimension $2^n-1$ over every commutative ring. Its module documentation explicitly leaves
  general determinantal universality unformalized.
- [Permanent.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Permanent.lean):
  `permFamily_mem_VNP` proves membership over every commutative ring, not hardness.
- [Permanent/Formula.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Permanent/Formula.lean):
  `Cslib.Circuits.Formula.isProjection_permanent` and `isProjection_permanent_toCircuit` simulate
  a formula by dimension `F.size + 1`, over every commutative semiring. Here `size` counts
  operation nodes, including constants; sharing a subexpression in a circuit is different.
- [Permanent/BooleanSum.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Permanent/BooleanSum.lean):
  `isProjection_booleanSum_entry_permanent` eliminates a selector occurring in exactly one
  entry, using an explicit scalar `half` with `2 * half = 1` and one extra matrix dimension.
  Repeated-selector elimination and full VNP-hardness are explicitly outstanding.

The draft's Definition 14.4 uses formula witnesses for `AlgP`; the library's
[VP](../CslibFrontier/Computability/Circuit/Arithmetic/VP.lean) and
[VNP](../CslibFrontier/Computability/Circuit/Arithmetic/VNP.lean) use circuits. No equivalence
bridge was identified in this audit. The draft's Definition 14.6 also allows only substitutions
from $0,1,x_i$, whereas library `IsProjection` permits arbitrary scalar constants. This matters:
a permanent with only $0,1,x_i$ substituted has nonnegative real coefficients and cannot yield
the constant $-1$, although the preceding draft arithmetic model permits $-1$ as a constant.
The field convention also needs correction: the standard permanent-completeness target in
[#321](https://github.com/cslib-community/cslib-frontier/issues/321) excludes characteristic two;
the draft's bundled statement does not say so. These differences prevent declaring 14.7 covered
merely by finding a similarly named theorem.

### Checked degree obstruction to literal 14.7

The draft says that an arbitrary circuit of size $u$ projects to a determinant “on $u+2$
variables.” Even interpreting $u+2$ generously as matrix dimension fails for unrestricted
circuits: four squarings compute $X^{16}$, but a determinant of dimension at most six has degree
at most six, and variable/scalar projection cannot raise degree.

[AroraBarakAlgebraic.lean](../CslibFrontierTests/AroraBarakAlgebraic.lean) checks this over every
nontrivial commutative ring, using `exists_circuit_pow_two_pow`, `totalDegree_projection_le`
and `totalDegree_det_genericMatrix_le`. The witness has size at most four and is not a
projection of a determinant of dimension **its actual size plus two**. Inputs are free;
these are formal polynomials, not polynomial functions identified by evaluation on a finite
field. Run from the repository root:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.AroraBarakAlgebraic
```

A formula/circuit typo is plausible in context, but this audit does not silently replace the
source claim or assert a corrected universality theorem. The draft's lack of a degree bound
makes the unrestricted statement unsuitable as a formalization target.

### Other source and model boundaries

The chapter describes addition/subtraction as free in its computation-tree model but later
uses depth to count leaves and constraints. A formal model must state which branch and
arithmetic operations contribute to depth and why those counting bounds hold. The draft's
Definition 14.13 describes path connectivity; a port using Mathlib's connected components must
supply the relevant equivalence, rather than conflate the notions by definition.

For 14.23, specify input polynomial encodings, allowed field constants, witnesses and the
reduction before claiming BSS completeness. The existing Boolean-root Nullstellensatz
[proof-system results](../CslibFrontier/Logics/Propositional/Algebraic/Boolean.lean) concern
refutations with Boolean axioms, not this common-complex-root decision problem.

For 14.25, the sketch's asserted dimension consequence is invalid for semialgebraic sets in
general: the complex plane, viewed as the real plane, is already semialgebraic of dimension
two. A correct argument needs the precise equality-test/algebraic-machine restrictions and a
suitable topological obstruction. This observation does not refute the intended undecidability
result; it prevents using the draft sketch as a complete proof.

## Chapter 18: PCP and hardness of approximation

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12, CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All 24 numbered result headings were
checked against PDF pp. 367–400, including the technical notes after the exercises.
Searches inspected `Computability/PCP`, `Classes/PCP`, Boolean analysis, constraint graphs
and the approximation modules on that snapshot. “Endpoint not located” means not located in
those sources or by repository-wide searches for the named constructions, not semantic absence
from all possible general lemmas. This is source inspection, without new Lean elaboration or
an axiom audit. The library's polynomial-time certificates use native multitape TMs and explicit
embeddings into `List Bool`; their validity does not depend on identifying an uncosted finite
construction with a polynomial-time reduction. In the table, library `unsatVal` is $1-\mathrm{val}$.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 18.2 (PCP theorem) | 353 / 369 | **Covered.** `Cslib.Complexity.NP_eq_PCP_log` in [Completeness.lean](../CslibFrontier/Computability/PCP/Completeness.lean) gives equality for every input encoding, with randomness bounded by a constant times `Nat.log 2 n + 1`, constantly many nonadaptive Boolean queries, perfect completeness and soundness $1/2$. The additive one handles short inputs. NP is the deterministic-verifier class; efficiency is certified in the native TM model. |
| 18.4 (scaled-up PCP) | 354 / 370 | **Endpoint not located.** No equality of polynomial-randomness constant-query PCP with NEXP was found in the PCP classes or completeness modules. [#892](https://github.com/cslib-community/cslib-frontier/issues/892) owns the related BFL/MIP = NEXP objective, not an already proved PCP bridge. The scaled PCP characterization needs its own explicit transfer. Open [#3609](https://github.com/cslib-community/cslib-frontier/pull/3609) supplies an oracularization direction in a proposed `PCPPoly` model, not this equality; its description explicitly leaves NEXP inclusion open. |
| 18.7 (MAX-3SAT approximation consequence) | 355 / 371 | **Partial.** `Cslib.Complexity.GapThreeSAT_notMem_PromiseP` in [MaxThreeSAT.lean](../CslibFrontier/Computability/PCP/Approximation/MaxThreeSAT.lean) excludes a polynomial-time separator at $s=1-1/(3\cdot2^{77})$ assuming $P\ne NP$. No general optimization-algorithm interface and extraction of that separator from an assignment-producing $\rho$-approximation is supplied there. Use a slightly larger $\rho<1$ to separate the non-strict no-instance threshold. |
| 18.8 (gap-producing 3SAT reduction) | 356 / 372 | **Covered.** `Cslib.Complexity.GapThreeSAT_npHard`, using `polyTimeReducible_GapTwoCSP_GapThreeSAT` in [MaxThreeSAT.lean](../CslibFrontier/Computability/PCP/Approximation/MaxThreeSAT.lean), provides an encoded polynomial-time gap reduction with perfect completeness. The formal no-bound is $\mathrm{val}\le s$; choosing $s<\rho<1$ gives the draft's strict $<\rho$ convention. |
| 18.13 (gap-CSP formulation) | 358 / 374 | **Partial.** `Cslib.Complexity.GapTwoCSP_npHard` in [MaxCSP.lean](../CslibFrontier/Computability/PCP/Approximation/MaxCSP.lean) proves a constant gap over a 128-symbol alphabet, with full binary constraint tables and explicit encodings. This is not literally the draft's binary-alphabet bounded-arity CSP. [Completeness.lean](../CslibFrontier/Computability/PCP/Completeness.lean) and [Encoded/Verifier/Reduction.lean](../CslibFrontier/Computability/PCP/Encoded/Verifier/Reduction.lean) implement the reduction-to-verifier direction; no packaged equivalence for arbitrary draft-style binary qCSP instances was identified. |
| 18.15 (18.8 restated) | 359 / 375 | **Covered.** `Cslib.Complexity.GapThreeSAT_npHard` in [MaxThreeSAT.lean](../CslibFrontier/Computability/PCP/Approximation/MaxThreeSAT.lean), with clauses of at most three literals and the explicit constant above. This counts the source's separately numbered restatement once. |
| 18.16 (3CNF to independent-set value) | 359 / 375 | **Partial.** `Cslib.Complexity.SAT.indepNum_toIndependentSet_le` and `card_toFinset_vertices_toIndependentSet` in [IndependentSet.lean](../CslibFrontier/Computability/PCP/Approximation/IndependentSet.lean) support a polynomial-time Karp literal-occurrence graph, with $3m$ vertices for exactly-three-literal clauses. The draft instead uses seven satisfying local assignments per clause and claims $\alpha(G)=\mathrm{val}(\varphi)n/7$; that exact construction/cardinality is not supplied. Seven assignments presupposes three distinct variables. |
| 18.19 (walk stays in a set) | 361 / 377 | **Source issue.** The displayed bounds have exponent $k$ although the walk is parameterized by $\ell$, and $k$ is unbound. Moreover $(\beta-2\lambda)^k$ is not a valid universal lower bound for negative base and even exponent without further restrictions. A corrected exponent and lower-bound range must be fixed before comparing to expander-walk APIs. |
| 18.20 (independent-set amplification) | 362 / 378 | **Endpoint not located.** The graph transformation with fractional independence number between $(\widetilde\alpha(G)\pm2\lambda)^{\log n}$ and polynomial output size was not found. [IndependentSet.lean](../CslibFrontier/Computability/PCP/Approximation/IndependentSet.lean) explicitly stops at one fixed constant gap. The ROADMAP's FGLSS direction records the broader goal; no dedicated owning issue was located. |
| 18.21 (Walsh–Hadamard PCP) | 363 / 379 | **Covered.** Endpoint, different proof route: `Cslib.Complexity.NP_subset_PCP_log` in [Completeness.lean](../CslibFrontier/Computability/PCP/Completeness.lean) gives the stronger logarithmic-randomness result, hence a polynomial randomness allowance. The proof uses encoded Dinur amplification and a Hadamard assignment tester, rather than a separately packaged exponential Walsh–Hadamard verifier for QUADEQ. |
| 18.23 (linearity testing) | 364 / 380 | **Covered.** `Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance` in [Linearity.lean](../CslibFrontier/Foundations/BooleanAnalysis/Linearity.lean), with $\epsilon=1-\rho$, gives agreement at least $\rho$ with a parity. Uniform finite cube `ι → Bool`, coordinatewise XOR addition and normalized Hamming distance match the draft's GF(2) model; there is no machine-time claim. |
| 18.25 (exponential PCP of proximity) | 368 / 384 | **Partial.** [AssignmentTester.lean](../CslibFrontier/Computability/PCP/AssignmentTester.lean), notably `Cslib.PCP.HadamardTester.exists_inputDist_le_of_le_acceptProb`, tests long-code encodings of two labels against a binary constraint. It does not state the draft's arbitrary-circuit, Walsh–Hadamard-input proximity theorem with $0.99$ agreement and polynomial randomness. The related PCPP objective is already listed under [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131). |
| 18.26 (two-piece PCP of proximity) | 368–369 / 384–385 | **Partial.** The same [Hadamard assignment tester](../CslibFrontier/Computability/PCP/AssignmentTester.lean) supplies two-endpoint proximity machinery, but not the arbitrary split $n_1+n_2=n$, circuit input and quantitative guarantees of this corollary. This number is a proximity result, not an independent-set hardness theorem. |
| 18.28 (PCP main lemma) | 369 / 385 | **Partial.** `Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplify` in [Encoded/Amplification.lean](../CslibFrontier/Computability/PCP/Encoded/Amplification.lean) doubles the gap up to a threshold; its executable iteration and final native polynomial-time certificate are in [Encoded/Amplification/Iteration.lean](../CslibFrontier/Computability/PCP/Encoded/Amplification/Iteration.lean). The formal round uses fixed 128-symbol binary constraints, not binary-alphabet qCSP; the exact source constant-linear size contract is not the stated native runtime contract. The PCP endpoint itself is covered by 18.2. |
| 18.29 (gap amplification) | 370 / 386 | **Partial.** `Cslib.PCP.ConstraintGraph.min_le_div_unsatVal_power_preprocessWith` in [Amplification/Family.lean](../CslibFrontier/Computability/PCP/Amplification/Family.lean), with the fixed parameters in [Amplification/Arithmetic.lean](../CslibFrontier/Computability/PCP/Amplification/Arithmetic.lean), implements amplification via preprocessing and killed walks. It is not the exact all-$\ell$ binary-qCSP CL-reduction statement. |
| 18.30 (alphabet reduction) | 370 / 386 | **Partial.** `Cslib.PCP.ConstraintGraph.le_unsatVal_composeSelected` and `satisfiable_composeSelected_iff` in [SelectedComposition.lean](../CslibFrontier/Computability/PCP/SelectedComposition.lean) reduce to 128 symbols, with loss 840. The draft reduces to a binary alphabet, constant arity, with loss three. Its exact quantitative statement is not established by this different composition. |
| 18.31 (powering) | 371 / 387 | **Partial.** `Cslib.PCP.RegularConstraintGraph.power`, `card_alphabet_power`, `satisfiable_power` in [Power.lean](../CslibFrontier/Computability/PCP/Power.lean) and `le_unsatVal_power` in [PoweringBound.lean](../CslibFrontier/Computability/PCP/PoweringBound.lean) prove killed-walk powering. The draft uses fixed-length lazy walks, a $\sqrt t$ gain, and different alphabet/constraint counts; those precise bounds are not the formal statement. |
| 18.32 (plurality event lower bound) | 374 / 390 | **Partial; not separately formalized in this model.** `Cslib.PCP.RegularConstraintGraph.le_expect_numHits` in [PoweringBound.lean](../CslibFrontier/Computability/PCP/PoweringBound.lean) serves the corresponding first-moment role for killed walks. It does not prove the draft's per-edge/per-position $B_{j,f}$ bound for fixed-length lazy walks. |
| 18.33 (intersection bound) | 375 / 391 | **Partial; not separately formalized in this model.** `Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le` in [PoweringBound.lean](../CslibFrontier/Computability/PCP/PoweringBound.lean) provides the second-moment estimate used by the formal proof. The draft's event indexing and $30kd\epsilon$ constant are not its statement; the displayed source intersection also repeats $j$ where the subsequent argument uses $j'$. |
| 18.34 (union from pairwise intersections) | 376 / 392 | **Partial.** Boundary convention: the denominator $4C$ requires $C>0$, the statement says only $C\in\mathbb N$ and its proof makes $2C$ copies, so fix the positive-natural convention explicitly. For positive $C$ this is a useful finite-set second-moment consequence. No separately named exact finite-set statement was located; [PoweringBound.lean](../CslibFrontier/Computability/PCP/PoweringBound.lean) instead proves the probability bound needed by its own proof. |
| 18.35 (CSP view of proximity) | 377–378 / 393–394 | **Partial.** [AssignmentTester.lean](../CslibFrontier/Computability/PCP/AssignmentTester.lean) constructs local constraint tests and proves `satisfies_toConstraintGraph_honestProof` and `exists_inputDist_div_le_unsatFrac`. These are not the source's arbitrary-circuit exponential transformation with two separately Walsh–Hadamard-encoded input blocks. |
| 18.36 (arity reduction) | 383 / 399 | **Partial.** [ThreeSAT.lean](../CslibFrontier/Computability/PCP/ThreeSAT.lean) and [Encoded/ThreeSAT.lean](../CslibFrontier/Computability/PCP/Encoded/ThreeSAT.lean) implement the clause/assignment consistency construction for 3SAT used by completeness. The generic all-qCSP transformation to alphabet $2^q$ with loss $q$ and the source's CL size bound was not located as a public endpoint. |
| 18.37 (degree reduction) | 383–384 / 399–400 | **Partial.** `Cslib.PCP.ConstraintGraph.degreeReduce`, `le_unsatVal_degreeReduce` and `satisfiable_degreeReduce_iff` in [DegreeReduction.lean](../CslibFrontier/Computability/PCP/DegreeReduction.lean) provide the cloud construction and gap preservation given expander clouds. This is parameterized by the cloud degree/spectral bound, not the draft's precise $100Wd$ loss. Executable preprocessing is separately certified. |
| 18.38 (expanderization and loops) | 384 / 400 | **Partial.** `Cslib.PCP.ConstraintGraph.preprocess`, `spectralExpansion_preprocess_le`, `le_unsatVal_preprocess` in [Preprocess.lean](../CslibFrontier/Computability/PCP/Preprocess.lean) give regular expansion and satisfiability preservation. The added loop degree is not one half of the final degree; killed-walk powering does not need that draft convention. No exact $4d$-regular, half-loop, $10d$-loss endpoint is claimed. |

### What the existing PCP API establishes

- The class-level PCP theorem and native polynomial-time gap reductions are implemented, not
  merely postulated finite constructions. The gap-CSP alphabet and encodings remain visible.
- [IndependentSet.lean](../CslibFrontier/Computability/PCP/Approximation/IndependentSet.lean)
  proves `Cslib.Complexity.GapIndependentSet_npHard` at one fixed constant and
  `GapIndependentSet_notMem_PromiseP` under $P\ne NP$. Neither supplies the $n^{-\delta}$
  hardness claimed in the unnumbered §18.3 conclusion, or amplification to every constant.
- The many partial Dinur rows reflect a different, successful proof of 18.2, not a missing PCP
  theorem. Reimplementing every fixed-walk auxiliary lemma is not necessary to use that endpoint.

## Chapter 19: more PCP theorems and the Fourier transform technique

Snapshot and pin are as in Chapter 18. All 12 numbered results were checked against PDF
pp. 401–416. Inspection covers parallel repetition, Label Cover, the Håstad test, Fourier/noise
analysis, bucket weights and Kushilevitz–Mansour learning. The conversion between signs and bits
is $(-1)^b$ (`Cslib.BitString.signVal`); set frequencies correspond to parity characters.
Finite probability identities do not by themselves certify a randomized oracle machine's runtime.
Existing issue/PR searches included open and closed Håstad, Label Cover, repetition and Fourier
learning work. [#886](https://github.com/cslib-community/cslib-frontier/issues/886) is still open,
but its original missing-repetition description is older than the merged results below.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 19.3 (parallel repetition) | 387 / 403 | **Partial.** Strong finite-game theorem present: `Cslib.PCP.TwoProverGame.value_pow_le_of_value_le` in [ParallelRepetition.lean](../CslibFrontier/Computability/PCP/ParallelRepetition.lean) proves Holenstein's bound $(1-\epsilon^3/6000)^{k/\log_2(|A||B|)}$ over arbitrary tuple strategies, not just product strategies. This gives exponential decay in the finite two-prover model. It is not a theorem stated for every PCP verifier in the draft's representation. Encoded small-soundness Label Cover is also present in [SmallSoundness.lean](../CslibFrontier/Computability/PCP/Approximation/LabelCover/SmallSoundness.lean), `Cslib.Complexity.exists_GapLabelCover_npHard`; see merged [#2875](https://github.com/cslib-community/cslib-frontier/pull/2875) and [#3225](https://github.com/cslib-community/cslib-frontier/pull/3225). |
| 19.5 (Håstad's three-bit PCP) | 387 / 403 | **Partial.** `Cslib.PCP.Hastad.gapLabelCover_dichotomy_lt_one` in [Hastad.lean](../CslibFrontier/Computability/PCP/Approximation/Hastad.lean) proves completeness $1-\delta$ and soundness $1/2+4\epsilon$ for the analytic three-query test. Small-soundness Label Cover hardness now exists, but the module explicitly does not construct a MAX-E3LIN instance or a uniform PCP verifier. That final encoded reduction remains in the [#886](https://github.com/cslib-community/cslib-frontier/issues/886) roadmap direction; repetition alone does not finish it. |
| 19.6 (MAX-3SAT $7/8+\epsilon$ hardness) | 388 / 404 | **Partial.** `Cslib.Logic.PL.CSP.proportion_countUnsat_toCNFBounded_parity` and `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_parity` in [ThreeXOR.lean](../CslibFrontier/Computability/PCP/Approximation/ThreeXOR.lean) certify the exact four-clause reduction and quarter loss. MAX-E3LIN hardness and composition to this approximation endpoint are still missing. This corollary uses imperfect completeness; it is distinct from the stronger satisfiable-formula hardness target in [#886](https://github.com/cslib-community/cslib-frontier/issues/886). |
| 19.7 (Plancherel and Parseval) | 389 / 405 | **Covered.** `Cslib.BitString.expect_mul_eq_sum_fourierCoeff_mul` in [Fourier.lean](../CslibFrontier/Foundations/BooleanAnalysis/Fourier.lean) is the real-function inner-product identity, specialized to $g=f$ for Parseval. Cube coordinates are bits read as signs and expectations are uniformly normalized, matching the source. |
| 19.9 (large linearity-test coefficient) | 390–391 / 406–407 | **Covered.** Covered by the proof: [Linearity.lean](../CslibFrontier/Foundations/BooleanAnalysis/Linearity.lean), `Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three` and the maximum-coefficient argument inside `exists_hammingDist_parityOn_le_of_le_blrAcceptance`, prove a coefficient at least $2\epsilon$ when acceptance is at least $1/2+\epsilon$. The public conclusion is the equivalent normalized Hamming-distance bound, via `fourierCoeff_signVal`. |
| 19.12 (noisy cubic Fourier identity) | 392 / 408 | **Covered.** By specialization: `Cslib.PCP.Hastad.linearCorr_eq_sum` and `linearProb_eq_add_linearCorr` in [LinearTest.lean](../CslibFrontier/Computability/PCP/Approximation/Hastad/LinearTest.lean), taking the projection to be identity and the two tables equal, give $\sum_S\widehat f(S)^3(1-2\rho)^{|S|}=2\Pr[\mathrm{accept}]-1$. This matches the source test for a noise probability in $[0,1]$; source signs are `signVal` of Boolean tables. |
| 19.13 (low-degree truncation) | 393 / 409 | **Unverified.** The draft states an unweighted signed cubic sum at degrees at most $k=(2\rho)^{-1}\log(1/\epsilon)$. [LinearTest.lean](../CslibFrontier/Computability/PCP/Approximation/Hastad/LinearTest.lean) has a different squared-correlation cutoff bound. A bound on the noisy weighted sum does not immediately imply the displayed signed unweighted truncation: negative coefficients must be handled. No exact endpoint or verified correction was located; rounding $k$ and parameter ranges also need specification. |
| 19.15 (odd Fourier support of folded functions) | 393–394 / 409–410 | **Covered.** `Cslib.BitString.IsOdd.fourierCoeff_of_even` in [LongCode.lean](../CslibFrontier/Foundations/BooleanAnalysis/LongCode.lean) kills all even-cardinality coefficients, including the empty set. Its `IsOdd` is exactly $F(-x)=-F(x)$ after converting bits to signs, the draft's folding condition. |
| 19.16 (projected two-table test identity) | 394 / 410 | **Covered.** `Cslib.PCP.Hastad.linearCorr_eq_sum` and `linearProb_eq_add_linearCorr` in [LinearTest.lean](../CslibFrontier/Computability/PCP/Approximation/Hastad/LinearTest.lean) give the projected Fourier sum and acceptance relation. `Cslib.BitString.projectSet` retains target coordinates with odd preimage multiplicity, the source's $h_2(\alpha)$; [LongCode.lean](../CslibFrontier/Foundations/BooleanAnalysis/LongCode.lean) supplies its character pullback identity. The identity holds without folding; folding removes the empty term. |
| 19.17 (soundness transfer to Håstad verifier) | 395–396 / 411–412 | **Partial.** `Cslib.PCP.Hastad.graphLinearCorr_sq_le` and `gapLabelCover_dichotomy_lt_one` in [Hastad.lean](../CslibFrontier/Computability/PCP/Approximation/Hastad.lean) prove finite Label Cover soundness via spectral decoding. Their cutoff-dependent bound differs from the explicit source condition $\rho\delta^2>\epsilon$; an encoded verifier and that exact quantitative implication are not supplied. |
| 19.18 (finding large Fourier coefficients in polynomial time) | 397–398 / 413–414 | **Partial.** [KushilevitzMansour.lean](../CslibFrontier/MachineLearning/UniformLearning/KushilevitzMansour.lean), in namespace `Cslib.MachineLearning.UniformLearning`, has `inter_mem_bucketSearch`, `mul_card_bucketSearch_le_one`, `uniform_not_accurate_le` and `kmLearner_queriesAtMost`. They supply heavy-frequency retention, $4/\theta^2$ candidate size on accurate samples and a failure/query analysis. The module explicitly certifies only oracle-query cost, not native polynomial runtime or a packaged $0.9$-success frequency-list algorithm for every Boolean function. |
| 19.19 (bucket-weight estimator) | 398 / 414 | **Covered.** `Cslib.BitString.bucketWeight_eq_expect_sample` in [BucketWeight.lean](../CslibFrontier/Foundations/BooleanAnalysis/BucketWeight.lean) is the identity for any coordinate subset $J$. Taking the first $k$ coordinates and $S$ for the prefix frequency gives the source's three-sample expectation. Sampling full cube points leaves unused coordinates, which does not change the uniform expectation. |

### What the existing Fourier and approximation API establishes

- Parallel repetition and small-soundness Label Cover no longer need to be proposed as absent
  prerequisites. The missing endpoint for 19.5/19.6 is the encoded test-to-instance/verifier
  construction and final hardness composition, not another proof of Raz's theorem.
- A certified four-clause compiler does not prove MAX-E3LIN hardness. The constant gap near one
  of Chapter 18 does not prove the optimal $7/8+\epsilon$ threshold.
- Heavy-frequency search has finite mathematical and query guarantees. Its polynomial-time
  machine realization is a separate remaining objective from the learning theorem.

## Chapter 20: quantum computation

Snapshot and pin are as in Chapter 18. All 12 numbered results, including appendix 20.A, were
checked against PDF pp. 417–448. Searches covered quantum foundations/circuits/query algorithms,
BQP/counting/space classes, period finding, and pinned Mathlib's unitary and continued-fraction
areas. Negative results retain the qualified meaning above. The class `Cslib.Complexity.BQP`
uses polynomial-time uniform circuits over Hadamard, NOT, CNOT and Toffoli, with explicit input
encoding and measurement of qubit zero. The draft permits arbitrary described elementary
unitaries; the formal equivalence is still [#3350](https://github.com/cslib-community/cslib-frontier/issues/3350).
Finite unitary or oracle-query semantics do not certify gate synthesis, uniformity or machine time.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 20.2 (classical Bell/CHSH bound) | 404 / 420 | **Covered.** `Cslib.PCP.TwoProverGame.winProb_chsh_le`, `value_chsh` in [CHSH.lean](../CslibFrontier/Computability/PCP/TwoProverGame/CHSH.lean) give the exact $3/4$ value for uniformly random Boolean questions and XOR/AND winning predicate. `winProb_shared_le_value` in [TwoProverGame.lean](../CslibFrontier/Computability/PCP/TwoProverGame.lean) extends the deterministic bound to shared randomness, as in the draft's averaging argument. |
| 20.7 (BPP equals polynomial probabilistic register time) | 407 / 423 | **Endpoint not located.** The BPP verifier definition and uniform Boolean/reversible circuit simulation do not state equivalence with the draft's sequential probabilistic register operations (local functions and fresh random replacement). No explicit simulation of this whole operational model in both directions was located. |
| 20.11 (unitarity characterizations) | 409 / 425 | **Partial.** `Cslib.Quantum.unitaryEquiv` and `unitaryEquiv_apply` in [Basic.lean](../CslibFrontier/Computability/Circuit/Quantum/Basic.lean) turn a unitary matrix into a norm-preserving linear isometry equivalence. Pinned Mathlib has `Matrix.mem_unitaryGroup_iff`, `mem_unitaryGroup_iff'` ([UnitaryGroup.lean](https://github.com/leanprover-community/mathlib4/blob/69552756cd8a2d2d48763cf7279fd814d6a1224d/Mathlib/LinearAlgebra/UnitaryGroup.lean)) and `LinearIsometryEquiv.toMatrix_mem_unitaryGroup` ([PiL2.lean](https://github.com/leanprover-community/mathlib4/blob/69552756cd8a2d2d48763cf7279fd814d6a1224d/Mathlib/Analysis/InnerProductSpace/PiL2.lean)). A single theorem packaging all four arbitrary-matrix conditions, including the converse from norm preservation, was not identified. |
| 20.16 (the specified entangled strategy wins at least $0.8$) | 414–415 / 430–431 | **Partial.** Stronger existential value, different strategy: `Cslib.PCP.TwoProverGame.quantumWinProb_chsh_chshEPR` and `quantumValue_chsh` in [Tsirelson.lean](../CslibFrontier/Computability/PCP/TwoProverGame/Tsirelson.lean) give $\cos^2(\pi/8)$ for an explicit optimal EPR strategy. The draft's strategy uses the same basis on question zero and rotated bases on question one, with average $(1+2\cos^2(\pi/8)+1/2)/4$. The inspected theorem does not identify its measurements with those source measurements. |
| 20.17 ($BPP\subseteq BQP$) | 416 / 432 | **Covered, with gate-model boundary.** `Cslib.Complexity.BPP_subset_BQP` in [QMA/MA.lean](../CslibFrontier/Computability/Complexity/Classes/QMA/MA.lean) proves the inclusion for every input encoding, using uniformly generated reversible classical circuits and Hadamard-prepared random bits. These are allowed elementary operations in the draft. The converse equivalence between the two full BQP definitions is not needed for this simulation and remains #3350. |
| 20.20 (efficient QFT) | 424 / 440 | **Partial.** `Cslib.Quantum.qft`, `qft_apply`, `qft_mulVec` in [Fourier.lean](../CslibFrontier/Foundations/Quantum/Fourier.lean) provide the normalized positive-exponent transform as a unitary on `ZMod N`. The module explicitly does not construct its $O(m^2)$ circuit for $N=2^m$. [#3252](https://github.com/cslib-community/cslib-frontier/issues/3252) and merged [#3267](https://github.com/cslib-community/cslib-frontier/pull/3267) completed only the matrix/exact-period milestone; the ROADMAP retains circuit generation and approximation costs. |
| 20.21 (many good approximate-order samples) | 427 / 443 | **Partial.** `Cslib.Quantum.HasExactPeriod.periodFindingOutcome_recover` and `inv_log_add_one_le_periodFindingOutcome_recover` in [PeriodFinding.lean](../CslibFrontier/Algorithms/Quantum/PeriodFinding.lean) give exact recovery probability $\varphi(r)/r\ge1/(\lfloor\log_2r\rfloor+1)$ when $r\mid N$. They do not prove this count of approximate good samples when the Fourier modulus is not divisible by $r$, nor the continued-fraction recovery theorem. Remaining Shor scope is recorded under [#3252](https://github.com/cslib-community/cslib-frontier/issues/3252), not #896. |
| 20.22 (amplitude near a Fourier peak) | 427 / 443 | **Source issue.** Literal statement; partial nearby result: “The coefficient” is complex, so “at least $\Omega(1/\sqrt r)$” must refer to its modulus or a specified phase convention. [PeriodFinding.lean](../CslibFrontier/Algorithms/Quantum/PeriodFinding.lean), `Cslib.Quantum.HasExactPeriod.norm_periodState_apply_sq`, gives exact squared moduli for $r\mid N$, not the approximate non-dividing case. Specify the postmeasurement coset state and modulus before formalizing this lemma. |
| 20.23 (factoring succeeds with constant probability) | 428–429 / 444–445 | **Source issue.** As printed, the assertion for every nonprime $N$ is false for $N=4$: the unit group is $\{1,3\}$, and its only even-order element is $-1$, which the statement excludes. The factoring algorithm must first handle prime powers/even numbers and use the right condition on $X^{r/2}$, rather than only $X\ne-1$. No corrected native randomized factoring reduction is claimed by the exact-period milestone. |
| 20.24 (nontrivial square root gives a factor) | 428 / 444 | **Endpoint not located.** Interpreting its equations modulo $N$, a nontrivial square root $Y$ of one yields a nontrivial $\gcd(Y-1,N)$. Repository searches of factoring/quantum/number-theory modules did not locate this exact public declaration connected to order finding. Generic gcd and modular arithmetic are prerequisites, not by themselves a certified reduction. The exact integer/modular representatives and positivity hypotheses should be explicit. |
| 20.25 ($BQP\subseteq PSPACE$) | 429–430 / 445–446 | **Partial.** Relative to the draft's gate model; covered for library BQP by composition: `Cslib.Complexity.BQP_subset_PP` in [BQP/Counting.lean](../CslibFrontier/Computability/Complexity/Classes/BQP/Counting.lean), followed by `PP_subset_PSPACE` in [Counting/Space.lean](../CslibFrontier/Computability/Complexity/Classes/Counting/Space.lean), proves the stronger route for the library's uniform finite-gate circuits and native TM space class. Transferring from all draft elementary gates requires the representation/precision equivalence tracked by [#3350](https://github.com/cslib-community/cslib-frontier/issues/3350). |
| 20.26 (continued-fraction best approximation) | 432 / 448 | **Source issue.** The PDF prints $|\alpha-a/b|>|\alpha-c/d|$ for every denominator $d\le b$, the reverse of a best-approximation inequality; it even includes $c/d=a/b$. This cannot be a formalization target verbatim. A corrected appropriate convergent/approximation theorem, with exclusions and strictness fixed, is needed for approximate order finding. |

### What the existing quantum API establishes

- The unnumbered Deutsch–Jozsa discussion has an exact one-query endpoint,
  `Cslib.Quantum.deutschJozsa_regProb_eq_bitVal` and `deutschJozsa_separation` in
  [DeutschJozsa.lean](../CslibFrontier/Computability/QueryComplexity/Quantum/DeutschJozsa.lean).
  These use a phase oracle and the constant/balanced promise, not a native time bound.
- The unnumbered Grover discussion has `Cslib.Quantum.run_grover_of_weight` and
  `grover_success` in [Grover.lean](../CslibFrontier/Computability/QueryComplexity/Quantum/Grover.lean),
  including the single-mark success bound $1-1/N$ with at most $\pi\sqrt N/4$ queries.
  This counts oracle queries; it does not by itself prove the displayed native SAT runtime.
- The unnumbered Simon discussion has decision guarantees `Cslib.Quantum.simonAlg_spec` in
  [Simon.lean](../CslibFrontier/Computability/QueryComplexity/Quantum/Simon.lean), and recovery in
  [SimonSearch.lean](../CslibFrontier/Computability/QueryComplexity/Quantum/SimonSearch.lean).
  They use bit queries to an encoded truth table, rather than one unit-cost whole-value query.
  Native polynomial-time Gaussian-elimination postprocessing remains a separate resource obligation
  in [#2991](https://github.com/cslib-community/cslib-frontier/issues/2991).
- [#896](https://github.com/cslib-community/cslib-frontier/issues/896) is the closed quantum
  foundations/Grover/counting track, not the Shor issue. The open full Shor objective is recorded
  in `ROADMAP.md`, with the closed exact-period milestone [#3252](https://github.com/cslib-community/cslib-frontier/issues/3252).
  Full gate-set universality remains [#3350](https://github.com/cslib-community/cslib-frontier/issues/3350).

## Remaining audit work

Chapters other than 14 and 18–20 have not been catalogued here. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
