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

## Chapter 11: decision trees

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All six numbered results were checked in the PDF text/layout on PDF pp. 227–236. Searches covered decision trees, query measures and their clients, including pinned CSLib `Measures.lean`. These are total finite Boolean functions with unit-cost coordinate queries, not time bounds for Turing machines. Negative searches do not establish semantic absence.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 11.4 (connectivity evasiveness) | 212 / 228 | **Endpoint not located.** The exact graph-connectivity function needs $\binom m2$ edge queries. Searches for connectivity/evasiveness in decision-tree and query modules located general Fourier and symmetric-function criteria, but no connectivity instance. Symmetry under vertex relabelling is not symmetry under all edge-coordinate permutations. |
| 11.11 | 214 / 230 | **Covered.** `Cslib.DecisionTree.complexity_le_certificateComplexity_sq` in [Certificate](../CslibFrontier/Computability/DecisionTree/Certificate.lean) gives $D(f)\le C(f)^2$ for all total Boolean functions. |
| 11.17 (Yao, zero-error expected cost) | 216 / 232 | **Partial.** [Yao](../CslibFrontier/Computability/QueryComplexity/Yao.lean) proves `Cslib.QueryComplexity.randomizedComplexity_eq_iSup_distributionalComplexity` for worst-case depth at bounded error. [ZeroError](../CslibFrontier/Computability/QueryComplexity/Randomized/ZeroError.lean) defines `zeroErrorComplexity` and proves `zeroErrorComplexity_le_complexity`; the equality between worst-input expected zero-error cost and maximum distributional expected deterministic cost was not located. Setting the error to zero in the depth theorem does not supply it. |
| 11.20 | 217 / 233 | **Covered.** `Cslib.QueryComplexity.sensitivity_le_blockSensitivity` and `blockSensitivity_le_certificateComplexity` in pinned [CSLib Measures.lean](https://github.com/leanprover/cslib/blob/ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342/Cslib/Computability/QueryComplexity/Measures.lean), followed by `Cslib.DecisionTree.certificateComplexity_le_complexity` in [Sensitivity](../CslibFrontier/Computability/DecisionTree/Sensitivity.lean), give $s(f)\le bs(f)\le D(f)$. |
| 11.21 (Nisan) | 217 / 233 | **Covered.** `Cslib.QueryComplexity.certificateComplexity_le_sensitivity_mul_blockSensitivity` in [Relations](../CslibFrontier/Computability/QueryComplexity/Relations.lean) gives exactly $C(f)\le s(f)bs(f)$. Its minimal-block argument also avoids the draft sketch’s unjustified assertion about arbitrary sensitive blocks. |
| 11.24 (both parts) | 218 / 234 | **Covered.** `Cslib.DecisionTree.degree_le_complexity` in [Degree](../CslibFrontier/Computability/QueryComplexity/Degree.lean) proves part 1. `Cslib.DecisionTree.complexity_le_degree_mul_blockSensitivity` and `complexity_le_two_mul_degree_pow_three` in [Midrijanis](../CslibFrontier/Computability/QueryComplexity/Midrijanis.lean) strengthen part 2: $D\le\deg(f)bs(f)$ and $D\le2\deg(f)^3$. Degree is exact real multilinear degree; constants have degree and query cost zero, so their case is separate from the positive-degree asymptotic comparison. |


### What the existing query API establishes

- Exact finite query-measure inequalities are available without a machine-encoding translation.
- Bounded-error depth minimax and zero-error expected cost are distinct contracts; their separate APIs do not by themselves prove 11.17.

## Chapter 12: communication complexity

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All ten numbered results were checked on PDF pp. 237–249. The inspected two-party and number-on-forehead (NOF) APIs charge bits in deterministic binary protocol trees, with free local computation. Boolean outputs are converted to signs for discrepancy. Arbitrary monochromatic tilings need not be protocol partitions; rows below retain that distinction.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 12.4 (fooling sets) | 223 / 239 | **Covered.** `Cslib.Communication.IsFoolingSet.card_le` in [FoolingSet](../CslibFrontier/Computability/Communication/FoolingSet.lean) injects the fooling set into output-labelled leaves; `Protocol.leafCount_le_two_pow_depth` gives $m\le2^C$, hence the logarithmic bound. The stronger `card_lt_two_pow` additionally assumes the function takes another value. |
| 12.7 (tiling bound) | 224 / 240 | **Covered.** `Cslib.Communication.Protocol.exists_rectangle_partition` in [Rectangle](../CslibFrontier/Computability/Communication/Rectangle.lean) and `Protocol.leafCount_le_two_pow_depth` in [Protocol](../CslibFrontier/Computability/Communication/Protocol.lean) give a monochromatic partition with at most $2^C$ rectangles. The minimum tiling number $\chi$ is not a separately located definition; its lower bound follows by taking a minimum. |
| 12.8 | 224 / 240 | **Partial.** The distinct-leaf argument in `IsFoolingSet.card_le` ([FoolingSet](../CslibFrontier/Computability/Communication/FoolingSet.lean)) proves the protocol version. No separately formalized minimum over arbitrary monochromatic tilings, or theorem $m\le\chi(f)$ for that notion, was located in the communication modules. |
| 12.10 (rank versus tiling) | 224 / 240 | **Partial.** `Cslib.Communication.Protocol.rank_communicationMatrix_le` in [Rank](../CslibFrontier/Computability/Communication/Rank.lean) bounds matrix rank by protocol leaf count over a commutative semiring. The draft bounds rank by every arbitrary monochromatic tiling; that general tiling endpoint was not located. Its $0/1$ matrix must not be confused with the sign matrix. |
| 12.11 (discrepancy versus tiling) | 225 / 241 | **Partial.** `Cslib.Communication.Protocol.abs_sum_mul_signVal_le` in [Discrepancy](../CslibFrontier/Computability/Communication/Discrepancy.lean) yields the protocol leaf-count bound, and `two_mul_le_two_pow_mul_discrepancy` yields the bit bound. The $\chi(f)\ge1/\mathrm{Disc}(f)$ assertion for arbitrary tilings was not separately located. The draft uses uniform inputs; the API permits arbitrary PMFs. |
| 12.13 (eigenvalue bound) | 225 / 241 | **Source issue.** The claim is stated for any matrix using the largest eigenvalue magnitude. The bilinear estimate used in the proof requires the largest singular value (operator norm), or a symmetric/normal-matrix hypothesis. For example the sign matrix with rows $(1,1)$ and $(-1,-1)$ has eigenvalues zero but a nonzero one-entry rectangle sum. The private bilinear norm estimate in [Forster](../CslibFrontier/Computability/Communication/Forster.lean) is nearby infrastructure, not the literal theorem. |
| 12.16 (four-corner bound) | 226 / 242 | **Covered.** `Cslib.Communication.NOF.discrepancy_uniformOfFintype_pow_le` in [Cube](../CslibFrontier/Computability/Communication/NOF/Cube.lean) specializes to two nonempty finite parties and gives $\mathrm{Disc}(f)^4\le E(f)$, the division-free version. Its `pow_expect_mul_prod_le` proves the auxiliary Cauchy–Schwarz argument; the draft’s unnumbered internal Claims 1 and 2 are not separate chapter-numbered results. |
| 12.20 (NOF partition bound) | 229 / 245 | **Covered.** `Cslib.Communication.NOF.Protocol.isCylinderIntersection_leaf` in [Discrepancy](../CslibFrontier/Computability/Communication/NOF/Discrepancy.lean), `run_eq_of_leaf_eq` and `leafCount_le_two_pow_depth` in [Leaf](../CslibFrontier/Computability/Communication/NOF/Leaf.lean) give monochromatic cylinder-intersection fibres partitioning the inputs, with at most $2^C$ leaves. The stated conditional lower bound follows for any lower bound $R$ on all such partitions; no named minimum is required. |
| 12.21 (cube bound) | 229 / 245 | **Covered.** `Cslib.Communication.NOF.discrepancy_uniformOfFintype_pow_le` in [Cube](../CslibFrontier/Computability/Communication/NOF/Cube.lean) gives $\mathrm{Disc}(f)^{2^k}\le E(f)$ for $k\ge1$, equivalent to the draft’s root inequality. This is NOF, not number-in-hand communication. |
| 12.22 (generalized inner product) | 229 / 245 | **Covered.** `Cslib.Communication.NOF.Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le` in [GeneralizedInnerProduct](../CslibFrontier/Computability/Communication/NOF/GeneralizedInnerProduct.lean) proves $2n\le4^k C$ for $k\ge1$, stronger than the stated $\Omega(n/8^k)$. The public-coin theorem in the same module also handles error $1/3$ with additive cost two. |


## Chapter 13: circuit lower bounds

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All fourteen numbered results were checked on PDF pp. 250–270. Circuit families here are nonuniform; no construction-runtime or uniformity claim is inferred from existence of circuits. Searches included Boolean, monotone, branching-program and graph-depth APIs. General MOD separation and native space simulation are distinct from the special cases below.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 13.1 (parity outside AC⁰) | 235 / 251 | **Covered.** `Cslib.Circuits.Boolean.parity_notMem_AC0` in [AC0](../CslibFrontier/Computability/Circuit/Boolean/AC0.lean) gives the nonuniform constant-depth polynomial-size separation for unbounded AND/OR and NOT. |
| 13.2 (Håstad switching) | 236 / 252 | **Partial.** `Cslib.Logic.PL.DNF.card_switching_le` in [Switching](../CslibFrontier/Computability/DecisionTree/Switching.lean) bounds bad restrictions leaving $\ell$ variables free by $\#R(\ell-s)(4k)^s$, assuming no repeated variable in a term. It controls decision-tree depth, hence supplies switching infrastructure, but the draft’s exact $((n-t)k^{10}/n)^{s/2}$ probability bound and its parameter/rounding translation were not verified as a named endpoint. |
| 13.5 (Razborov–Smolensky) | 239 / 255 | **Partial.** `Cslib.Circuits.Boolean.Smolensky.parity_notMem_AC0Mod` in [Smolensky](../CslibFrontier/Computability/Circuit/Boolean/Smolensky.lean) covers target MOD₂ against every odd-prime modulus. It does not quantify over arbitrary distinct primes $p,q$ in $\mathrm{MOD}_p\notin\mathrm{AC}^0[q]$. Majority lower bounds also do not imply that separation. |
| 13.6 (interpolation on the agreement set) | 241 / 257 | **Partial.** `Cslib.BitString.exists_agree_of_parity` and `card_le_of_forall_exists_agree` in [LowDegreeParity](../CslibFrontier/Foundations/BooleanAnalysis/LowDegreeParity.lean) supply the low-degree agreement/dimension argument used for parity lower bounds. A declaration of the draft’s exact GF(3) interpolation statement for every function on its set $G$, with degree $n/2+\sqrt n$, was not located; the proof route is related, not an exact statement match. |
| 13.9 (monotone clique) | 242 / 258 | **Covered.** `Cslib.Circuits.Monotone.two_rpow_sqrt_lt_size` in [Asymptotic](../CslibFrontier/Computability/Circuit/Monotone/Clique/Asymptotic.lean) proves size $>2^{\sqrt k}$ when $2\le k$ and $k^4\le n$. Vertices have the $\binom n2$ distinct undirected edge coordinates. This implies the draft’s exponential bound in its nontrivial range, with explicit stronger constant; the draft omits the necessary exclusion of trivial $k=0,1$. |
| 13.10 (clique-indicator dichotomy) | 243 / 259 | **Partial.** `Cslib.Circuits.Monotone.Positive.card_superCliques` in [Positive](../CslibFrontier/Computability/Circuit/Monotone/Clique/Positive.lean) counts positive examples; `Negative.half_le_card_acceptedColorings` in [Negative](../CslibFrontier/Computability/Circuit/Monotone/Clique/Negative.lean) bounds negative acceptance. The exact $0.99$ versus $n^{-\sqrt k/20}$ dichotomy was not located. These lemmas support a different quantitative proof of 13.9. |
| 13.11 (approximating a monotone circuit) | 243 / 259 | **Source issue.** The statement introduces size $s$ but imposes no small-size hypothesis, while its proof charges per-gate errors $1/(10s)$ using parameters independent of $s$. The claimed simultaneous $0.9$ approximations require a size restriction and integer parameter conventions. [LowerBound](../CslibFrontier/Computability/Circuit/Monotone/Clique/LowerBound.lean) provides explicit error caps times circuit size (`nonempty_outputApproximator`, `choose_le_or_pow_le_mul_size`); it should not be cited as the unrestricted printed statement. |
| 13.12 (sunflower) | 244 / 260 | **Covered.** `Cslib.containsSunflower_of_forall_card_le` in [Sunflower](../CslibFrontier/Foundations/Combinatorics/Sunflower.lean) proves the finite-family bound $(p-1)^\ell\ell!$ with sets of size at most $\ell$ and distinct petals. This is the auxiliary combinatorial lemma itself, not just coverage by the final clique theorem. |
| 13.13 (Yao–Beigel–Tarui) | 247 / 263 | **Covered.** `Cslib.Circuits.Boolean.exists_symAnd_of_mem_ACC0` in [ACC0](../CslibFrontier/Computability/Circuit/Boolean/SymAnd/ACC0.lean) gives quasipolynomial-size SYM∘AND with polylogarithmic bottom fan-in. The printed statement uses OR gates; input complementation and the dual symmetric output convert AND to OR without changing these bounds. The library does not certify the construction runtime. |
| 13.14 (Valiant depth reduction) | 247 / 263 | **Covered.** `Cslib.IsGrading.exists_sdiff` in [DepthReduction](../CslibFrontier/Foundations/Combinatorics/DepthReduction.lean) removes edges $F$ with $K\#F\le r\#E$ from a $2^K$-level grading, leaving $2^{K-r}$ levels, for $r\le K$. This is the combinatorial depth-reduction lemma with explicit integer parameters; interpreting circuit depth as edge depth requires one extra vertex level and power-of-two rounding. The draft’s real $km/\log d$ edge count is an upper bound, not an exact cardinality or a claim at $d=1$. |
| 13.15 (space to branching programs) | 248 / 264 | **Endpoint not located.** No compiler from native multitape $\mathrm{SPACE}(S)$, $S\ge\log n$, to general acyclic variable-query branching programs of size $2^{O(S)}$ was located in branching-program, circuit or space-class sources. [MonoidProgram](../CslibFrontier/Computability/BranchingProgram/MonoidProgram.lean) and read-once/frontier programs restrict the model and do not supply the configuration simulation. Input-head positions, fixed machine alphabet and explicit input encoding must enter the eventual bound. |
| 13.16 (Barrington) | 248 / 264 | **Covered.** `Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five` and `NC_one_eq_polyLength_end` in [BarringtonClass](../CslibFrontier/Computability/Circuit/Boolean/BarringtonClass.lean) give nonuniform NC¹ exactly as polynomial-length width-five permutation/general transformation programs. Width is fixed, so length and total layered program size differ only by a constant factor. |
| 13.17 (monotone perfect-matching depth) | 249 / 265 | **Covered.** `Cslib.Circuits.Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add` in [BipartiteMatching](../CslibFrontier/Computability/Circuit/Monotone/BipartiteMatching.lean) gives $n\le2^{13}D+2^{14}$ for monotone formulas on subgraphs of $K_{n,n}$. Unfolding a bounded-fan-in monotone circuit into a formula preserves depth ([Unfolding](../CslibFrontier/Computability/Circuit/Unfolding.lean)); restricting general graphs to bipartite graphs transfers the obstruction. Thus even this restricted family excludes logarithmic monotone depth. This does not concern unbounded-fan-in depth. |
| 13.18 (Karchmer–Wigderson) | 250 / 266 | **Covered.** `Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity` in [KarchmerWigderson](../CslibFrontier/Computability/Circuit/Boolean/KarchmerWigderson.lean) gives equality for $n\ge1$, with binary AND/OR depth and free negations. Formula/circuit unfolding preserves that depth. The game outputs any differing coordinate, not necessarily a $0$-to-$1$ coordinate; the oriented relation belongs to the monotone variant. Zero arity is excluded because the output-coordinate type is empty. |


### What the existing circuit API establishes

- The parity, monotone-clique, Barrington and Karchmer–Wigderson endpoints have explicit finite or class-level statements.
- Valiant’s combinatorial edge-deletion lemma is present; a native space-to-general-branching-program compiler was not located.
- The polynomial approximation and switching APIs support lower bounds but do not automatically verify every quantitative auxiliary lemma in the draft.

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

## Chapter 15: average-case complexity

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All four numbered results were checked on PDF pp. 286–296. In this draft Chapter 15 is average-case complexity; proof complexity is in Chapter 21. The current APIs use length-indexed ensembles and native multitape polynomial-time predicates with explicit encodings, rather than silently identifying them with the chapter’s single distribution on all finite words.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 15.7 (average-time reduction closure) | 274 / 290 | **Partial.** `Cslib.Complexity.DistReduction.mem_AvgP` in [Reduction](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Reduction.lean) transfers errorless polynomial-time schemes with unary accuracy parameter, under an explicit polynomial length map and domination. Equivalence with the draft’s moment-based average polynomial time over a single distribution is not supplied. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) explicitly retains that equivalence as remaining work. |
| 15.8 (Levin completeness) | 275 / 291 | **Partial.** `Cslib.Complexity.BoundedHalting.distComplete_problem` in [Completeness](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Completeness.lean) proves the ensemble version of DistNP completeness (landed [#3061](https://github.com/cslib-community/cslib-frontier/pull/3061)). Its padded clock and self-delimiting machine/code header, witness convention and per-length distribution differ from the draft’s $(M,x,1^t,1^\ell)$ and global product distribution. No equivalence of those precise distributional problems was verified; [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) owns the average-case framework. |
| 15.9 (peak elimination) | 275 / 291 | **Partial.** `Cslib.Complexity.Compression.compress_polyTime`, `length_compress_le`, `two_pow_length_compress_mul_le` and `compress_injective` in [Compression](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Compression.lean) prove the bounds for each fixed input length. Injectivity is only within a length, not the global injectivity in the draft. `BoundedHalting.code` adds a framed length prefix for global injectivity, changing the claimed $|g(x)|\le|x|+1$ bound. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) tracks the framework differences. |
| 15.11 (heuristic reduction closure) | 277 / 293 | **Partial.** `Cslib.Complexity.DistReduction.mem_HeurP` in [Reduction](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Reduction.lean) transfers polynomial-time heuristic schemes for length-indexed ensembles and explicit accuracy. The draft instead uses one global distribution, its heuristic definition and a polynomially honest reduction; equivalence of these contracts was not located. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) is the existing framework owner. |


## Chapter 21: logical characterizations and proof complexity

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. The two numbered result headings on PDF pp. 450–452 were checked, including the unfinished Fagin entry. Karchmer–Wigderson is 13.18 in this source version. Named logical results do not fill a missing source statement automatically.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 21.2 (Fagin) | 435 / 451 | **Unverified.** The entire draft statement is “To be written.” There is consequently no source contract to compare. The actual library theorem `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP` in [Converse](../CslibFrontier/Computability/Complexity/Fagin/Converse.lean) characterizes isomorphism-closed classes of finite relational structures with finite vocabulary, using explicit `encStructure` and native multitape NP. This is strong nearby coverage, not verification of unwritten text. |
| 21.4 (polynomially bounded proofs) | 435 / 451 | **Source issue.** The printed statement says SAT has polynomial proof complexity iff NP = coNP. SAT already has short assignment certificates; the intended problem must be UNSAT/tautologies. `Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded` in [ProofSystem](../CslibFrontier/Computability/Complexity/ProofSystem.lean) proves the corrected UNSAT statement. Its Cook–Reckhow system is a polynomial-time surjection from bit strings, with a general verifier-to-surjection bridge for nonempty decodable languages. This is not a proof of the literal SAT formulation. |


## Chapter 22: natural proofs

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All four numbered results were checked on PDF pp. 453–459, consistently with [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712), [#4713](https://github.com/cslib-community/cslib-frontier/pull/4713) and [the inventory](README.md#remaining-collection-work). Formal measures take nonnegative integer values and need not be invariant under complementation.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 22.1 (formal-measure formula bound) | 438 / 454 | **Partial.** `Cslib.Circuits.Boolean.FormalComplexityMeasure.le_leafSize` in [FormalComplexityMeasure](../CslibFrontier/Computability/Circuit/Boolean/FormalComplexityMeasure.lean) proves the source literal/AND/OR induction for constant-free De Morgan formulas. Repository constants cost zero input leaves, whereas the source axioms do not force their measure to vanish. [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) deliberately preserves this restriction; no unrestricted zero-cost-constant formula claim is covered. |
| 22.2 (quarter density) | 438 / 454 | **Covered.** `Cslib.Circuits.Boolean.FormalComplexityMeasure.card_le_four_mul_card` in [FormalComplexityMeasure](../CslibFrontier/Computability/Circuit/Boolean/FormalComplexityMeasure.lean) proves $\#\mathcal B_n\le4\#\{g:c\le4\mu(g)\}$ if $c\le\mu(f)$. This is the exact finite integer interpretation of density at least $1/4$ above $c/4$, with no complement invariance or independence assumption; [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712). |
| 22.3 (density amplification) | 438 / 454 | **Source issue.** [Certificate](../CslibFrontier/Computability/Circuit/Boolean/FormalComplexityMeasure/Certificate.lean) proves `Cslib.Circuits.Boolean.acceptedCertificateMeasure_singleton` (measure $n$) and `card_le_two_mul_card_zero_acceptedCertificateMeasure` (at least half the truth tables have measure zero). [#4713](https://github.com/cslib-community/cslib-frontier/pull/4713) therefore refutes an unrestricted positive real threshold for the same measure, even with linearly growing witnesses. It proves neither a superlinear-witness counterexample nor amplification. Published Razborov–Rudich Theorem 5.1(b) has the missing additive $-n$ loss and remains open under [#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). |
| 22.9 (Razborov–Rudich barrier) | 441 / 457 | **Partial.** `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural` in [NaturalProof](../CslibFrontier/Computability/Circuit/Boolean/NaturalProof.lean) proves a barrier against P/poly-natural useful properties under explicit exponential circuit security of a small keyed truth-table family. `NaturalProof.IsNatural.PPoly_of_P` connects native P constructivity to P/poly. This is a stronger nonuniform security hypothesis than the draft’s uniform exponential-time distinguisher definition. The final factoring/discrete-log subexponential algorithms and equivalence to that precise security convention were not located; the generic barrier alone does not establish the bundled cryptographic conclusion. |


### What the existing natural-proofs API establishes

- The measure bound is for constant-free formulas, and the quarter-density theorem is exact.
- The certificate example is an original obstruction to unrestricted draft 22.3, not a proof of corrected amplification.
- The natural-proofs barrier states its nonuniform circuit-security hypothesis explicitly; the draft’s factoring/discrete-log consequence needs further bridges.

## Remaining audit work

Chapters 11–15, 21 and 22 are catalogued above at their recorded snapshots; other chapters remain to be audited. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
