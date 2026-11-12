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

## Chapter 16: derandomization and extractors

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12, with CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. The chapter has **30 numbered results**,
including its expander and connectivity sections. Headings were checked in the PDF text across
PDF pages 297–336, rather than counting references to results as additional headings; ambiguous
formulas were checked against the page image. Printed locators below give the absolute printed
page, e.g. `p16.4 (284)` is recorded as 284. Definitions, remarks and unnumbered claims are not
additional rows. Searches inspected the NW, BPP derandomization, arithmetic PIT, MA, logspace,
expander, extractor and probability modules, plus the pinned CSLib and Mathlib named-result
searches. An **Endpoint not located** means this search found no endpoint, not a proof of semantic
absence. No Lean builds, checked new clients or whole-library dependency audit were performed.

The library's uniform classes use native multitape machines with explicit embeddings
$\alpha\hookrightarrow\mathrm{List\ Bool}$; running time is measured in encoded input length.
Its Boolean hardness is nonuniform De Morgan gate complexity, counting constants and negations.
A finite generator/security theorem alone supplies neither a native runtime certificate nor a
simulation of a space-bounded machine. These distinctions apply throughout both chapters.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 16.4 (PRGs give deterministic simulation) | 284 / 300 | **Partial.** `Cslib.Complexity.nwDecider` and `BPP_subset_P_of_isAverageCaseHard` in [BPP/Derandomization](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization.lean) certify seed enumeration for the exponential-hardness schedule. No general monotone polynomial-time $S,\ell$ theorem with $\mathrm{BPTIME}(S(\ell(n)))\subseteq\mathrm{DTIME}(2^{c\ell(n)})$ was located. Input-reading, generator-evaluation and machine-to-circuit overhead must be explicit in that generalization. |
| 16.6 (three derandomization regimes) | 285 / 301 | **Partial.** `Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard` in [BPP/Derandomization](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization.lean) gives the exponential average-case hardness consequence. It does not take an arbitrary PRG as its hypothesis; the quasipolynomial and general superpolynomial/subexponential consequences were not located. |
| 16.10 (consequences of NW) | 287 / 303 | **Partial.** The preceding `P_eq_BPP_of_isAverageCaseHard` proves the exponential special case for eventual hardness $2^{\lfloor n/c\rfloor}$ of a language in `E encBits`, for every instance encoding. [NW/Derandomization](../CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/Derandomization.lean) supplies greedy designs and finite fooling. The general $S(\epsilon\ell)^\epsilon$ generator theorem and the other two regimes were not located. Remark 16.12 explicitly says the book proves a weaker seed/hardness tradeoff, so its proof must not be cited as the stronger theorem verbatim. |
| 16.13 (one-bit generator) | 288 / 304 | **Partial.** `Cslib.Crypto.PRG.Generator.Unpredictable.secure` in [NextBit](../CslibFrontier/Crypto/Primitives/PRG/NextBit.lean) supplies the hybrid implication. No separately packaged $z\mapsto z\mathbin\circ f(z)$ generator with the draft's $n^4$ hardness and uniform exponential-time certificate was located. Small lengths require the usual eventual/asymptotic convention. |
| 16.14 (Yao next-bit theorem, 10.12 restated) | 288 / 304 | **Partial.** [NextBit](../CslibFrontier/Crypto/Primitives/PRG/NextBit.lean), `Cslib.Crypto.PRG.Generator.Unpredictable.secure`, gives error $m\delta$ assuming closure of admissible predictors under `nextBitPredictor`. The finite probability reduction is proved; that hypothesis is not itself the draft's circuit-size-$2S$ versus $S$ bound. The draft also uses an unexplained $n$ in $S>10n$ while the output length is $m$. |
| 16.15 (two-bit generator) | 289 / 305 | **Partial.** The same next-bit API provides the hybrid ingredient; fixing the independent first block is not separately packaged as the two-bit construction with uniform runtime. Odd input lengths and finitely many small lengths need conventions. |
| 16.18 (construction of designs) | 291 / 307 | **Partial.** `Cslib.Crypto.PRG.NisanWigderson.choose_le_length_greedyMasks_mul` and `le_length_greedyMasks` in [NW/Derandomization](../CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/Derandomization.lean) prove explicit greedy-design cardinality inequalities. [Generator](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization/Generator.lean) certifies the executable construction. The exact $\ell>10n^2/d$, $2^{d/10}$ corollary, with integer rounding and the draft's strict-overlap convention, was not located separately. |
| 16.19 (NW pseudorandomness) | 291 / 307 | **Partial.** `Cslib.Crypto.PRG.NisanWigderson.toReal_realExperiment_sub_toReal_idealExperiment_lt` in [NW/Circuit](../CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/Circuit.lean) proves reconstruction with circuit cost $S+m(2^a(2a+3)+1)+1$ and prediction advantage $\epsilon/m$. This is a concrete finite NW theorem, but the draft's $H_{\rm avg}/10$ size guarantee from just $2^d<\sqrt{H_{\rm avg}}$ is not the stated library corollary. |
| 16.21 (BPP = P implies lower bounds) | 293 / 309 | **Endpoint not located.** Searches of PIT, arithmetic-circuit and class modules found no Kabanets–Impagliazzo disjunction. [#891 M4](https://github.com/cslib-community/cslib-frontier/issues/891) owns it. Historical [#341](https://github.com/cslib-community/cslib-frontier/pull/341) is not present-day coverage: [#375](https://github.com/cslib-community/cslib-frontier/pull/375) withdrew overclaimed results. The draft's `AlgP/poly` and arithmetic field/constant conventions need reconciliation with circuit-based `VP`. |
| 16.23 (ZEROP in P implies lower bounds) | 294 / 310 | **Endpoint not located.** Arithmetic PIT and polynomial evaluation infrastructure do not establish the disjunction $\mathrm{NEXP}\nsubseteq\mathrm{P/poly}$ or permanent lower bounds. Owned by [#891 M4](https://github.com/cslib-community/cslib-frontier/issues/891); fix the formal PIT input/field and formula-versus-circuit convention first. |
| 16.24 (EXP in P/poly implies EXP = MA) | 294 / 310 | **Endpoint not located.** No such implication was found in the MA, EXP, nonuniform-class or derandomization sources. A prerequisite of the [#891](https://github.com/cslib-community/cslib-frontier/issues/891) proof route; the native MA class and existence of interactive protocols alone do not prove it. |
| 16.25 (PIT plus small permanent gives $\mathrm{P}^{\rm perm}\subseteq\mathrm{NP}$) | 294 / 310 | **Endpoint not located.** No oracle-class inclusion with both hypotheses was located. Exact integer permanent output encoding and arithmetic constants matter. This is part of [#891](https://github.com/cslib-community/cslib-frontier/issues/891), not merely permanent membership in VNP. |
| 16.26 (NEXP in P/poly implies NEXP = EXP) | 295 / 311 | **Endpoint not located.** Searches of NEXP, EXP, MA and nonuniform-class sources did not locate the easy-witness implication. It remains a prerequisite in [#891](https://github.com/cslib-community/cslib-frontier/issues/891)'s KI route. |
| 16.28 (matrix product improves expansion) | 298 / 314 | **Source issue.** The printed bound is $\lambda(G'G)\le\lambda(G')\lambda(G')$, repeating $G'$; the intended operator-norm product uses $\lambda(G')\lambda(G)$. Taking $G$ to be the identity walk shows why the repeated factor is not valid in general. `Cslib.RotationMap.spectralExpansion_pow_le` in [Power](../CslibFrontier/Foundations/Combinatorics/Expander/Power.lean) handles repeated powers, not the literal erroneous two-graph statement. |
| 16.29 (tensor product preserves expansion) | 299 / 315 | **Covered.** `Cslib.RotationMap.spectralExpansion_tensor_le` in [Tensor](../CslibFrontier/Foundations/Combinatorics/Expander/Tensor.lean) proves $\lambda(G\otimes H)\le\max\{\lambda(G),\lambda(H)\}$. Graphs are finite undirected labelled regular multigraphs represented by involutive rotation maps; the spectral parameter is the norm on mean-zero functions. No machine efficiency is asserted by this lemma. |
| 16.30 (replacement product expansion) | 300 / 316 | **Partial.** `Cslib.RotationMap.spectralExpansion_balancedReplacement_le` in [Replacement](../CslibFrontier/Foundations/Combinatorics/Expander/Replacement.lean) gives $1-(1-\lambda(G))(1-\lambda(H))^2/24$, and `spectralExpansion_balancedReplacement_lt_one` gives a gap. This does not give the displayed $1-\epsilon\epsilon'/4$ estimate; product/normalization and constants must be compared, rather than identifying the two bounds. |
| 16.31 (strongly explicit expander family) | 301 / 317 | **Partial.** `Cslib.RotationMap.spectralExpansion_affinePlaneTower_le` in [AffineTower](../CslibFrontier/Foundations/Combinatorics/Expander/AffineTower.lean) gives a concrete constant-degree tower. Its fixed-base rotation certificates do not prove uniform time polynomial in the bit length of a vertex name. The full strongly explicit endpoint was not located. |
| 16.32 (strongly explicit expanders at every size) | 302 / 318 | **Partial.** `Cslib.RotationMap.zigzagTowerFamily` and `spectralExpansion_zigzagTowerFamily_le` in [TowerFamily](../CslibFrontier/Foundations/Combinatorics/Expander/TowerFamily.lean) give every vertex count with constant degree/gap. `polytime_arithmeticExpanderRotate` in [RotationMap/Family](../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/RotationMap/Family.lean) charges unary size and vertex inputs and constructs tables; this is not the draft's polylogarithmic-time neighbour algorithm. |
| 16.34 (Reingold) | 303 / 319 | **Covered.** `Cslib.Complexity.USTCON_mem_L` in [LogSpace/USTCON](../CslibFrontier/Computability/Complexity/Classes/LogSpace/USTCON.lean) proves undirected connectivity in native `L encUSTCON`. The library uses its explicit graph-instance encoding; the theorem is not parameterized by every imaginable graph encoding. The proof includes the reduction to its regular labelled graph model. |
| 16.35 (logarithmic expander diameter) | 303 / 319 | **Partial.** `Cslib.RotationMap.exists_neighbor_pow_eq` in [Connected](../CslibFrontier/Foundations/Combinatorics/Expander/Connected.lean) proves an exact length-$t$ walk when $\lambda^t(\lvert V\rvert-1)<1$. This is the finite mixing ingredient, stronger once $t$ is chosen; a named $O(d\log n)$ diameter corollary and graph-distance translation were not located. |
| 16.39 (three statistical-distance facts) | 306 / 322 | **Covered.** `Cslib.Probability.PMF.dist_eq` and `dist_map_le` in pinned [CSLib StatisticalDistance](https://github.com/leanprover/cslib/blob/ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342/Cslib/Probability/StatisticalDistance.lean) give half the $\ell^1$ distance and contraction. `dist_eq_sum_filter_lt` in [StatisticalDistance](../CslibFrontier/Probability/StatisticalDistance.lean), together with `abs_toOuterMeasure_toReal_sub_le_dist` in [Event](../CslibFrontier/Probability/StatisticalDistance/Event.lean), gives an attaining event and the event upper bound. Boolean tests are indicators of these events. These are finite-PMF statements, not complexity restrictions on tests. |
| 16.41 (min-entropy bounds collisions) | 307 / 323 | **Covered.** `Cslib.Probability.PMF.collisionProbability_le_rpow_neg_minEntropy` in [MinEntropy](../CslibFrontier/Probability/MinEntropy.lean) proves the bound for arbitrary discrete PMFs. Binary logarithms are used. A lower bound $k$ on min-entropy gives the draft inequality by monotonicity of $2^{-k}$. |
| 16.42 (leftover hash lemma) | 308 / 324 | **Partial.** `Cslib.Probability.IsUniversalHash.isStrongExtractor` in [Extractor/LeftoverHash](../CslibFrontier/Probability/Extractor/LeftoverHash.lean) bounds error by $\sqrt{\lvert O\rvert(2^{-h}+\eta)-1}/2$, where $h$ is min-entropy and $\eta$ bounds pairwise collisions. The draft instead uses output length $k$, collision bound $(1+\delta)/2^k$, entropy $k/\delta$ and error $\sqrt{2\delta}$. The general hashing theorem exists; a checked derivation of this unusual parameterization, including $\delta>0$ and small $k$, was not located. |
| 16.43 (full-length extractor from walks) | 308 / 324 | **Partial.** [Extractor/Basic](../CslibFrontier/Probability/Extractor/Basic.lean) defines `Cslib.Probability.IsExtractor`; expansion and mixing machinery exists. No construction theorem with output length $n$ and seed $O(n-k+\log(1/\epsilon))$ was located. [#895](https://github.com/cslib-community/cslib-frontier/issues/895) is the existing extractor track. This is the chapter's walk construction, not an assertion that every existential extractor bound has been formalized. |
| 16.45 (Trevisan/NW extractor analysis) | 310 / 326 | **Partial.** NW black-box reconstruction and code/list-decoding APIs exist, but no `ExtNW` theorem with entropy $m^3$, error $2\epsilon$ and $\epsilon>2^{-m^2}$ was found. The bad-source counting argument is not separately formalized as an extractor proof. Existing track: [#895](https://github.com/cslib-community/cslib-frontier/issues/895). |
| 16.46 (explicit extractor parameters) | 311 / 327 | **Endpoint not located.** No native polynomial-time extractor with $k=N^{\Omega(1)}$, output $k^{1/3}$ and $O(\log N)$ seed was located. Universal matrix hashing has a different seed bound. Existing track: [#895](https://github.com/cslib-community/cslib-frontier/issues/895). |
| 16.47 (simulation from a weak source) | 312 / 328 | **Endpoint not located.** No seed-enumeration simulator with runtime $2^t(T_A+T_E)$ and success at least $3/4$ from one $(N,k+2)$-source sample was found. The preceding discussion's $3/4$ success assumption on $A$ and majority convention are required, although the theorem box omits the former. Existing track: [#895](https://github.com/cslib-community/cslib-frontier/issues/895). |
| 16.48 (Nisan) | 313 / 329 | **Partial.** `Cslib.Crypto.PRG.Nisan.secure_bitGenerator_of_le` and `card_bitSeed` in [Nisan/Bits](../CslibFrontier/Crypto/Primitives/PRG/Nisan/Bits.lean) prove finite read-once branching-program security with $O(\log(wR/\epsilon)\log R)$ seed bits. Native polynomial-time generator realization and a machine/configuration bridge yielding the stated simulation were not located. In particular the adjacent $\mathrm{BPL}\subseteq\mathrm{DSPACE}(\log^2 n)$ consequence is not supplied by this finite security theorem. [#459](https://github.com/cslib-community/cslib-frontier/issues/459) owns the machine endpoint; [#3187](https://github.com/cslib-community/cslib-frontier/issues/3187)/[#3216](https://github.com/cslib-community/cslib-frontier/pull/3216) completed the branching-program milestone. |
| 16.49 (recycling lemma) | 314 / 330 | **Partial.** `Cslib.Probability.IsTwoUniversal.leftover_hash_conditional_of_isSource` in [MinEntropy/LeftoverHash](../CslibFrontier/Probability/MinEntropy/LeftoverHash.lean) handles hashing when every conditional source has an entropy guarantee. The draft allows any extractor and discards rare heavy side-information fibers; that endpoint with $k=n-(s+1)-\log(1/\epsilon)$ was not located. Existing extractor track: [#895](https://github.com/cslib-community/cslib-frontier/issues/895). |
| 16.52 (recursive generator error) | 315 / 331 | **Partial.** `Cslib.Crypto.PRG.Nisan.abs_dens_foldlIdx_blocks_sub_le` in [Nisan](../CslibFrontier/Crypto/Primitives/PRG/Nisan.lean) gives error $(2^k-1)w/(2\sqrt{\lvert X\rvert})$ for the hashing generator. It is not the draft's extractor-recursive $3^k\epsilon$ theorem. Definition 16.51 also needs an indexing repair: its displayed output length is $2^k$ but its $k=1$ case outputs one bit. Existing tracks: [#895](https://github.com/cslib-community/cslib-frontier/issues/895), [#459](https://github.com/cslib-community/cslib-frontier/issues/459). |

### What the existing API establishes

- **Exponential hardness:** [BPP/Derandomization](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization.lean)
  proves the uniform `P = BPP` consequence of eventual exponential average-case hardness in `E`.
  This does not cover all monotone hardness functions $S$ or arbitrary supplied PRGs.
- **Finite pseudorandomness:** NW reconstruction has explicit gate overhead; Nisan security
  concerns read-once programs. The latter's seeds are a finite product type of the stated
  cardinality, not yet a native encoded generator evaluation theorem.
- **Expanders:** spectral products, a concrete tower and every-size families are available.
  Unary-size table construction and a strongly explicit neighbour algorithm are different claims.
- **Extractors:** seeded/strong extractor definitions and universal-hashing constructions are
  available. The Trevisan, weak-source simulation and arbitrary-extractor recycling endpoints
  remain with the existing extractor track. Neither PIT correctness nor the arithmetic
  lower-bound developments complete the KI disjunction.

## Chapter 17: hardness amplification and error-correcting codes

Snapshot and model conventions: the same main and dependency revisions as Chapter 16 above.
All **13 numbered result headings** were checked in the PDF text across pages 337–364,
including 17.26–17.28 and the final 17.31 after the earlier headline hardness results. Inspection covers the hard-core,
XOR, worst-case encoding/schedule, code, Sudan interpolation and local decoding modules.
General finite coding bounds, probabilistic oracle-query decoding, native encoding runtime and
uniform language-family hardness are distinguished. The searches and no-build limitations above
apply; a missing packaged corollary is not a claim that its finite mathematics is unavailable.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 17.2 (Yao XOR lemma) | 322 / 338 | **Partial.** `Cslib.Circuits.Boolean.card_eq_xorPower_div_le` in [XorLemma](../CslibFrontier/Computability/Circuit/Boolean/XorLemma.lean) proves agreement at most $1/2+\eta+(1/2-\eta)(1-\delta)^k$, from hardness against size $T(s+3)+2+2T(T+2)$ with $1\le3\eta^2\delta^2T$. This is a genuine nonuniform XOR lemma; it does not give the draft's sharp retained size $\epsilon^2 S/(100\log(1/(\delta\epsilon)))$ under $\epsilon>2(1-\delta/2)^k$. |
| 17.5 (Impagliazzo hard-core lemma) | 323 / 339 | **Partial.** `Cslib.Circuits.Boolean.exists_isHardCoreMeasure_of_le` in [HardCore](../CslibFrontier/Computability/Circuit/Boolean/HardCore.lean) gives a $[0,1]$-weighted hard core of density at least $\delta$, size $(S-(2+2T(T+2)))/T$ and advantage $\epsilon$, for $1\le3\epsilon^2\delta^2T$. Normalizing its positive mass gives a distribution. The draft's logarithmic size-loss estimate is not supplied. Its printed $f:\{0,1\}^n\to\{0,1\}^n$ is a type typo in a Boolean-prediction statement. [#3557](https://github.com/cslib-community/cslib-frontier/issues/3557) and [#3567](https://github.com/cslib-community/cslib-frontier/pull/3567) concern set rounding, not that sharp parameter target. |
| 17.9 (existence of constant-rate codes) | 329 / 345 | **Partial.** `Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose` in [HammingBound](../CslibFrontier/Foundations/Data/Code/HammingBound.lean) gives the finite Gilbert bound; `card_filter_hammingDist_le_le_exp_mul_qaryEntropy` in [BallVolume](../CslibFrontier/Foundations/Data/Code/BallVolume.lean) bounds ball volume. The exact binary-message injection at rounded length $2n/(1-H(\delta))$, for $0<\delta<1/2$ and large $n$, is not separately stated. [#4666](https://github.com/cslib-community/cslib-frontier/issues/4666) owns a stronger linear-code existence program; this audit does not count that open objective as proved. |
| 17.14 (local decoding implies hardness amplification) | 332 / 348 | **Source issue.** The displayed conclusion is $H_{\rm wrs}(g)(n)\ge S(\epsilon n)^\epsilon$, whereas the section and Figure 17.2 describe average-case hardness. Thus the box does not state its intended amplification endpoint. [WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean), `Cslib.Circuits.Boolean.complexity_le_of_agree_hardnessEncode`, supplies reconstruction for a particular Reed–Muller/Hadamard encoding, not a generic theorem from an arbitrary locally decodable ECC. [#2929](https://github.com/cslib-community/cslib-frontier/issues/2929) owns query-bounded LDC infrastructure, not automatically this uniform class bridge. |
| 17.15 (Walsh–Hadamard distance) | 332 / 348 | **Covered.** `Cslib.BitString.two_mul_hammingDist_hadamardCode` and `hadamardCode_injective` in [Hadamard](../CslibFrontier/Foundations/Data/Code/Hadamard.lean) prove injectivity and exact distance half the block length for distinct messages. `minDist_range_hadamardCode` assumes a nonempty message-coordinate type; at zero message bits there is only one message, so pairwise separation is vacuous. No efficient decoding claim is needed for this result. |
| 17.18 (Reed–Solomon distance) | 334 / 350 | **Covered.** `Cslib.Code.le_minDist_reedSolomon` and `minDist_reedSolomon` in [ReedSolomon](../CslibFrontier/Foundations/Data/Code/ReedSolomon.lean) give distance $m-n+1$ for degree $<n$ evaluated at $m$ distinct points, with $1\le n\le m$ for equality. This implies the draft's weaker relative separation $1-n/m$. The source definition uses “at least” separation; this is not an equality to the weaker bound. |
| 17.20 (concatenation distance) | 335 / 351 | **Covered.** `Cslib.Code.mul_hammingDist_le_hammingDist_concat` and `le_minDist_image_concat` in [Concatenation](../CslibFrontier/Foundations/Data/Code/Concatenation.lean) give the product lower bound for any inner/outer codes. Specializing to RS and Hadamard, using a fixed binary representation of field symbols, yields the draft bound. Distances are absolute natural numbers before normalization; no encoding/decoding runtime is part of this claim. |
| 17.24 (worst-case to mild hardness) | 340 / 356 | **Partial.** `Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode` in [WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean) gives explicit finite reconstruction. `Cslib.HardnessEncoding.encodedLanguage_mem_E` in [PolyTime](../CslibFrontier/Computability/Complexity/HardnessEncoding/PolyTime.lean) supplies uniform `E` membership; `eventually_isAverageCaseHard_encodedSlice` in [Schedule](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/Schedule.lean) treats exponential worst-case hardness. No all-functions-$S$ family theorem with retained hardness $S(n/c)/n^c$ and $0.99$ agreement was located. |
| 17.25 (worst-case hardness gives PRGs) | 341 / 357 | **Partial.** `Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity` in [BPP/WorstCaseHardness](../CslibFrontier/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean) proves `P = BPP` from eventual exponential worst-case circuit hardness of a language in `E encBits`. It does not state an $S(\sqrt\ell)^\epsilon$-PRG theorem for general $S$. A generalization must state regularity, growth and rounding assumptions on $S$ instead of inheriting the box's unrestricted $S:\mathbb N\to\mathbb N$. |
| 17.26 (Johnson bound) | 342 / 358 | **Covered.** `Cslib.Code.card_filter_hammingDist_le_mul_two_mul_sq_lt_one` in [BinaryJohnson](../CslibFrontier/Foundations/Data/Code/BinaryJohnson.lean) gives list size strictly below $1/(2\delta^2)$ for distance at least $1/2-\delta^2$ and radius $1/2-\delta$, with $\delta>0$ and nonempty positions. For draft distance $1/2-\epsilon$ and $\delta\ge\sqrt\epsilon$, this applies by weakening separation. The vectors counted must be distinct **codewords**, as the surrounding text specifies, not arbitrary vectors near the received word; division by zero at $\delta=0$ is excluded. |
| 17.27 (Sudan interpolation) | 343 / 359 | **Partial.** `Cslib.Code.Sudan.exists_isInterpolant` and `isInterpolant_interpolant` in [SudanInterpolant](../CslibFrontier/Foundations/Data/Code/SudanInterpolant.lean) supply nonzero interpolants under an explicit monomial-count condition, with weighted degree. The rectangular bidegree $\lceil\sqrt m\rceil+1$ corollary and a native polynomial-time construction certificate for that exact input representation were not located. Polynomial expressions and an executable linear-algebra definition alone do not certify the boxed runtime. |
| 17.28 (agreement implies polynomial factor) | 343 / 359 | **Covered.** `Cslib.Code.Sudan.IsInterpolant.eval_eq_zero` and `IsInterpolant.X_sub_C_dvd` in [SudanInterpolant](../CslibFrontier/Foundations/Data/Code/SudanInterpolant.lean) prove the root-count/divisibility argument when substituted degree is below the number of agreeing distinct abscissae. Its weighted-degree API uses $D$ in place of $(d+1)(\lceil\sqrt m\rceil+1)$. For the draft bidegree bound $r$, substitution has degree at most $(d+1)r$. The input is a set of pairs: agreeing distinct pairs have distinct abscissae. Repeated data records would require deduplication, rather than counting multiplicity as additional roots. |
| 17.31 (worst-case to strong average-case hardness) | 346 / 362 | **Partial.** `Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice` in [Schedule](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/Schedule.lean), together with `encodedLanguage_mem_E` in [PolyTime](../CslibFrontier/Computability/Complexity/HardnessEncoding/PolyTime.lean), proves eventual exponential average-case hardness in `E` from eventual exponential worst-case hardness. This is the strong-hardness special case, not a theorem for arbitrary $S$ with retained hardness $S(n/c)^{1/c}$. The draft proof's footnote assumes growth/computability of $S$ and sketches removing them; no corresponding general schedule/guessing construction was located. |

### What the existing API establishes

- **Hardness amplification:** there are actual quantitative XOR and hard-core theorems. Their
  polynomial loss in $1/\delta$ is not the logarithmic loss in the draft. The hard-core
  distribution formulation should also not be confused with the separate hard-core set theorem.
- **Coding:** Hadamard distance, RS distance, concatenation, finite Gilbert and Johnson bounds,
  and Sudan interpolation/root containment are present. Counting lemmas do not by themselves
  certify the runtime of the corresponding decoder or a native local-query implementation.
- **Uniform hardness:** the explicit Reed–Muller/Hadamard encoding and its exponential-hardness
  schedule give `P = BPP` from eventual exponential worst-case hardness. The general-$S$
  17.24/17.25 endpoints remain separate. These results do not establish infinitely-often
  hardness variants or all resource tradeoffs in the book.

## Remaining audit work

Chapters other than 14, 16 and 17 have not been catalogued here. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
