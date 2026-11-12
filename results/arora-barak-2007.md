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

## Chapter 6: circuits

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12, with CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. The twelve numbered results were checked in
PDF pages 117–130, including the continuation of 6.26. Searches inspected Boolean circuits,
advice, circuit-value/satisfiability, PH and EXP modules on that snapshot, and the pinned CSLib
circuit API. Negative searches below mean that no matching endpoint was located in these
sources, not that no equivalent general theorem can exist. Open and closed issue/PR searches
included uniform circuits, PRAM, DC uniformity, Meyer and circuit hierarchies.

The library uses straight-line De Morgan circuits with free input wires and gate-count size,
including constant gates; the draft counts all vertices, including inputs. Polynomial classes
survive this change, but explicit size bounds require translation. Machine classes use native
multitape machines and explicit embeddings `enc : α ↪ List Bool`; choose `encBits` for the
draft's bit-string languages. Statements over arbitrary encodings only require correctness on
the encoding image, without an implicit efficient validity test.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 6.7, uniform circuits characterize P | 104 / 120 | **Partial.** `Cslib.Complexity.CircuitValue.computableInLogSpace_tableauInstance` and `exists_uniformCircuits` in [CircuitValue/Completeness.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean) give the logspace tableau writer and a polynomial-time unary-length circuit constructor; [CircuitValue.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitValue.lean)'s `CircuitValue.mem_P` supplies evaluation. The public family theorem certifies polynomial-time generation, not a bundled logspace-uniform-family equivalence. Uniform-family APIs and the remaining uniform simulations are tracked by [#4224, B2–B4](https://github.com/cslib-community/cslib-frontier/issues/4224). |
| 6.11, polynomial advice | 106 / 122 | **Covered.** `Cslib.Circuits.Boolean.PPoly_eq_PAdvice` in [Advice.lean](../CslibFrontier/Computability/Circuit/Boolean/Advice.lean) equates circuits with polynomial-length, length-dependent advice and a polynomial-time decider. `PAdvice` uses framed advice/input pairs and polynomially bounded functions, rather than literally taking the union of the exact bounds $n^c/n^d$. This is the polynomial-class endpoint, with finite lengths absorbed in constants. |
| 6.13, Karp–Lipton | 106 / 122 | **Covered.** `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT` and `PH_eq_SigmaP_two_of_NP_subset_PPoly` in [PH/KarpLipton.lean](../CslibFrontier/Computability/Complexity/Classes/PH/KarpLipton.lean). The latter quantifies over all encoded instance types; the former only needs SAT under `encCNF`. `NP_subset_PPolyOn_iff_SAT` connects the ordinary bit-string premise to the SAT premise. The collapse is the quantified-verifier PH, for every explicit encoding. |
| 6.14, Meyer EXP collapse | 107 / 123 | **Endpoint not located.** The conclusion is $\mathrm{EXP}=\Sigma_2^p$ under $\mathrm{EXP}\subseteq\mathrm{P/poly}$; ordinary Karp–Lipton only collapses PH. Searches of EXP/PH, circuit and Meyer-named modules found no EXP-to-second-level simulation. [Sparse/Meyer.lean](../CslibFrontier/Computability/Complexity/Classes/Sparse/Meyer.lean) concerns sparse/tally oracle characterizations of P/poly. [#891](https://github.com/cslib-community/cslib-frontier/issues/891) owns Kabanets–Impagliazzo, not this standalone endpoint; [#889](https://github.com/cslib-community/cslib-frontier/issues/889) has related easy-witness objectives, without this acceptance criterion. |
| 6.15, almost-all circuit lower bound | 107 / 123 | **Partial.** `Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow` in [CountingBound.lean](../CslibFrontier/Computability/Circuit/Boolean/CountingBound.lean) bounds the number of functions with at most $s$ gates. Pinned CSLib's [`Cslib.Circuits.Boolean.Shannon.exists_hard_function`](https://github.com/leanprover/cslib/blob/ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342/Cslib/Computability/Circuit/Boolean/Shannon.lean) gives an eventual existential lower bound $2^n/n$. Neither inspected public statement gives the draft's almost-all density conclusion at $2^n/(10n)$ for every $n\ge100$. An explicit finite counting/size-convention calculation remains; existence of one hard function is insufficient. |
| 6.17, size hierarchy | 108 / 124 | **Partial.** `Cslib.Circuits.Boolean.SIZE_ssubset` in [Hierarchy.lean](../CslibFrontier/Computability/Circuit/Boolean/Hierarchy.lean) proves strictness with $s\le t$, positive $t$, eventual gap $s(n)+2n+3\le t(n)$ and infinitely often $s(n)<2^n/n$; `SIZE_pow_ssubset` handles polynomial powers. The draft instead assumes $n<T<T'<2^n/(100n)$ and $T\log T=o(T')$. These imply the needed eventual separation, but a source-bound corollary translating total vertices to gates was not located. |
| 6.24, parallel computation and NC | 110 / 126 | **Endpoint not located.** No PRAM/interconnection-network machine simulation in either direction was located. [DepthClasses.lean](../CslibFrontier/Computability/Circuit/Boolean/DepthClasses.lean)'s `Cslib.Circuits.Boolean.NC` and `AC` are nonuniform circuit classes, whereas the draft uses logspace-uniform families. The draft also leaves network routing/load details informal; processor operations, word width, communication cost and uniform setup must be fixed before claiming an equivalence. [#4224](https://github.com/cslib-community/cslib-frontier/issues/4224) owns uniform-circuit work, not a parallel-machine model. |
| 6.26, consequences of P-completeness | 110–111 / 126–127 | **Partial.** `Cslib.Complexity.LogSpaceReducible.mem_L` in [LogSpace.lean](../CslibFrontier/Computability/Complexity/Classes/LogSpace.lean), with `L_subset_P`, gives the general L half by the definition of P-hardness. `CircuitValue.mem_L_iff_forall_P_eq_L` in [CircuitValue/Completeness.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean) explicitly records that instance. The NC half requires uniform NC and closure under logspace reductions, not membership in the existing nonuniform `NC i`; see [#4224](https://github.com/cslib-community/cslib-frontier/issues/4224). |
| 6.27, CIRCUIT-EVAL is P-complete | 111 / 127 | **Covered.** `Cslib.Complexity.CircuitValue.logSpaceComplete` in [CircuitValue/Completeness.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean), under native logspace many-one reductions. `encCircuitValue` explicitly encodes arity, circuit code and assignment; these are typed valid circuit instances, not a claim about rejecting every malformed binary string. |
| 6.29, DC-uniform exponential circuits | 111 / 127 | **Endpoint not located.** No direct-connection-uniform exponential-size constant-depth characterization of PH, nor its unrestricted-depth EXP extension, was located in circuit/PH/EXP source searches. Existing `AC 0` has polynomial size and no uniformity condition. The target needs polynomial-time local gate/edge access with binary gate indices and a precise encoding of the input length. The related descriptive-complexity plan [#4075](https://github.com/cslib-community/cslib-frontier/issues/4075) is not itself this circuit endpoint. |
| 6.31, CKT-SAT hardness | 112 / 128 | **Covered.** `Cslib.Complexity.CircuitSAT_npHard` in [CircuitSAT.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitSAT.lean). The proof reduces encoded CNF SAT to typed De Morgan circuits and invokes native Cook–Levin. It proves the endpoint, rather than the draft's alternative direct machine-to-circuit presentation. |
| 6.32, CKT-SAT reduces to 3SAT | 112 / 128 | **Covered by the general reduction API; not separately named.** `Cslib.Complexity.ThreeSAT_npHard` in [ThreeSAT.lean](../CslibFrontier/Computability/Complexity/Problems/ThreeSAT.lean) applies to `CircuitSAT.mem_NP` in [CircuitSAT.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitSAT.lean), giving precisely the native polynomial-time many-one reduction from `encCircuit 1` to `encCNF`. This is not a claim that the chapter's particular local Tseitin construction is the chosen proof. |

### What the existing circuit API establishes

- The advice equivalence and Karp–Lipton collapse are actual class results, with explicit
  encodings, rather than assumptions bundled into circuit records.
- The tableau writer is certified in logarithmic space; the exported `exists_uniformCircuits`
  theorem exposes polynomial-time generation. A new uniform-family interface should reuse that
  writer, not repeat the machine simulation. The unresolved uniform NC questions remain in #4224.
- Counting and interpolation of circuit complexity already support substantial size-hierarchy
  statements. A finite quantitative density result and a textbook-bound translation would make
  their precise relation to 6.15/6.17 available without overstating existing declarations.

## Chapter 7: randomized computation

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12, with the same CSLib pin as
Chapter 6. All 21 numbered results were checked in PDF pages 131–162, including the random-walk
and expander appendices. A PDF text-heading scan across both chapters found no additional
numbered result headings beyond these 33; remarks, examples, definitions and exercise requests
are not counted. The PDF itself was inspected for the formulas in 7.5, 7.11, 7.12,
7.35–7.36 and 7.41. Searches covered randomized classes, probabilistic computation, concentration,
coins and expander modules, pinned CSLib, and targeted pinned Mathlib searches for coin extraction
and expander Chernoff results. Negative findings retain those search limits. No new Lean client
or build was run for this documentation audit. Chapters 6–7 total 12 Covered, 10 Partial,
5 Endpoint not located, 6 Source issue and 0 Unverified results.

Unless otherwise qualified, complexity declarations below are in `Cslib.Complexity`.
`BPP` and `RP` use native deterministic polynomial-time verifiers on framed instance/random-word
pairs, counting uniformly chosen words of polynomial length; BPP has success at least $2/3$
and RP at least $1/2$. [Time.lean](../CslibFrontier/Computability/Complexity/Classes/Time.lean)'s
`mem_BPP_iff_exists_mem_BPTIME` supplies the fair-coin PTM characterization. `RL`/`BPL` instead
use native fair-coin multitape machines directly, consuming a fresh bit each step, with all-branch
logarithmic workspace and halting. The graph API uses finite undirected regular multigraphs
represented by involutive rotation maps; `spectralExpansion` is the absolute nonconstant
operator norm, and a uniformly chosen starting vertex plus uniform port sequence is the walk
probability space. Simple graphs are a specialization; parallel edges/loops carry multiplicity.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 7.5, Schwartz–Zippel | 119 / 135 | **Source issue.** The displayed statement omits $p\ne0$ (and sampling requires nonempty $S$). Take $p=0$, $d=0$ and nonempty $S$: it would assert nonzero evaluation with probability at least one. The corrected result is `MvPolynomial.schwartz_zippel_totalDegree_fintype` in [SchwartzZippel.lean](../CslibFrontier/Foundations/Data/MvPolynomial/SchwartzZippel.lean), over an integral domain with explicit nonzero hypothesis and finite-set counting probability. It specializes to integer coefficients and independent samples with replacement. |
| 7.8, ZPP = RP ∩ coRP | 121 / 137 | **Partial.** `ZPP_eq_RP_inter_coRP` in [ZPP.lean](../CslibFrontier/Computability/Complexity/Classes/ZPP.lean) proves the equality for polynomial-time `Option Bool` verifiers that never give a wrong answer and return an answer on at least half the seeds. The draft defines ZPP by expected polynomial running time. The module explicitly says this expected-time equivalence is not modeled; that bridge is required for literal source-model coverage. |
| 7.9, inverse-polynomial BPP gap | 121 / 137 | **Source issue; normalized endpoint not located.** Requiring success $\ge1/2+\vert x\vert ^{-c}$ on every string is impossible at $\vert x\vert =1$, where the bound is $3/2$, and needs a convention at length zero. Thus the literal class is empty, not BPP. After restricting to sufficiently large lengths or using a feasible scaled $(n+1)^{-c}$ gap, no class-level weak-gap amplification theorem was located. The fixed-$2/3$ result below does not prove it. |
| 7.10, error reduction | 122 / 138 | **Partial, after the finite-length repair of 7.9.** `mem_BPP_iff_forall_decidesWithErrorExponent` in [BPP/Amplification.lean](../CslibFrontier/Computability/Complexity/Classes/BPP/Amplification.lean) supplies every polynomial error exponent from the fixed $2/3$ threshold. The statistical ingredient `Cslib.ProbComp.countTrue_average_deviation_pow` in [Concentration.lean](../CslibFrontier/Languages/Probabilistic/Concentration.lean) supports inverse-polynomial tolerance, but no inspected theorem connects the weak-gap premise to native BPP with polynomially many majority trials. Integer polynomial exponents dominate the draft's real $d>0$ after finite-length handling. |
| 7.11, two-sided Chernoff corollary | 122 / 138 | **Source issue.** The PDF prints a two-sided probability strictly below $e^{-\delta^2pk/4}$ without a prefactor. For $k=1$, $p=1/2$, $\delta=1/4$, the left side is one and the right side is less than one. `Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_mul` in [Chernoff.lean](../CslibFrontier/Probability/Chernoff.lean) has the correct two-sided prefactor $2$ for relative deviation; `Cslib.ProbComp.countTrue_average_deviation` in [Concentration.lean](../CslibFrontier/Languages/Probabilistic/Concentration.lean) gives the additive Hoeffding form. These do not establish the false printed formula. |
| 7.12, RP error reduction | 122 / 138 | **Partial.** The rendered PDF correctly requires zero acceptance on nonmembers in both premise and conclusion. `Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent` in [RP.lean](../CslibFrontier/Computability/Complexity/Classes/RP.lean) preserves this zero acceptance and supplies every polynomial error exponent, but starts from success $1/2$, rather than the draft's inverse-polynomial success $n^{-c}$. The inverse-polynomial-success class bridge was not located; `Cslib.ProbComp.replicate_failure_pow` in [Concentration.lean](../CslibFrontier/Languages/Probabilistic/Concentration.lean) supplies a statistical ingredient, not the entire native class theorem. |
| 7.14, fair coins simulate computable bias | 124 / 140 | **Endpoint not located.** No native expected-constant-time exact sampler for a fixed $\rho\in[0,1]$ with polynomial-time binary digits was located. [PMF/Coin.lean](../CslibFrontier/Probability/PMF/Coin.lean)'s `Cslib.Probability.PMF.coin` defines the distribution; it is noncomputable and does not certify this algorithm. `Cslib.Probability.DDGTree.knuthYao_generates` and `expectedFlips_knuthYao_lt` in [DDGTree/KnuthYao.lean](../CslibFrontier/Probability/DDGTree/KnuthYao.lean) give exact output and expected flip bounds, but no native running-time certificate for computing the tree. The target compares successive independent fair bits to the fixed expansion and sums the geometrically weighted digit-computation costs. |
| 7.15, von Neumann extraction | 124 / 140 | **Endpoint not located.** For independent identically biased coins, $0<\rho<1$ is necessary: deterministic coins cannot yield a fair bit. No native repeat-until-different sampler with exact fair output and expected cost $O(1/(\rho(1-\rho)))$ was located. Existing biased-coin PMFs and finite/rejection-sampling APIs are not that expected-runtime endpoint. |
| 7.16, expander-walk error reduction | 126 / 142 | **Covered, with the spectral constant explicit.** `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_pow` in [Hitting.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Hitting.lean) gives $(\beta+\lambda(1-\beta))^k$ for $k\ge1$ uniformly started vertices, stronger than the asymptotic claim. A family requires a fixed $\lambda<1$; the decay constant depends on that bound as well as $\beta$, rather than on $\beta$ alone across arbitrary expander families. |
| 7.17, Adleman | 126 / 142 | **Covered.** `Cslib.Circuits.Boolean.BPP_subset_PPolyOn` in [PolynomialTime.lean](../CslibFrontier/Computability/Circuit/Boolean/PolynomialTime.lean), specialized to `encBits`, is BPP ⊆ P/poly. Its general statement is agreement with a circuit language on the encoding image; circuits count gates. |
| 7.18, Sipser–Gács | 127 / 143 | **Covered.** `BPP_subset_SigmaP_two_inter_PiP_two` in [PH/SipserLautemann.lean](../CslibFrontier/Computability/Complexity/Classes/PH/SipserLautemann.lean) proves the full two-sided inclusion, for the native seeded-verifier BPP and bounded-quantifier PH with any explicit encoding. |
| 7.22, UPATH ∈ RL | 130 / 146 | **Covered as a class endpoint, via a stronger algorithm.** `USTCON_mem_L` in [LogSpace/USTCON.lean](../CslibFrontier/Computability/Complexity/Classes/LogSpace/USTCON.lean), followed by `L_subset_RL` in [LogSpace/Randomized.lean](../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized.lean), proves membership for simple undirected graphs encoded by adjacency matrices with named endpoints. This uses Reingold, not the chapter's $n^3$-step random walk or hitting-time analysis; [#459](https://github.com/cslib-community/cslib-frontier/issues/459) retains that classical randomized-algorithm objective. |
| 7.27, spectral mixing of a distribution | 137 / 153 | **Covered by a general analytic bound; probability-vector corollary not separately named.** `Cslib.RotationMap.expect_walk_pow_sub_expect_sq_le` in [Mixing.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Mixing.lean) contracts variance by $\lambda^{2T}$. For a probability vector $p$, multiply its mean-square inequality by $n$ and use $\sum p_i^2\le1$ to recover $\|A^Tp-\mathbf1/n\|_2\le\lambda^T$. The library uses uniform averages rather than unnormalized Euclidean sums. |
| 7.28, connected looped graph gap | 137 / 153 | **Partial.** `Cslib.RotationMap.spectralExpansion_le_of_preconnected` in [Connected.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Connected.lean) gives $1-1/(2n^2d^2)$ when at least half the ports at every vertex are self-loops. The draft only assumes a self-loop at each vertex and claims $1-1/(8dn^3)$. Strong laziness is a genuine extra hypothesis; the different bounds are not recorded as interchangeable. The broader random-walk analysis belongs to [#459](https://github.com/cslib-community/cslib-frontier/issues/459). |
| 7.30, pointwise mixing | 138 / 154 | **Partial.** `Cslib.RotationMap.sq_expect_mul_walk_pow_sub_le` in [Mixing.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Mixing.lean), specialized to singleton indicators, controls pointwise transition probabilities. It does not by itself provide the draft's $T>10dn^3\log n$ bound for every regular graph with one loop per vertex, including restriction to the start component; the precise 7.28 bridge remains. See [#459](https://github.com/cslib-community/cslib-frontier/issues/459). |
| 7.35, existence of expanders | 141 / 157 | **Source issue.** With Definition 7.34's normalization $\vert E(S,\bar S)\vert \ge\rho d\vert S\vert $, the claimed $\rho=1-\epsilon$ for every $\epsilon>0$ is impossible for positive degree and sufficiently large even $n$: averaging over half-size sets gives some cut ratio at most $n/(2(n-1))$. Loops only decrease it. `Cslib.RotationMap.exists_forall_exists_spectralExpansion_le` in [Existence.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Existence.lean) supplies a fixed positive-degree constant-gap multigraph family, not the false near-one normalized edge expansion. |
| 7.36, combinatorial versus spectral expansion | 141 / 157 | **Source issue in part 2; part 1 covered.** `Cslib.RotationMap.le_edgeExpansion_of_spectralExpansion_le` in [Cheeger.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Cheeger.lean) gives part 1 after dividing edge expansion by degree. `secondEigenvalue_le_one_sub_edgeExpansion_sq_div` gives the correct one-sided Cheeger bound. The draft uses the absolute spectral parameter: the two-vertex single-edge graph has $\rho=1$ but absolute nonconstant eigenvalue $1$, contradicting its claimed $\le1-\rho^2/2$. A second-largest-eigenvalue or suitable laziness convention is required. |
| 7.37, expander mixing lemma | 141 / 157 | **Covered.** `Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt` in [Mixing.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Mixing.lean) states the displayed bound exactly, counting directed ports from $S$ to $T$ with multiplicity and using normalized absolute spectral expansion. |
| 7.38, expander walks stay in a set | 143 / 159 | **Covered by a stronger bound.** `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le` in [Hitting.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Hitting.lean) gives $\beta(\beta+\lambda(1-\beta))^{k-1}$ for $k\ge1$, even for varying bad sets. Since $\beta\le\sqrt\beta$ for $0\le\beta\le1$, this implies the draft's $((1-\lambda)\sqrt\beta+\lambda)^{k-1}$. Uniform start and port sampling match the draft's walk distribution. |
| 7.40, adjacency decomposition | 144 / 160 | **Partial; auxiliary lemma not separately formalized.** The orthogonal mean/mean-zero split and spectral contraction used by the draft are present in `Cslib.RotationMap.expect_walk_pow_sub_expect_sq_le` and its proof in [Mixing.lean](../CslibFrontier/Foundations/Combinatorics/Expander/Mixing.lean). No inspected public statement exposes $A=(1-\lambda)J+\lambda C$ with $\|C\|\le1$. The case $\lambda=0$ needs its own branch rather than the draft proof's division by $\lambda$. The stronger 7.38 proof does not require this named matrix decomposition. |
| 7.41, expander Chernoff | 145 / 161 | **Source issue; intended endpoint not located.** The PDF prints $2e^{+(1-\lambda)\delta^2k/60}$: this exceeds one, so it gives no concentration. A useful target needs a negative exponent. Searches of expander walks, hitting, mixing, probability concentration and pinned upstream sources found no tail bound for the fraction of bad vertices with that corrected exponent. Independent-sample Chernoff and the all-vertices-bad hitting bound do not establish this occupation-time concentration. |

### What the existing randomized API establishes

- Adleman and Sipser–Gács–Lautemann are native class inclusions. The weak-gap normalization
  is a separate missing bridge; constant-error amplification alone must not be counted as 7.9.
- The zero-error equality is proved for bounded-time partial answers. Relating it to expected-time
  Las Vegas machines, and certifying the two biased-coin procedures, needs runtime semantics beyond
  the distributional identity of a Bernoulli PMF.
- The expander API gives spectral mixing, one-sided Cheeger, and a stronger all-bad-walk bound
  than 7.38. It distinguishes the second eigenvalue from its absolute analogue. An expander
  occupation-time Chernoff bound remains distinct from all these endpoints.

The source issues above are checks of the literal draft, not refutations of the standard corrected
results. In particular, 7.9/7.10 need a feasible gap for all required lengths,
7.35 needs a corrected normalization/constant, and 7.36 needs the correct
spectral convention. Definition 7.39 also says “maximum” where the operator norm requires the
least valid upper bound; all norm comparisons here use the standard operator norm. Proposed
machine-checked counterexample clients for the elementary source defects are follow-ups, not
artifacts produced or tested by this audit.

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

## Remaining audit work

Chapters other than 6, 7 and 14 have not been catalogued here. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
