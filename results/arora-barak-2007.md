# Arora–Barak draft coverage audit

Audit and checked client: Christian Reitwiessner, with Codex assistance.

This is a growing statement-level audit under [#4711](https://github.com/cslib-community/cslib-frontier/issues/4711),
not a completeness claim for the book or library. The scope includes exercises that establish
new theory; routine practice is excluded. Its source is the
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

## Chapter 8: interactive proofs

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12, CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. The 17 numbered results were checked against
PDF pages 163–186, including Claim 8.13.1 and the permanent appendix. PDF text/layout inspection
found no additional numbered theorem, lemma, corollary, claim, fact or proposition headings.
Definitions, remarks and examples are not counted. Searches inspected `Classes/IP`,
`Classes/ArthurMerlin`, `Classes/MIP`, `Computability/PCP`, arithmetic permanent modules and
neighboring source, and searched pinned CSLib. Negative findings mean that no endpoint was
located in these searches, not a proof of absence from all equivalent general theorems.
The native verifier model uses multitape TMs, explicit embeddings `enc : α ↪ List Bool`,
and strict polynomial clocks. `IP` permits stateful word provers with completeness $2/3$ and
soundness $1/3$; those conventions must be distinguished from particular perfectly complete
textbook protocols. Class names below are in `Cslib.Complexity` unless qualified.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 8.3, $\mathrm{dIP}=\mathrm{NP}$ | 148 / 164 | **Endpoint not located.** `IP` and deterministic verifier/game infrastructure do not supply a located deterministic-interaction class equality. Searches for `dIP` and deterministic interactive proofs found no endpoint. A transcript certificate needs a polynomial total communication/time bound, not just a bound on the number of rounds. |
| 8.8, Goldwasser–Sipser | 152 / 168 | **Covered.** [`IPPolyRounds_subset_AMPolyRounds`](../CslibFrontier/Computability/Complexity/Classes/IP/Games/PolyRounds.lean) proves dynamic $\mathrm{IP}[k(n)]\subseteq\mathrm{AM}[k(n)+2]$. Shape/coin maps are uniformly polynomial-time from unary input length. [`IPPolyQueryBounded_eq_IPPolyRounds`, `IPPolyQueryBounded_subset_AMPolyRounds`](../CslibFrontier/Computability/Complexity/Classes/IP/Games/Oracle.lean) connect strict oracle-PPT verifiers: $q(n)$ request/response exchanges correspond to $2q(n)$ individual moves, followed by two extra moves. The draft's AM[2] convention counts individual messages. The variable-round proof is landed [#4424](https://github.com/cslib-community/cslib-frontier/pull/4424), completing [#3425](https://github.com/cslib-community/cslib-frontier/issues/3425); the older constant-round `IPk_subset_AMk` alone would not suffice. |
| 8.9, GNI in constant-round AM | 152 / 168 | **Covered.** [`GraphNonIsomorphism.mem_AM`](../CslibFrontier/Computability/Complexity/Classes/ArthurMerlin/GraphNonIsomorphism.lean), together with [`AMk_two`](../CslibFrontier/Computability/Complexity/Classes/ArthurMerlin/Games.lean), gives two-move membership. Uses the library's finite graph-pair encoding `encGraphIsomorphism`, with bounded error; it does not claim perfect completeness for the displayed draft protocol. |
| 8.11, efficient pairwise independent hashing | 153 / 169 | **Partial.** [`Cslib.Probability.isPairwiseIndependentHash_affineHash`](../CslibFrontier/Probability/PairwiseIndependentHash/Affine.lean) proves pairwise independence for affine vector maps over finite fields. This includes scalar maps over a field of size $2^n$ mathematically, but does not itself construct a uniform polynomial-time field presentation of $\mathrm{GF}(2^n)$ for the draft's scalar family. Binary affine matrices used by the AM API are an alternative family. |
| Claim 8.13.1, set-hashing lower bound | 155 / 171 | **Covered.** [`Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_mem_image`](../CslibFrontier/Probability/PairwiseIndependentHash.lean) proves the $\frac34|S|/|Y|$ bound under $2|S|\le |Y|$, for every fixed target $y$. Averaging over independent uniform $y$ gives the draft version; no efficiency claim is part of this finite probability lemma. |
| 8.16, GI completeness collapses level two | 157 / 173 | **Partial.** [`PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism`](../CslibFrontier/Computability/Complexity/Classes/ArthurMerlin/Collapse.lean) proves the stronger PH collapse for `NPComplete encGraphIsomorphism GraphIsomorphism`. The draft's exact $\Sigma_2=\Pi_2$ conclusion is not that declaration's statement; recovering it uses complement closure and level inclusions. No new checked client for that consequence is claimed. |
| 8.17, LFKN–Shamir | 157 / 173 | **Covered.** [`IP_eq_PSPACE`](../CslibFrontier/Computability/Complexity/Classes/IP/Shamir.lean), using `PSPACE_subset_IP` and [`IP_subset_PSPACE`](../CslibFrontier/Computability/Complexity/Classes/IP/PSPACE.lean), proves equality for every explicit input encoding. Native strict oracle-PPT verifiers and polynomial workspace replace the draft's informal machine bounds; the lower direction is through encoded TQBF arithmetization. |
| 8.18, $\#\mathrm{SAT}_D\in\mathrm{IP}$ | 158 / 174 | **Partial.** [`IP_eq_PSPACE`](../CslibFrontier/Computability/Complexity/Classes/IP/Shamir.lean) and counting-space infrastructure are available, but no declaration for the encoded pair $(\varphi,K)$ with exact count equality was located. General sumcheck is not by itself the certified membership of this decision language. |
| 8.20, PSPACE circuits imply PSPACE = MA | 162 / 178 | **Endpoint not located.** No `PSPACE ⊆ PPoly` to `PSPACE = MA` endpoint was located in IP, AM or circuit/advice sources. [#891](https://github.com/cslib-community/cslib-frontier/issues/891) is a related Kabanets–Impagliazzo lead, but its stated M4 scope does not explicitly own this collapse. The missing step is an efficiently implementable honest prover under the circuit assumption, not IP = PSPACE alone. |
| 8.23, GNI program checker | 163 / 179 | **Endpoint not located.** The private/public-coin GNI protocols do not establish a checker for an arbitrary supplied program: global correctness must give acceptance always, while error at the designated instance must be detected with probability at least $1-2^{-k}$, in polynomial oracle time. No checker contract/endpoint was located. |
| 8.24, GI, permanent and TQBF have checkers | 163 / 179 | **Endpoint not located.** No oracle-checker construction for these three problems was located. The required honest-prover implementation with access to the problem is additional to protocol soundness. [#892](https://github.com/cslib-community/cslib-frontier/issues/892) concerns delegation/MIP, not this checker endpoint. |
| 8.25, NC checkers for P-complete languages | 164 / 180 | **Endpoint not located.** No NC oracle-checker endpoint or transfer along NC reductions was located. The oracle/query convention and uniformity of NC must be fixed; membership of the language in P does not supply this parallel checker. |
| 8.26, BFL, NEXP = MIP | 164 / 180 | **Partial.** [`MIP_subset_NEXP`](../CslibFrontier/Computability/Complexity/Classes/MIP/NEXP.lean) proves the upper containment with finite independently stateful prover families and a strict polynomial-time verifier. `MIP₂_subset_NEXP` also exists. NEXP $\subseteq$ MIP remains [#892](https://github.com/cslib-community/cslib-frontier/issues/892). |
| 8.27, NEXP = PCP[poly, poly] | 164 / 180 | **Endpoint not located.** The polynomial-randomness/query characterization and its connection to MIP were not located on the audited main in `Classes/PCP`, `Computability/PCP` or MIP source. Open [#3609](https://github.com/cslib-community/cslib-frontier/pull/3609) proves `PCPPoly_subset_MIP₂` for an oracle-PCP model; it is not part of this snapshot and does not prove NEXP $\subseteq$ PCPPoly. [#892](https://github.com/cslib-community/cslib-frontier/issues/892) owns the underlying NEXP-to-MIP direction; a PCP correspondence remains additional work. |
| 8.28, PCP theorem | 165 / 181 | **Covered.** [`NP_eq_PCP_log`](../CslibFrontier/Computability/PCP/Completeness.lean) proves equality with `PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) input`. [`PCP`](../CslibFrontier/Computability/Complexity/Classes/PCP.lean) includes constant multipliers in both bounds, so this is logarithmic randomness and constantly many nonadaptive Boolean queries, with perfect completeness and soundness $1/2$, not literally one query. Input length is the explicit encoding length. |
| 8.30, Lipton permanent random self-reduction | 168 / 184 | **Endpoint not located.** No certified worst-case recovery algorithm from an oracle correct on a $1-1/(3n)$ fraction of matrices over a finite field of size $>3n$ was located. Permanent polynomial identities and interpolation prerequisites do not supply the randomized oracle algorithm and its success/time guarantee. [#321](https://github.com/cslib-community/cslib-frontier/issues/321) is algebraic completeness, not this result. |
| Claim 8.32, permanent interactive proof | 169 / 185; proof continues 170 / 186 | **Endpoint not located.** No certified protocol for a claimed permanent value with the appendix's recursive minor interpolation, perfect completeness and accumulated soundness bound was located. IP = PSPACE gives a route to abstract membership after an encoded language/space proof, but does not verify this particular protocol. Neither [#321](https://github.com/cslib-community/cslib-frontier/issues/321) nor [#892](https://github.com/cslib-community/cslib-frontier/issues/892) explicitly owns it. |

### What the existing API establishes

- Dynamic public/private-coin games have a uniform Goldwasser–Sipser conversion. The oracle
  bridge counts a request/response exchange as two moves; constant-round collapse is separate.
- IP = PSPACE and the PCP theorem are actual class equalities. No claim is made here that their
  proof terms implement each auxiliary protocol in the draft.
- The MIP upper bound and algebraic permanent APIs leave the reverse MIP direction, permanent
  random self-reduction and checker endpoints distinct. The audit proposes gaps, not ownership
  transfers from the existing implementation issues.

## Chapter 9: counting complexity

Snapshot and native model: the Chapter 8 snapshot above. All nine numbered results were checked
against PDF pages 187–201. Searches covered `Classes/SharpP`, `GapP`, `Toda`, `ValiantVazirani`,
`CookLevin/Counting`, counting problems, permanent and graph-counting source, plus pinned CSLib.
No additional numbered result headings were found in the PDF text/layout scan. Negative findings
have the same qualified scope as Chapter 8. `SharpP enc` counts fixed-polynomial-length accepted
Boolean witnesses of a native polynomial-time verifier; its machine correspondence is
[`mem_SharpP_iff_exists_machine`](../CslibFrontier/Computability/Complexity/Classes/SharpP/Characterization.lean).
Binary result encoding and the reduction type matter: parsimonious completeness and polynomial-time
oracle completeness must not be identified. Names below are in `Cslib.Complexity` unless qualified.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 9.4, $\#\mathrm{CYCLE}\in\mathrm{FP}\Rightarrow\mathrm{P}=\mathrm{NP}$ | 173 / 189 | **Endpoint not located.** No exact simple directed-cycle counting function with the Hamiltonian-cycle amplification reduction was located. Hamiltonian-path counting and Euler-tour/spanning-tree counting are different functions. No dedicated owner was found by the issue/PR searches described below. |
| Proposition 9.6, complete counting in FP collapses #P | 174 / 190 | **Partial.** [`SharpPComplete`, `ParsimoniousReducible`](../CslibFrontier/Computability/Complexity/Classes/SharpP/Completeness.lean), native polynomial-time composition and [`mem_SharpP_of_polyTime`](../CslibFrontier/Computability/Complexity/Classes/SharpP/PolyTime.lean) supply the ingredients for the parsimonious version. No bundled FP = #P endpoint for the draft's oracle-reduction definition was located. FP here must be natural-valued functions with binary output, rather than all word-valued functions. |
| 9.7, #SAT completeness | 174 / 190 | **Covered.** [`Cslib.Complexity.CookLevin.SharpSAT_sharpPComplete`](../CslibFrontier/Computability/Complexity/CookLevin/Counting.lean) proves parsimonious completeness, stronger than oracle hardness. Counts assignments to the distinct variables occurring in encoded CNF, with uniquely determined auxiliary tableau variables. `encCNF` replaces the draft's unspecified Boolean-formula representation. |
| 9.8, Valiant, 0/1 permanent #P-completeness | 175 / 191 | **Endpoint not located.** No polynomial-time counting-oracle hardness theorem for unrestricted 0/1 matrices was located. [`permFamily_mem_VNP`](../CslibFrontier/Computability/Circuit/Arithmetic/Permanent.lean) concerns algebraic polynomial families, not #P. [#321](https://github.com/cslib-community/cslib-frontier/issues/321) owns algebraic VNP completeness; [#2095](https://github.com/cslib-community/cslib-frontier/issues/2095) concerns bounded-degree counting algorithms. Neither is this Boolean counting-hardness endpoint. Do not use parsimonious `SharpPComplete` as a silent replacement for the draft's oracle reduction. |
| 9.11, Toda | 179 / 195 | **Partial.** [`PH_subset_PWithSharpPOracle`](../CslibFrontier/Computability/Complexity/Classes/Toda.lean) proves PH $\subseteq$ P with a #P bit oracle; its proof constructs one queried bit, though the class does not record a query count. The literal draft target is a fixed #SAT oracle. Parsimonious #SAT completeness exists, but no packaged transfer from this bit-oracle class to that particular encoded oracle was located. This is not a missing Toda containment proof. |
| 9.15, Valiant–Vazirani | 180 / 196 | **Partial.** [`ValiantVazirani.three_div_le_dens_reduce_mem_USAT`](../CslibFrontier/Computability/Complexity/Classes/ValiantVazirani/Reduction.lean) gives success at least $3/(32(v+3))$, where $v$ counts variable occurrences, with `reduce_mem_UNSAT` preserving unsatisfiability. The draft requires $1/(8n)$ for $n$ variables and outputs odd-SAT. Unique satisfiability implies odd parity, but the parameter bound is weaker. [`NP_subset_RPWithPromiseOracle_PromiseUSAT`](../CslibFrontier/Computability/Complexity/Classes/ValiantVazirani.lean) gives the amplified promise-oracle consequence. |
| Lemma 9.16, isolation | 180 / 196 | **Covered.** [`Cslib.Probability.IsPairwiseIndependentHash.three_sixteenths_le_dens_filter_card_filter_eq_one`](../CslibFrontier/Probability/PairwiseIndependentHash.lean) gives $3/16\ge1/8$ under $|Y|\le4|S|$ and $2|S|\le|Y|$, exactly the source size window written without truncated natural subtraction. It holds for arbitrary finite pairwise independent families and fixed target, including the zero target. |
| Lemma 9.18, constant alternation to random parity | 181 / 197 | **Partial.** [`Toda.exists_isRandomParityRep_alternation`](../CslibFrontier/Computability/Complexity/Classes/Toda/Hierarchy.lean) constructs polynomial-time parity representations with arbitrary inverse-exponential two-sided error. The draft requires no false positives and success at least $2/3$ on true QBFs. The existing theorem's two-sided guarantee does not imply that exact one-sided endpoint or a concrete output formula. |
| Lemma 9.19, parity to counts modulo $2^{m+1}$ | 183 / 199 | **Partial.** [`Toda.testBit_card_filter_sharpTest`](../CslibFrontier/Computability/Complexity/Classes/Toda/Counting.lean) and [`exists_SharpP_testBit_of_mem_BPOp_ParityP`](../CslibFrontier/Computability/Complexity/Classes/Toda.lean) implement a counting/bit-extraction route to Toda. No explicit polynomial-time formula transformation $T(\psi,1^m)$ with counts $-1$ or $0$ modulo $2^{m+1}$ was located. The source's $\varphi$ is read as the output $T(\psi,1^m)$. |

### What the existing API establishes

- The witness and machine definitions of #P are connected, and #SAT has exact parsimonious
  completeness. Algebraic VNP membership of the permanent is a separate theorem.
- Toda's class containment is proved with a bit-oracle representation. This audit retains the
  fixed-#SAT interface gap and distinguishes alternative proof machinery from the draft's
  one-sided/formula-level auxiliary lemmas.
- Valiant–Vazirani isolation has a strong finite probability lemma, but the implemented formula
  reduction documents a weaker occurrence-dependent success bound.

## Chapter 10: cryptography

Snapshot: the Chapter 8 snapshot above. All eight numbered results were checked against PDF
pages 203–219; the PDF scan found no additional numbered result heading. The zero-knowledge
application in §10.4 is unnumbered and is discussed below, not counted as an extra theorem.
Inspection covered `Crypto/Computational` (OWF, PRG, Goldreich–Levin, discrete log, stretch,
nonuniform security and ZK), `Crypto/Primitives/PRG`, and BPP derandomization, plus pinned CSLib.
Negative searches are qualified as above. Uniform crypto theorems use word algorithms with
native strict PPT certificates, unary security parameters and negligible advantage. Such an
asymptotic theorem does not establish an explicit finite-time security exponent. All `Crypto`
names below are in `Cslib.Crypto` unless otherwise indicated.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 10.5, discrete-log random self-reduction | 191 / 207 | **Partial.** [`PrimeOrderGroupFamily.uniform_smul_generator_add`](../CslibFrontier/Crypto/Computational/DiscreteLog.lean) supplies the uniform group-mask identity in prime-order groups. No recovery/repetition theorem with time $O(\delta^{-1}\log(1/\epsilon)(t(n)+\mathrm{poly}(n)))$ was located. The draft uses the full multiplicative group modulo prime $p$, of order $p-1$, which is generally composite; the prime-order subgroup interface is not that model. The proof text's reciprocal-log repetition count is a typo relative to the theorem's bound. |
| Corollary 10.6, worst-case to almost-all discrete log | 191 / 207 | **Partial.** The masking infrastructure above is present, but no asymptotic hardness transfer for every infinite prime sequence was located. “Hard” and “almost all” need explicit time/success and sequence quantifiers; no claim about an unproved discrete-log assumption follows from the group identity alone. |
| 10.12, prediction versus indistinguishability | 194 / 210 | **Partial.** [`PRG.Generator.advantage_le_sum_predictionAdvantage`, `PRG.Generator.Unpredictable.secure`, `PRG.Generator.Secure.unpredictable`](../CslibFrontier/Crypto/Primitives/PRG/NextBit.lean) prove finite hybrid/probability implications. Their arbitrary finite tests do not certify the draft's time budget $2t(n)$ with $t(n)\ge N(n)^2$. Also Definition 10.9 samples the prediction index only up to seed length $n$ although the output length is $N(n)$; the usual full-output next-bit convention must be used before identifying the source theorem with this API. |
| 10.13, OWF iff PRG | 196 / 212 | **Covered.** [`exists_oneWay_iff_exists_pseudorandomGenerator`](../CslibFrontier/Crypto/Computational/PRGToOneWay.lean), using [`OneWay.exists_pseudorandomGenerator`](../CslibFrontier/Crypto/Computational/OneWayToPRG.lean), proves the uniform strict-PPT/negligible-advantage equivalence for word functions. One-bit stretch is amplified to arbitrary polynomial stretch by [`PseudorandomGenerator.amplify`](../CslibFrontier/Crypto/Computational/Stretch.lean). This is existential asymptotic security, with no asserted optimal reduction exponent or concrete candidate OWF. |
| 10.14, Goldreich–Levin | 197 / 213 | **Partial.** [`GoldreichLevin.negligible_parityPrediction`, `GoldreichLevin.word_prediction_advantage_le`](../CslibFrontier/Crypto/Computational/GoldreichLevin/WordReduction.lean) give a uniform inverter reduction and negligible prediction bias for general OWFs; [`GoldreichLevin.padded_hardCore`](../CslibFrontier/Crypto/Computational/GoldreichLevin/HardCore.lean) packages a hard-core predicate. The source's explicit $S(n)=\min\{s(n),1/\epsilon(n)\}^{1/8}$ runtime/advantage bound for permutations was not located as a certified theorem. |
| Claim 10.15, averaging good inputs | 197 / 213 | **Partial.** [`GoldreichLevin.dens_filter_agreement_ge`, `GoldreichLevin.card_filter_agreement_ge`](../CslibFrontier/Crypto/Computational/GoldreichLevin/Nonuniform.lean) prove density at least $\delta/2$ at agreement threshold $1/2+\delta/2$. The draft requires density at least $\delta$ at that threshold. The reverse-averaging argument can yield a sharper bound, but the located declarations state the weaker constant; no new checked strengthening is claimed. |
| 10.16, iterated permutation PRG | 199 / 215 | **Source issue.** The displayed generator has seed length $2n$ and output length $n+N+1$. “$N=n^c$ for any constant $c>0$” fails the chapter's strict-stretch requirement when $0<c<1$ for large $n$. After requiring stretch, [`OneWayPermutation.pseudorandomGenerator`](../CslibFrontier/Crypto/Computational/GoldreichLevin/HardCore.lean) and [`PseudorandomGenerator.amplify`](../CslibFrontier/Crypto/Computational/Stretch.lean) supply a PRG by a different construction; they do not certify the displayed orbit string with its exact ordering/count. |
| 10.17, circuit-secure PRGs derandomize BPP | 201 / 217 | **Endpoint not located.** No endpoint for the stated family of circuit-security assumptions implying $\mathrm{BPP}\subseteq\bigcap_{\epsilon>0}\mathrm{DTIME}(2^{n^\epsilon})$ was located. [`BPP_subset_P_of_isAverageCaseHard`](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization.lean) uses a different hardness hypothesis and NW construction. PRG game security alone is not the native enumeration runtime proof; output stretch, generator evaluation time and hardwired-input circuit size must be tracked. |

### What the existing API establishes

- General OWF-to-PRG and the converse are present. The explicit-security and displayed-construction
  variants above remain separate from that existence equivalence.
- For the unnumbered zero-knowledge application, [`NonuniformOneWay.exists_zkProof_of_mem_NP`](../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean)
  supplies auxiliary-input ZK with negligible soundness for NP. Its hypothesis is nonuniform OWF
  security; it must not be reported as an unconditional ZK theorem or silently weakened to a
  uniform-only OWF hypothesis. Existing development records are
  [#324](https://github.com/cslib-community/cslib-frontier/issues/324),
  [#2316](https://github.com/cslib-community/cslib-frontier/issues/2316), and
  [#643](https://github.com/cslib-community/cslib-frontier/issues/643).
- Issue/PR searches included open and closed records for deterministic interactive proofs,
  program checkers, permanent/Lipton, cycle counting, PSPACE/MA, discrete logarithm,
  Goldreich–Levin, PCP and derandomization. No dedicated owner was located for the proposed
  gaps other than the existing records explicitly linked above. Broad roadmap and audit issues
  are leads, not evidence that an exact endpoint has been assigned. Pinned CSLib and available
  Mathlib source searches did not identify the named missing computational endpoints; this is
  not a whole-library semantic audit. No Lean elaboration or axiom-dependency audit was run.

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

## Exercises establishing new theory

The scope includes exercises whose endpoints develop theory, as clarified by Christian
Reitwiessner; routine practice is not a formalization target. An exercise already implied by
an existing theorem should be mapped to that theorem rather than reproved. Exercise numbers
must be pinned to the source chapter, including subparts; placeholders do not supply a precise
mathematical specification.

The six exercise prompts at the end of Chapter 14 all appear on printed p. 265/PDF p. 281.
Their current dispositions are:

| Exercise | Endpoint and disposition |
|---|---|
| 14 §1 | Finite-field arithmetic versus Boolean circuits up to constant factors. **GF(2) milestone:** [Boolean/Arithmetic.lean](../CslibFrontier/Computability/Circuit/Boolean/Arithmetic.lean) proves same-carrier simulations with size factors three and four, preserving every output. The arbitrary fixed finite-field endpoint remains open; it needs explicit bit representations. |
| 14 §2 | Circuit depth versus exponential-size straight-line programs. **Source specification needed:** the short prompt does not fix the two directions, costs or parameter relation sufficiently for a formal endpoint. |
| 14 §3 | The draft only asks “Bauer-Strassen lemma?” **Source specification needed:** select and cite a precise differentiation theorem before implementation; do not silently repair the name and infer a statement. |
| 14 §4 | Algebraic-machine time to computation-tree depth. **Source issue:** the prompt uses running-time parameter `T` and concludes depth `O(d)` without defining `d`. A corrected endpoint also needs the absent machine/tree model. |
| 14 §5 | Real BSS computation with arbitrary-precision sign tests decides `P/poly`. **Endpoint not located:** specify the real constants, branch operations and binary-language interface before claiming the circuit-family decoding argument. |
| 14 §6 | The draft only asks “Shamir's trick?” **Source specification needed:** no exact algorithm, machine model or bound is given in the exercise. |

This is a first exercise inventory, not a complete classification of every chapter's exercises.
The GF(2) simulations concern values in `Bool`'s Boolean ring, not equality of formal
polynomials. They use existing gate replacement and four-gate XOR synthesis; no new carrier,
compiler-runtime claim or general finite-field completion is implied. Their
[clients](../CslibFrontierTests/BooleanArithmetic.lean) include multiple outputs and zero-cost
wiring. The remaining theoretical exercises stay under
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711).

## Chapter 15: average-case complexity

Snapshot: `b91d5151fd7dc665a5e3efcb466077caf44e690d` (2026-11-12), CSLib pin
`ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`. All four numbered results were checked on PDF pp. 286–296. In this draft Chapter 15 is average-case complexity; proof complexity is in Chapter 21. The current APIs use length-indexed ensembles and native multitape polynomial-time predicates with explicit encodings, rather than silently identifying them with the chapter’s single distribution on all finite words.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 15.7 (average-time reduction closure) | 274 / 290 | **Partial.** `Cslib.Complexity.DistReduction.mem_AvgP` in [Reduction](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Reduction.lean) transfers errorless polynomial-time schemes with unary accuracy parameter, under an explicit polynomial length map and domination. Equivalence with the draft’s moment-based average polynomial time over a single distribution is not supplied. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) explicitly retains that equivalence as remaining work. |
| 15.8 (Levin completeness) | 275 / 291 | **Partial.** `Cslib.Complexity.BoundedHalting.distComplete_problem` in [Completeness](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Completeness.lean) proves the ensemble version of DistNP completeness (landed [#3061](https://github.com/cslib-community/cslib-frontier/pull/3061)). Its padded clock and self-delimiting machine/code header, witness convention and per-length distribution differ from the draft’s $(M,x,1^t,1^\ell)$ and global product distribution. No equivalence of those precise distributional problems was verified; [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) owns the average-case framework. |
| 15.9 (peak elimination) | 275 / 291 | **Partial.** `Cslib.Complexity.Compression.compress_polyTime`, `length_compress_le`, `two_pow_length_compress_mul_le` and `compress_injective` in [Compression](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Compression.lean) prove the bounds for each fixed input length. Injectivity is only within a length, not the global injectivity in the draft. `BoundedHalting.code` adds a framed length prefix for global injectivity, changing the claimed $|g(x)|\le|x|+1$ bound. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) tracks the framework differences. |
| 15.11 (heuristic reduction closure) | 277 / 293 | **Partial.** `Cslib.Complexity.DistReduction.mem_HeurP` in [Reduction](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Reduction.lean) transfers polynomial-time heuristic schemes for length-indexed ensembles and explicit accuracy. The draft instead uses one global distribution, its heuristic definition and a polynomially honest reduction; equivalence of these contracts was not located. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) is the existing framework owner. |


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

Chapters 6–17, 21 and 22 have chapter-specific records above; chapters 1–5 and 18–20
have not yet been catalogued here. These are snapshot-qualified audit records, not proofs of
the remaining theory endpoints or exercises. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
