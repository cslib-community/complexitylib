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

Chapters 8–10 and 14 have chapter-specific records above; the remaining chapters have not
yet been catalogued here. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
