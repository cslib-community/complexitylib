# Goldreich draft coverage audit

Audit: Christian Reitwiessner, with AI assistance.

This is a growing statement-level audit under [#4772](https://github.com/cslib-community/cslib-frontier/issues/4772),
not a completeness claim for the book or library. Its sources are Oded Goldreich's draft revisions of
*Computational Complexity: A Conceptual Perspective* dated December 2006 to May 2007, from the
[author's drafts page](https://www.wisdom.weizmann.ac.il/~oded/cc-drafts.html). File names and SHA-256
digests are listed in #4772. Numbers and pages belong to those drafts, not the 2008 published edition.

The results registry remains [Entries.lean](../CslibFrontierResults/Entries.lean). A nearby theorem is
not counted as full coverage.

## Chapter 8: Pseudorandom Generators

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main` inspected on
2026-11-12), CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.
This section audits 19 numbered result headings in `r4.pdf` against the glyph-position
extraction, with page-level heading searches and rendered checks of ambiguous statements.
Definitions, constructions, exercises and unnumbered assertions are not additional table rows.
Searches read the relevant PRG, probability, circuit, complexity, interaction and PCP sources,
plus pinned CSLib/Mathlib sources and open/closed issue searches; sibling Arora–Barak audit PRs
[#4764](https://github.com/cslib-community/cslib-frontier/pull/4764),
[#4766](https://github.com/cslib-community/cslib-frontier/pull/4766),
[#4767](https://github.com/cslib-community/cslib-frontier/pull/4767),
[#4768](https://github.com/cslib-community/cslib-frontier/pull/4768),
[#4769](https://github.com/cslib-community/cslib-frontier/pull/4769) and
[#4770](https://github.com/cslib-community/cslib-frontier/pull/4770) were cross-checked for proposals.
Negative results are qualified search findings, not a semantic absence proof. No Lean build,
new client test, whole-library semantic audit or axiom-dependency audit was performed.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 8.3 | `r4.pdf` / 56 / 320 | **Partial.** PRG indistinguishability and efficient postprocessing are present in [PseudorandomGenerator](../CslibFrontier/Crypto/Computational/PseudorandomGenerator.lean). The weighted absolute discrepancy against an efficient finder/tester, with injective randomness length and least-seed/prefix conversion, was not located as a packaged theorem. This does not imply per-input security of a uniform PRG. |
| 8.6 | `r4.pdf` / 61 / 325 | **Covered.** `Cslib.Crypto.ComputationallyIndistinguishable.replicate_bind` in [Sequence](../CslibFrontier/Crypto/Computational/Hybrid/Sequence.lean) gives the multiple-independent-sample direction for strict PPT samplers, an efficiently computed polynomial count and efficient postprocessing. The reverse is first-sample projection for a positive count. Zero samples must be excluded; the draft’s “positive polynomial” convention is needed. |
| 8.8 | `r4.pdf` / 64 / 328 | **Partial.** `Cslib.Crypto.PseudorandomGenerator.amplify` in [Stretch](../CslibFrontier/Crypto/Computational/Stretch.lean) proves iterative one-bit stretch amplification to every efficiently computed strictly larger target. The library construction retains a final seed state plus emitted bits; the draft emits only successive last bits. The exact output-only construction needs its own correspondence or prefix/security argument. Unary target-length computability and pointwise stretch are explicit in Lean. |
| 8.9 | `r4.pdf` / 66 / 330 | **Covered.** `Cslib.Crypto.HardCore.pseudorandomGenerator` in [HardCore](../CslibFrontier/Crypto/Computational/HardCore.lean) appends the predicate to the image. Its explicit length and uniform-image premises follow from the draft’s length-preserving injection on each finite cube. It does not require one-wayness beyond the hard-core premise. |
| 8.10 | `r4.pdf` / 67 / 331 | **Covered.** `Cslib.Crypto.OneWay.exists_pseudorandomGenerator` in [OneWayToPRG](../CslibFrontier/Crypto/Computational/OneWayToPRG.lean) is stronger in allowing general OWFs; compose with `.amplify` above for efficiently computed polynomial stretch. This establishes existence, not identity with the draft’s permutation-orbit construction. |
| 8.11 | `r4.pdf` / 68 / 332 | **Covered.** `Cslib.Crypto.exists_oneWay_iff_exists_pseudorandomGenerator` in [PRGToOneWay](../CslibFrontier/Crypto/Computational/PRGToOneWay.lean) gives the uniform equivalence on `List Bool`, strict PPT and negligible distinguishing/inversion probability. A one-bit generator need not itself be one-way: the reverse theorem first amplifies it. |
| 8.13 | `r4.pdf` / 70 / 334 | **Endpoint not located.** Circuit-secure polynomial-stretch PRGs imply $BPP\subseteq\bigcap_{\epsilon>0}DTIME(2^{n^\epsilon})$. The NW theorem uses a different hardness premise. This is already proposed in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769) (Arora–Barak 10.17); do not duplicate that proposal. |
| 8.15 | `r4.pdf` / 75 / 339 | **Partial.** Seed enumeration and a native polynomial-time NW simulation exist in [Derandomization](../CslibFrontier/Computability/Complexity/Classes/BPP/Derandomization.lean). No arbitrary time-constructible $t$, inverse-stretch and $\operatorname{poly}(2^{\ell^{-1}(t(n))}t(n))$ simulation interface was located. |
| 8.16 | `r4.pdf` / 75 / 339 | **Partial.** The same native derandomization machinery proves the NW instantiation, but the implication from an arbitrary exponentially stretching canonical derandomizer to $BPP=P$ was not located separately. Generator evaluation must be charged in exponential seed time; a finite security predicate alone is insufficient. |
| 8.18 | `r4.pdf` / 77 / 341 | **Partial.** `Cslib.Crypto.PRG.NisanWigderson.exists_complexity_le_half_add_div_le_card_eq` in [Circuit](../CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/Circuit.lean) supplies finite reconstruction. It bounds reconstructed De Morgan complexity by test complexity plus $m(2^a(2a+3)+1)+1$, with advantage divided by output length $m$. The source’s arbitrary exponential-time design/function family and constants $\epsilon>2\alpha/\beta+\gamma$ are not this exact packaged endpoint. |
| 8.19 (both parts) | `r4.pdf` / 78 / 342 | **Partial.** Part 1 is `Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity` in [WorstCaseHardness](../CslibFrontier/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean): a bit language in `E encBits`, eventual exponential De Morgan circuit lower bound, and conclusion for every explicit encoding. Part 2’s $\forall$ polynomial $p$, $\exists L\in E$ eventual lower bound and subexponential simulation were not located. Part 1 alone does not cover the two-part result. |
| 8.21 | `r4.pdf` / 86 / 350 | **Partial.** `Cslib.Crypto.PRG.Nisan.secure_bitGenerator_of_le` and `card_bitSeed` in [Bits](../CslibFrontier/Crypto/Primitives/PRG/Nisan/Bits.lean) prove read-once width-$2^a$ security $2^{-d}$ with seed length $n+k(3n-1)$, $n=2(k+a+d)$, and output $2^kn$. Missing: the quantified space-constructible-family theorem and its linear seed-space/output-time realization. Historical finite-security milestone: [#3187](https://github.com/cslib-community/cslib-frontier/issues/3187), [#474](https://github.com/cslib-community/cslib-frontier/issues/474) (closed, proof route dropped; not an active implementation queue). |
| 8.22 | `r4.pdf` / 86 / 350 | **Endpoint not located.** Nisan–Zuckerman polynomial stretch with linear space and exponentially small distinguishing error, including linear-space/polynomial-time generation. Nisan’s seed proportional to space times log output is a different tradeoff. Consult extractor track [#895](https://github.com/cslib-community/cslib-frontier/issues/895); no dedicated endpoint owner located. |
| 8.23 | `r4.pdf` / 90 / 354 | **Partial.** `Cslib.Complexity.BPL_subset_P` in [PolyTime](../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PolyTime.lean) supplies deterministic polynomial time, not simultaneous polylogarithmic space. No $BPL\subseteq SC$ endpoint located in the randomized-space modules. [#474](https://github.com/cslib-community/cslib-frontier/issues/474) is closed as not planned; its stronger route was dropped. [#1444](https://github.com/cslib-community/cslib-frontier/issues/1444) owns classical RL quadratic-space work, not this simultaneous BPL time/space theorem. No active dedicated BPL/SC owner was located. |
| 8.24 | `r4.pdf` / 94 / 358 | **Covered.** `Cslib.Probability.isKWiseIndependentHash_polynomialHash` in [Polynomial](../CslibFrontier/Probability/KWiseIndependent/Polynomial.lean) proves the stated degree-less-than-$t$ polynomial family over any finite field at distinct points. Uniform coefficient tuples correspond to the seed blocks after choosing a $GF(2^b)$ bit equivalence. The proposition itself does not certify efficient construction of that field representation. |
| 8.25 | `r4.pdf` / 95 / 359 | **Covered.** `Cslib.BitString.isPairwiseIndependentHash_toeplitzHash_bool` in [ToeplitzHash](../CslibFrontier/Probability/BitString/ToeplitzHash.lean) gives the exact affine Toeplitz family: $b\times m$ matrix, $b+m-1$ matrix bits and $b$ independent offset bits. Evaluate at the chosen distinct $m$-bit labels. This is a distribution theorem, not a native runtime claim. |
| 8.26 | `r4.pdf` / 97 / 361 | **Partial.** `Cslib.BitString.exists_isSmallBias_uniformOfFintype_map` in [Powering](../CslibFrontier/Probability/SmallBias/Powering.lean) gives $2m$ seed bits, $n$ output bits and bias $(n-1)/2^m$; this gives the mathematical exponential seed/bias tradeoff. The finite-field/bit equivalence is existential; no uniform output-polynomial-time generator for the stated family was located. |
| 8.28 | `r4.pdf` / 101 / 365 | **Covered.** `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le` in [Hitting](../CslibFrontier/Foundations/Combinatorics/Expander/Hitting.lean) gives $\rho(\rho+\lambda_{norm}(1-\rho))^{\ell-1}$ with a uniform initial vertex and $\ell-1$ steps, even for varying sets. The source adjacency bound is normalized by $\lambda_{norm}=\lambda/d$. Use the rotation-map representation of the regular undirected graph; nonzero degree and nonempty vertex set are explicit. |
| 8.29 | `r4.pdf` / 102 / 366 | **Partial.** `Cslib.RotationMap.dens_filter_forall_walkAt_notMem_le` in the preceding module proves the required miss-probability estimate (retaining an initial-density factor), conditional on a supplied rotation map. The claimed explicit binary-label expander family and uniform generator runtime/seed layout remain separate. Strong explicitness is already proposed in [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768), Arora–Barak 16.31–16.32. |

## Chapter 9: Probabilistic Proof Systems

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main` inspected on
2026-11-12), CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.
This section audits 14 numbered result headings in `r5.pdf` against the glyph-position
extraction, with page-level heading searches and rendered checks of ambiguous statements.
Definitions, constructions, exercises and unnumbered assertions are not additional table rows.
Searches read the relevant PRG, probability, circuit, complexity, interaction and PCP sources,
plus pinned CSLib/Mathlib sources and open/closed issue searches; sibling Arora–Barak audit PRs
[#4764](https://github.com/cslib-community/cslib-frontier/pull/4764),
[#4766](https://github.com/cslib-community/cslib-frontier/pull/4766),
[#4767](https://github.com/cslib-community/cslib-frontier/pull/4767),
[#4768](https://github.com/cslib-community/cslib-frontier/pull/4768),
[#4769](https://github.com/cslib-community/cslib-frontier/pull/4769) and
[#4770](https://github.com/cslib-community/cslib-frontier/pull/4770) were cross-checked for proposals.
Negative results are qualified search findings, not a semantic absence proof. No Lean build,
new client test, whole-library semantic audit or axiom-dependency audit was performed.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 9.2 | `r5.pdf` / 9 / 391 | **Endpoint not located.** Perfect soundness implies NP by fixing verifier coins and checking a bounded transcript; the draft assumes perfect completeness. No zero-soundness class bridge located. Coordinate with the deterministic-interaction/transcript proposal in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769), Arora–Barak 8.3. |
| 9.4 | `r5.pdf` / 12 / 394 | **Covered.** `Cslib.Complexity.IP_eq_PSPACE` in [Shamir](../CslibFrontier/Computability/Complexity/Classes/IP/Shamir.lean) gives native equality for every explicit instance encoding. The IP model uses a strict oracle-PPT private-coin verifier and arbitrary randomized stateful provers, with completeness $2/3$ and soundness $1/3$; the lower-bound construction has perfect completeness. The draft’s perfect-completeness presentation requires this convention to be kept visible. |
| 9.5 | `r5.pdf` / 17 / 399 | **Partial.** `optimalProver` and exact acceptance maximization underlie `IP_subset_PSPACE` in [PSPACE](../CslibFrontier/Computability/Complexity/Classes/IP/PSPACE.lean); `Cslib.Complexity.Interaction.computableInPolySpace_evaluate` certifies the optimal value computation. A polynomial-space next-message strategy realizing that value, for every partial transcript, was not located as a certified strategy theorem. Computing the value alone is not the stated endpoint. |
| 9.11 | `r5.pdf` / 33 / 415 | **Covered.** `Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_npRelation` in [ZeroKnowledge](../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean) gives relation-preserving witnesses, a PPT honest prover, general auxiliary-input ZK and negligible soundness against unbounded stateful provers. The library uses explicit encodings and a separate security parameter; its clock bridges expose instance-indexed/unbounded-auxiliary formulations. This is the landed [#2316](https://github.com/cslib-community/cslib-frontier/issues/2316) endpoint, not merely the older generable-family ZK theorem. |
| 9.12 | `r5.pdf` / 33 / 415 | **Partial.** The NP case above and private/public-coin interactive proof machinery exist, but a compiler giving computational zero knowledge for every IP language under nonuniform OWFs was not located. NP zero knowledge alone does not imply $IP=ZK$. Consult protocol architecture [#643](https://github.com/cslib-community/cslib-frontier/issues/643); its stated IOP/Ligero program does not itself claim this equality. |
| 9.13 | `r5.pdf` / 36 / 418 | **Partial.** The GMW NP-relation proof uses the relation’s own witness and is zero knowledge, but that does not establish extraction from an arbitrary successful prover. Sigma-protocol special soundness and ROM knowledge theorems concern other models. No general OWF-to-ZK proof-of-knowledge compiler for every NP relation was located; coordinate knowledge abstractions with [#643](https://github.com/cslib-community/cslib-frontier/issues/643). |
| 9.15 | `r5.pdf` / 39 / 421 | **Partial.** `Cslib.Complexity.PCP_log_subset_NP` in [NP](../CslibFrontier/Computability/Complexity/Classes/PCP/NP.lean) proves the logarithmic-randomness specialization, via enumeration of all queried addresses and a consistent answer table. The arbitrary polynomially bounded $r$ theorem with nondeterministic time $2^r\operatorname{poly}(n)$ was not located; the library’s verifiers are nonadaptive. |
| 9.16 | `r5.pdf` / 40 / 422 | **Covered.** `Cslib.Complexity.NP_subset_PCP_log` in [Completeness](../CslibFrontier/Computability/PCP/Completeness.lean) proves logarithmic randomness and constant nonadaptive bit queries, perfect completeness and soundness at most $1/2$, with native polynomial-time verification. `PCP` bounds include multiplicative constants; the query argument `fun _ => 1` means $O(1)$, not one bit. The subsequent unnumbered efficient witness-to-oracle strengthening is not claimed by this class-containment theorem. |
| 9.17 | `r5.pdf` / 40 / 422 | **Covered.** `Cslib.Complexity.NP_eq_PCP_log` in the preceding module combines the two containments for every explicit encoding; same randomness, query and completeness/soundness conventions as 9.16. |
| 9.19 | `r5.pdf` / 51 / 433 | **Partial.** [GapTheorem](../CslibFrontier/Computability/PCP/GapTheorem.lean) has `Cslib.PCP.Dinur.min_le_unsatVal_round`, and [GapTheorem](../CslibFrontier/Computability/PCP/Encoded/GapTheorem.lean) supplies native `isPolyTime_gapGraph` and a final constant gap. The source asks for a single fixed-alphabet, linear-size, polynomial-time self-reduction with $\operatorname{vlt}(f(G))\ge\min(2\operatorname{vlt}(G),c)$. The exact factor-two single-round bridge was not located; a final PCP theorem does not prove this auxiliary contract. |
| 9.21 | `r5.pdf` / 55 / 437 | **Partial.** The PCP theorem and `GapThreeSAT_npHard` in [MaxThreeSAT](../CslibFrontier/Computability/PCP/Approximation/MaxThreeSAT.lean) give the main endpoints. No packaged equivalence with the source’s general bounded-arity `gapGSAT` and its specific $1/2$ gap was located. Arbitrary-verifier-to-constraint translation and exact promise conventions remain to be matched; merely having all nearby hardness theorems is not that interface. |
| 9.22 | `r5.pdf` / 57 / 439 | **Endpoint not located.** The randomness/query tradeoff $PCP(\ell-k,O(2^k))$ obtained by enumerating a random-tape prefix was not located. A uniform implementation needs an effective prefix length (or an explicit convention on resource functions); the draft quantifies over arbitrary integer functions. This is not supplied by zero-randomness NP membership alone. |
| 9.23 | `r5.pdf` / 59 / 441 | **Partial.** The native PCP theorem proves polynomial verification time. No verifier with degree fixed at two for every NP language, together with a native polynomial-time map from its own NP witnesses to accepting proof oracles, was located. The source’s quadratic-time endpoint is stronger than generic polynomial-time Cook–Levin followed by the current gap-graph verifier. |
| 9.24 | `r5.pdf` / 60 / 442 | **Endpoint not located.** General $NTIME(t)\subseteq PCP(O(\log t),O(1))$ for $n<t(n)<2^{\operatorname{poly}(n)}$ was not located. This needs succinct/local computation of the large proof representation, with explicit effectiveness and verifier-time conventions for $t$. The NP theorem does not scale merely by substituting a function; coordinate the NEXP case with [#892](https://github.com/cslib-community/cslib-frontier/issues/892) and [#3609](https://github.com/cslib-community/cslib-frontier/pull/3609). |

### What the existing proof-system API establishes

`IP_eq_PSPACE` is a native machine-class theorem, rather than an equality between classes
whose verifier efficiency is supplied as an external assumption. `NP_eq_PCP_log` similarly
uses the encoded gap-graph pipeline and a native polynomial-time nonadaptive verifier.
The noncomputable `Cslib.PCP.Dinur.round` separately has the exact factor-two combinatorial
bound and linear cardinality bounds; this must not be mistaken for the encoded single-round
runtime theorem in 9.19. Conversely, that remaining bridge does not invalidate the already
proved class-level PCP theorem.

For zero knowledge, use the nonuniform OWF endpoint, not just
`OneWay.exists_zeroKnowledgeProof_of_npRelation`: the latter's generable-family guarantee
is narrower. The full endpoint has a separate security parameter and polynomially bounded
families; the instance/auxiliary-input clock bridges are part of its interpretation.
Neither a witness-preserving honest prover nor soundness against arbitrary provers constitutes
a proof-of-knowledge extractor.

The chapter tables contain 33 rows (19 in chapter 8, 14 in chapter 9), counting the two parts
of 8.19 together. No additional numbered proof-internal claims were identified in the heading
search. Rendered checks included r4 PDF pages 77 and 101 and r5 pages 59–60; they confirm the
NW constants, normalized expander bound, quadratic verification-time assertion and the stated
range of the generalized PCP theorem. The source hashes agree with #4772:
`r4.pdf`: `a98294d7e07c21f9d9f831d0cb30c3d796c87c0740fa6a76da15088a900a3193`;
`r5.pdf`: `67616fb473bfdbf3c98979819f6cfaba79a2d19155f2701b7fa7c48c88b07502`.
The chapter-7 overlap of r3/r4 is outside these sections; chapter 8 uses r4 throughout.
No source-error row is asserted: effectiveness/rounding/positive-sample conventions needing
clarification are recorded as qualifications, without claiming a refutation of the intended
mathematics. Suitable follow-up checked clients would specialize the polynomial/Toeplitz
hash theorems at distinct points and the sharp hitting bound at zero walk steps and the empty
or full target; none was added or run in this audit.
