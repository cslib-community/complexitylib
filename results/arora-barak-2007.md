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

## Chapter 1: the computational model

Snapshot for chapters 1–5: `b91d5151fd7dc665a5e3efcb466077caf44e690d` on 2026-11-12,
with CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.
The six result headings in Chapter 1 were checked in the PDF, including its appendix;
references to earlier results in exercises are not additional results.
The same PDF heading scan for chapters 2–5 found respectively 13, 6, 8 and 8 results
(41 total across these five chapters). The scan checked the small-cap heading style and
surrounding text; Figure 2.4's theorem labels are cross-references, not extra headings.
Printed pages are PDF pages minus 16 throughout this range.

The correspondence used below is the native finite-state multitape model, with explicit
encodings `α ↪ List Bool`, a read-only input, write-only output, and work-tape space counted
separately from input length. The library's bidirectional work tapes and its output convention are not the
draft's one-way tapes with a separate output tape. Class-level results are reported in this
native model; the precise constant-cost model conversions in 1.8, 1.9 and 1.11 are not assumed.
Resource classes absorb multiplicative and additive constants. Source inspection, not a fresh
Lean build or a whole-library proof/dependency audit, supplies this record. Searches checked the
named modules and neighboring APIs on this snapshot, pinned CSLib, and open and closed GitHub
issues/PRs. An endpoint not located is a qualified search result, not a proof of absence under
all possible equivalent formulations. Declaration names below are in `Cslib.Complexity` unless
qualified otherwise.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 1.8, alphabet reduction | 19 / 35 | **Endpoint not located.** The machine and encoding APIs permit finite alphabets, but no inspected compiler establishes the draft's same-tape-count simulation over $\{0,1,\square,\triangleright\}$ within $4\lceil\log |\Gamma|\rceil T$ steps. Starting complexity classes with binary machines does not prove alphabet invariance. |
| 1.9, single work tape | 20 / 36 | **Endpoint not located.** No inspected multitape/single-tape bridge certifies one work tape plus separate input/output and the bound $5kT^2$. Single-tape crossing-sequence results concern a different input/output model. [#800](https://github.com/cslib-community/cslib-frontier/issues/800) owns universal-simulation improvements; [#798](https://github.com/cslib-community/cslib-frontier/issues/798) is a Kolmogorov consumer, not this endpoint. |
| 1.11, folding bidirectional tapes | 21 / 37 | **Endpoint not located.** Native tapes are already bidirectional. No conversion to the draft's one-way model with time $4T$ was located in the machine, tape or encoding modules. |
| 1.13, efficient universal TM | 24 / 40 | **Partial.** `Turing.MultiTapeTM.Universal.computableInO_universal_nlogn` in [WindowedComplexity.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Universal/WindowedComplexity.lean) certifies a clocked interpreter, with time and space $O(N+(D+M+2)^6(t+1)(\log_2(t+1)+1))$: $N$ is the encoded triple length, $D$ the description length and $M$ the largest input symbol. For fixed binary machines this gives the intended clocked near-linear simulation. It does not itself supply the unclocked partial universal machine or the draft's exact tape conventions; [#800](https://github.com/cslib-community/cslib-frontier/issues/800) retains that work. |
| 1.16, an uncomputable Boolean function | 25 / 41 | **Covered in the native model.** `Turing.MultiTapeTM.not_isDecidable_selfAcceptanceProblem` in [Halting.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting.lean) proves undecidability of self-acceptance of encoded native descriptions. Complementing its indicator gives the draft's diagonal Boolean function; no claim is made that the description encodings coincide. |
| 1.17, HALT undecidable | 25 / 41 | **Covered in the native model.** `Turing.MultiTapeTM.not_isDecidable_haltingProblem` in [Halting.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting.lean), with input encoding `encPair encBits encBits`, is the two-input native halting endpoint. |

### What the existing API establishes

- The clocked near-linear interpreter is a certified computation, not merely a recursive
  simulation function. Fixing the description and alphabet makes their overhead constant;
  letting descriptions grow with input length does not, which matters for Chapter 3.
- The native undecidability results quantify over all finite-state machines and arbitrary
  time/space bounds. They do not supply the quantitative model conversions in the first three rows.

## Chapter 2: NP and NP-completeness

Snapshot and model conventions are those recorded in Chapter 1. All 13 numbered result
headings were checked in the PDF. The library's `NP` uses fixed polynomial certificate lengths
and a native polynomial-time verifier on `encPair enc encBits`; its reductions carry both
encodings explicitly. CNFs use natural-number variable names and the named `encCNF` encoding.
The original source's formula-size measure is not automatically encoded bit length.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 2.3, $P\subseteq NP\subseteq EXP$ | 41 / 57 | **Covered.** `P_subset_NP` in [Reduction.lean](../CslibFrontier/Computability/Complexity/Reduction.lean) and `NP_subset_EXP` in [Inclusions.lean](../CslibFrontier/Computability/Complexity/Classes/Inclusions.lean). `EXP` is the union of native $DTIME(2^{n^k})$; enlarging an exponent absorbs the draft's union over $c>1$ and constants. |
| 2.6, verifier/NTM characterization | 42 / 58 | **Covered.** `mem_NP_iff_exists_mem_NTIME` in [Time.lean](../CslibFrontier/Computability/Complexity/Classes/Time.lean) gives $A\in NP\;enc\iff\exists k, A\in NTIME\;enc\;(n\mapsto n^k)$. The nondeterministic machines are native binary multitape machines, with all-branch time bounds. |
| 2.8, reductions and completeness | 44 / 60 | **Covered.** `PolyTimeReducible.trans`, `NPComplete.P_eq_NP_of_mem_P` and `NPComplete.mem_P_iff` in [Reduction.lean](../CslibFrontier/Computability/Complexity/Reduction.lean). The NP-hard case follows from the same reduction-closure proof, without using membership in NP; the library expresses collapse uniformly over instance encodings. |
| 2.9, TMSAT NP-complete | 44 / 60 | **Endpoint not located.** Searches for TMSAT and bounded acceptance did not locate NP-completeness for the four-part instance $(\alpha,x,1^n,1^t)$ with an existential $n$-bit witness. [BoundedHalting.lean](../CslibFrontier/Computability/Complexity/Problems/BoundedHalting.lean) instead uses a binary clock and deterministic acceptance and proves EXP-completeness. These are different endpoints. |
| 2.10, Cook–Levin | 45 / 61 | **Covered.** `CookLevin.SAT_npComplete` in [Completeness.lean](../CslibFrontier/Computability/Complexity/CookLevin/Completeness.lean) and `ThreeSAT_npComplete` in [ThreeSAT.lean](../CslibFrontier/Computability/Complexity/Problems/ThreeSAT.lean). The reductions are native polynomial-time, with `encCNF`; the three-CNF representation allows clauses of length at most three. No quasi-linear size/time bound follows. |
| 2.12, SAT NP-hard | 46 / 62 | **Covered.** `CookLevin.SAT_npHard` in [Completeness.lean](../CslibFrontier/Computability/Complexity/CookLevin/Completeness.lean), through a constructed native verifier tableau reduction. This auxiliary lemma is separately formalized. |
| 2.14, CNF for every Boolean function | 46 / 62 | **Endpoint not located.** Inspected propositional CNF and Cook–Levin clause APIs did not locate the general $\ell$-variable truth-table CNF with at most $\ell2^\ell$ AND/OR symbols. The proof says “at most”; the heading's wording “size $\ell2^\ell$” should be read as a bound. A tableau encoding of computations is not this size theorem. |
| 2.15, SAT reduces to 3SAT | 49 / 65 | **Covered.** `polyTimeReducible_SAT_ThreeSAT` in [ThreeSAT.lean](../CslibFrontier/Computability/Complexity/Problems/ThreeSAT.lean), with correctness `mem_ThreeSAT_toThreeSAT_iff` and polynomial-time construction. Fresh variables encode the long-clause splitting; satisfiability, rather than pointwise equality of assignments, is preserved. |
| 2.16, independent set NP-complete | 50 / 66 | **Covered.** `IndependentSet_npComplete` in [IndependentSet.lean](../CslibFrontier/Computability/Complexity/Problems/IndependentSet.lean). Finite listed graphs and binary threshold use `encPair encGraph encNat`; the predicate asks for an independent subset of cardinality at least the threshold, equivalent to existence of one of exactly that size by taking a subset. The reduction uses literal occurrences rather than the draft's seven assignments per clause. |
| 2.17, integer programming NP-complete | 52 / 68 | **Partial.** `ZeroOneIP_npComplete` in [IntegerProgramming.lean](../CslibFrontier/Computability/Complexity/Problems/IntegerProgramming.lean) covers natural-coefficient equalities with Boolean unknowns, encoded by `encZeroOneIP`. The draft permits rational inequalities and arbitrary nonnegative integer unknowns. General membership needs a polynomial-bit witness bound, not just a Boolean verifier. [#2904](https://github.com/cslib-community/cslib-frontier/issues/2904) catalogs Karp's 0–1 problem; [#2976](https://github.com/cslib-community/cslib-frontier/issues/2976) concerns rational LP, not integer feasibility. |
| 2.18, directed Hamiltonian path NP-complete | 52 / 68 | **Partial.** `DirHamPath_npComplete` in [Directed.lean](../CslibFrontier/Computability/Complexity/Problems/Hamiltonian/Directed.lean) proves completeness with designated start/end vertices (`encPathInstance`); the draft asks whether the graph has any Hamiltonian path. `DirHamCycle_npComplete` covers cycles. An explicit polynomial-time bridge to the unrestricted-endpoint path language, including empty-graph conventions, was not located. |
| 2.19, search from $P=NP$ | 55 / 71 | **Covered.** `FNP_subset_FPSearch_of_NP_subset_P` and `FNP_subset_FPSearch_iff_SAT_mem_P` in [SearchToDecision.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP/SearchToDecision.lean) produce an optional polynomial-time solution of any polynomially balanced, polynomial-time decidable witness relation. Apply to the original verifier and its exact-length certificate condition to retain that verifier's witnesses, rather than just some SAT assignment. The hypothesis is on the paired encoding (or uniformly all encodings). |
| 2.25, $EXP\ne NEXP\Rightarrow P\ne NP$ | 57 / 73 | **Covered.** `EXP_eq_NEXP_of_P_eq_NP` in [Padding.lean](../CslibFrontier/Computability/Complexity/Classes/Padding.lean) is the contrapositive, with `P encBits = NP encBits` implying equality for every target encoding. Native costs of writing exponential unary padding are included. |

### What the existing API establishes

- Cook–Levin, three-SAT, independent set, and designated-endpoint Hamiltonian path have
  unconditional polynomial-time completeness results. They are not merely abstract reductions
  with an assumed efficient implementation.
- The zero-one integer-programming theorem does not prove the draft's general integer-programming
  NP membership. The draft's “clearly in NP” suppresses the small-solution theorem needed there.
- [#4225](https://github.com/cslib-community/cslib-frontier/issues/4225) owns the small-formula
  Cook–Levin strengthening and records later local-computability/generation milestones needed
  by fine-grained consumers; current polynomial completeness
  does not settle the SAT time–space claim in Chapter 5.

## Chapter 3: diagonalization and hierarchies

Snapshot and native-model conventions are those recorded in Chapter 1. All six numbered
results were checked in the PDF. Constructibility in the library is an explicit computational
predicate, not an assumed textbook clock: time constructibility computes a binary value within
$O(f(n))$, while space constructibility supplies the space-bounded clock construction.
The draft's admissibility lower bounds must remain visible when comparing these predicates.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 3.1, deterministic time hierarchy | 66 / 82 | **Partial.** `exists_DTIME_ssubset_DTIME_polylog` in [TimePolylog.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/TimePolylog.lean) proves separation for a sufficiently large fixed polylogarithmic gap, assuming $n\le f(n)$. It does not give every $f\log f=o(g)$ gap. [#4211](https://github.com/cslib-community/cslib-frontier/issues/4211) owns that precise strengthening under [#1572](https://github.com/cslib-community/cslib-frontier/issues/1572) and [#800](https://github.com/cslib-community/cslib-frontier/issues/800). Near-linear simulation of each fixed machine alone does not remove the description-size overhead in the diagonal. |
| 3.2, deterministic space hierarchy | 66 / 82 | **Covered in the native model.** `DSPACE_ssubset_DSPACE` in [Space.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/Space.lean) assumes space-constructible $g$, pointwise $\log_2 n\le g(n)$, and $\forall c,\forall^\infty n,\;cf(n)+c\le g(n)$. The latter is the natural-valued domination form of the admissible $f=o(g)$ gap. Constructibility of $f$ is not needed. The logarithmic-space extension sought in [#4090](https://github.com/cslib-community/cslib-frontier/issues/4090) is present at this snapshot; that issue also tracks nondeterministic space. |
| 3.3, nondeterministic time hierarchy | 67 / 83 | **Partial.** `NTIME_pow_ssubset_NTIME_pow` in [NondeterministicPolynomial.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/NondeterministicPolynomial.lean) separates integer polynomial degrees $1\le a<b$. It is not the general $f(n+1)=o(g(n))$ endpoint or the draft's fractional-power example. [#4213](https://github.com/cslib-community/cslib-frontier/issues/4213) owns the sharp hierarchy and its transcript-checker prerequisites. |
| 3.4, Ladner | 68 / 84 | **Covered.** `Ladner.exists_NP_not_P_not_npComplete` in [Ladner.lean](../CslibFrontier/Computability/Complexity/Classes/Ladner.lean) produces a bit-string language in NP, outside P and not NP-complete, assuming $P\;enc\ne NP\;enc$ for an instance encoding. Native costs of the delayed-diagonal padding construction are proved. |
| 3.8, oracle query and polynomial oracle lowness | 70 / 86 | **Covered.** `mem_PWithOracle_compl_self` in [Lowness.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/Lowness.lean) specializes to encoded UNSAT with encoded SAT oracle. `PWithOracle_eq_P` in [PolyTime.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/PolyTime.lean) handles every bit-language oracle in P. The oracle model charges for native query construction and treats the reply as one oracle operation. |
| 3.9, Baker–Gill–Solovay | 71 / 87 | **Covered.** `baker_gill_solovay` in [Collapse.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/Collapse.lean) supplies both oracles. The equality oracle is encoded TQBF (PSPACE-complete), rather than the proof sketch's EXPCOM. The separation uses a native oracle diagonal and the unary length language, as in the draft. |

### What the existing API establishes

- The space hierarchy reaches logarithmic space; the general sharp time hierarchies remain
  distinct objectives. Integer polynomial time separation does not establish fractional or
  arbitrary constructible gaps.
- The relativization endpoints use actual oracle-computation predicates. No identification of
  arbitrary oracle access with an ordinary computable function is assumed.

## Chapter 4: space complexity

Snapshot and model conventions are those recorded in Chapter 1. All eight numbered results
were checked in the PDF. In 4.18 the PDF's bar means the **complement** of PATH; text extraction
loses it. Configurations include the read-only input-head position, so a general configuration
count contains a factor depending on input length; the usual $s\ge\log n$ lower bound absorbs it.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 4.3, time/space inclusions | 76 / 92 | **Covered in the native model.** `DTIME_subset_DSPACE` in [Space/Time.lean](../CslibFrontier/Computability/Complexity/Classes/Space/Time.lean), `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_decidesInSpace` in [Nondeterministic.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/Nondeterministic.lean) (the deterministic-to-nondeterministic inclusion, not a separately named class lemma), and `exists_mem_DTIME_of_mem_NSPACE_of_log2_le` in [DeterministicTime.lean](../CslibFrontier/Computability/Complexity/Classes/Space/Nondeterministic/DeterministicTime.lean) give the full chain for pointwise $\log_2 n\le s(n)$. The exponential-time constant depends on the machine. Constructibility is not needed for this upper bound. |
| 4.4, configuration count and local CNF | 77 / 93 | **Partial.** The native configuration graph and `vertexID_lt_pow_of_runsInSpace` / `length_vertexID_le_of_runsInSpace` in [Bounds.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/ConfigurationGraph/Bounds.lean) explicitly bound logspace configuration codes. General space-to-time counting also underlies 4.3. The draft additionally requires a CNF of size $O(S(n))$ expressing a **single edge** for arbitrary admissible $S$. TQBF's polynomial-time edge-test tableau does not certify that linear-size CNF; this auxiliary endpoint was not located separately. |
| 4.11, TQBF PSPACE-complete | 81 / 97 | **Partial (syntax bridge).** `TQBF_pspaceComplete` in [Space/TQBF.lean](../CslibFrontier/Computability/Complexity/Classes/Space/TQBF.lean). The language is true **closed** QBFs under token encoding `encQBF`, with general QBF syntax. The draft explicitly restricts to prenex formulas (p. 80 / PDF 96, footnote 1), without requiring a CNF matrix. The reduction produces closed formulas and the evaluator is a native polynomial-space computation; a checked polynomial-time prenex normalization/encoding bridge was not located in this pass. |
| 4.12, Savitch | 82 / 98 | **Covered.** `NSPACE_subset_DSPACE_sq` in [Savitch.lean](../CslibFrontier/Computability/Complexity/Classes/Space/Nondeterministic/Savitch.lean) assumes $\forall n,\log_2 n\le s(n)$ and proves $NSPACE(s)\subseteq DSPACE(s^2)$. It drops constructibility, and `mem_DSPACE_sq_of_recognizesInSpace` even admits nonhalting recognition branches. It establishes workspace, not a simultaneous fast running-time bound. |
| 4.15, logspace reduction composition | 84 / 100 | **Covered.** `LogSpaceReducible.trans` and `LogSpaceReducible.mem_L` in [LogSpace.lean](../CslibFrontier/Computability/Complexity/Classes/LogSpace.lean). The library uses native logspace functions with explicit input/output encodings and recomputation for composition; it does not store a polynomial-size intermediate output in logarithmic work space. |
| 4.16, PATH NL-complete | 85 / 101 | **Covered.** `STCON.logSpaceComplete` in [Completeness.lean](../CslibFrontier/Computability/Complexity/Problems/STCON/Completeness.lean). Instances have a positive vertex count, designated vertices and a Boolean adjacency matrix, encoded with unary size/endpoints and matrix bits by `encSTCON`. Reachability allows a zero-step path, so $s=t$ accepts. These conventions exclude malformed/zero-vertex encodings. |
| 4.18, complement of PATH in NL | 87 / 103 | **Covered.** `STCON.compl_mem_NL` in [Completeness.lean](../CslibFrontier/Computability/Complexity/Problems/STCON/Completeness.lean). The complement is within the well-formed `STCONInstance` domain and uses the same encoding as 4.16. Native inductive counting supplies complementation, not an unbounded external certificate checker. |
| 4.19, NSPACE closed under complement | 88 / 104 | **Covered.** `NSPACE_eq_coNSPACE` in [Nondeterministic.lean](../CslibFrontier/Computability/Complexity/Classes/Space/Nondeterministic.lean), for pointwise $\log_2 n\le s(n)$, without constructibility. This includes the draft's constructible $S>\log n$ regime, with the usual finite-length/rounding adjustments to natural bounds. |

### What the existing API establishes

- General Savitch and nondeterministic-space complementation are stronger than just the
  polynomial-space or NL corollaries. Their hypotheses and native workspace conventions are explicit.
- General-syntax TQBF completeness and PATH completeness have certified native reductions. Neither theorem
  by itself proves every formula-size assertion about configurations used in the draft's proofs.

## Chapter 5: the polynomial hierarchy and alternations

Snapshot and model conventions are those recorded in Chapter 1. All eight numbered headings
were checked in the PDF, including Claims 5.14.1 and 5.14.2. `SigmaP`/`PiP` use bounded
alternating verifier blocks; `AP` is machine-based. The separate `SigmaTwoTIME` API is a
linear-time verifier with existential/universal certificates above a time-dependent length
threshold. Its quantitative results must not be silently identified with an arbitrary
bounded-alternation ATM characterization. Fractional powers in this chapter require explicit
natural-valued rounding when turned into Lean resource functions.

| Draft result | Printed / PDF page | Disposition and remaining endpoint |
|---|---|---|
| 5.6, PH collapse | 93 / 109 | **Partial (encoding quantifier).** `PH_eq_SigmaP_of_PiP_subset_SigmaP` and `PH_eq_P_of_NP_subset_P` in [Collapse.lean](../CslibFrontier/Computability/Complexity/Classes/PH/Collapse.lean) prove the collapse uniformly assuming the relevant inclusion for **every instance encoding**. The draft assumes equality of bit-language classes. A checked transfer of that single bit-language hypothesis to the library's universal encoding hypothesis was not located here; the underlying collapse argument is present. |
| 5.7, PH-completeness forces collapse | 94 / 110 | **Partial; not separately formalized.** `mem_PH` in [PH.lean](../CslibFrontier/Computability/Complexity/Classes/PH.lean) locates the complete language at a finite level; `PolyTimeReducible.mem_SigmaP` in [Reduction.lean](../CslibFrontier/Computability/Complexity/Classes/PH/Reduction.lean) pulls all PH languages back to that level. These supply the short proof under compatible encodings, but no named PH-completeness/collapse endpoint was located. |
| 5.11, bounded alternation characterization | 96 / 112 | **Partial.** [PH.lean](../CslibFrontier/Computability/Complexity/Classes/PH.lean) defines the bounded-quantifier levels, and [Alternation.lean](../CslibFrontier/Computability/Complexity/Classes/Alternation.lean) defines native `ATIME`. No general bridge equating each fixed level with polynomial-time ATMs having that bounded number of alternations was located. [#4086](https://github.com/cslib-community/cslib-frontier/issues/4086) owns parametric alternating-resource simulations, not explicitly this level-by-level characterization. |
| 5.12, AP = PSPACE | 96 / 112 | **Covered.** `AP_eq_PSPACE` in [Savitch.lean](../CslibFrontier/Computability/Complexity/Classes/Alternation/Savitch.lean), together with `mem_AP_iff_exists_mem_ATIME` in [Alternation.lean](../CslibFrontier/Computability/Complexity/Classes/Alternation.lean). This is native polynomial-time alternation with least-fixed-point acceptance and finite-state binary machines. The class equality asserts no resource-exact simulation for each time bound; [#4086](https://github.com/cslib-community/cslib-frontier/issues/4086) retains the quantitative simulations. |
| 5.13, $SAT\notin TISP(n^{1.1},n^{0.1})$ | 96 / 112 | **Partial.** [TimeSpace/Basic.lean](../CslibFrontier/Computability/Complexity/Classes/TimeSpace/Basic.lean) defines simultaneous bounds on one machine; the speedup and slowdown below are implemented. No inspected theorem proves this SAT endpoint. [#2896](https://github.com/cslib-community/cslib-frontier/issues/2896) owns the nondeterministic-linear-time lower-bound program but explicitly excludes transfer to SAT; [#4225](https://github.com/cslib-community/cslib-frontier/issues/4225) owns the small-formula Cook–Levin milestone and records the later local-computability/generation work needed for that transfer. Polynomial-time SAT completeness cannot preserve these exponents. |
| 5.14.1, $TISP(n^{12},n^2)\subseteq\Sigma_2TIME(n^8)$ | 97 / 113 | **Covered in the two-block verifier model.** `TISP_pow_twelve_subset_SigmaTwoTIME` in [Speedup.lean](../CslibFrontier/Computability/Complexity/Classes/TimeSpace/Speedup.lean) proves exactly these integer exponents using $(n+1)$ powers to handle length zero. The target is `SigmaTwoTIME`'s explicit verifier semantics, not a proved identification with all two-alternation ATMs (5.11). |
| 5.14.2, slowdown from $NTIME(n)\subseteq DTIME(n^{1.2})$ | 97 / 113 | **Partial (fractional resource endpoint).** `SigmaTwoTIME_subset_NTIME` in [Slowdown.lean](../CslibFrontier/Computability/Complexity/Classes/TimeSpace/Slowdown.lean) proves the general clock/majorization version; `SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow` gives integer-power instances. The displayed $n^{9.6}$ conclusion needs a natural-valued fractional-power clock and its constructibility/bounds; no checked specialization to this literal exponent was located. The same quantitative program is tracked by [#2896](https://github.com/cslib-community/cslib-frontier/issues/2896). |
| 5.15, $\Sigma_i^p=NP^{\Sigma_{i-1}SAT}$ | 98 / 114 | **Partial.** Native `NPWithOracle` exists, but [OracleNP.lean](../CslibFrontier/Computability/Complexity/Classes/PH/OracleNP.lean) proves $P^{NP}\subseteq\Sigma_2\cap\Pi_2$, not this equality. Searches through PH, oracle and quantified-SAT APIs did not locate a general encoded $\Sigma_iSAT$ completeness family and the oracle equality for all $i\ge2$. [#4086](https://github.com/cslib-community/cslib-frontier/issues/4086) is related alternation work, not ownership of this full oracle endpoint. |

### What the existing API establishes

- Machine-based `AP = PSPACE` is present. It does not substitute for either the fixed-alternation
  equivalences or the oracle characterization of every PH level.
- The speedup has the advertised integer exponents. The general slowdown states the costs needed
  to instantiate fractional bounds, but existence of a general theorem is not a checked instance.
- The SAT time–space endpoint remains open even after the intermediate alternation-trading
  lemmas: both the quantitative lower bound and the sufficiently efficient SAT reduction matter.

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

Chapters other than 1–5 and 14 have not been catalogued here. The first implementation milestones for
§22.1 are [#4712](https://github.com/cslib-community/cslib-frontier/pull/4712) and
[#4713](https://github.com/cslib-community/cslib-frontier/pull/4713); the latter distinguishes
the literal unrestricted draft 22.3 from the published theorem with an additive loss.
The full book-wide mapping and corrected density-amplification theorem remain open in
[#4711](https://github.com/cslib-community/cslib-frontier/issues/4711). This chapter audit does
not claim ownership of linked implementation issues or mark the overall objective complete.
