# Goldreich draft coverage audit

Audit: Christian Reitwiessner, with AI assistance.

This is a growing statement-level audit under [#4772](https://github.com/cslib-community/cslib-frontier/issues/4772),
not a completeness claim for the book or library. Its sources are Oded Goldreich's draft revisions of
*Computational Complexity: A Conceptual Perspective* dated December 2006 to May 2007, from the
[author's drafts page](https://www.wisdom.weizmann.ac.il/~oded/cc-drafts.html). File names and SHA-256
digests are listed in #4772. Numbers and pages belong to those drafts, not the 2008 published edition.
The end-of-chapter exercises of chapters 2 and 5–10 are classified in the companion
[exercise inventory](goldreich-2007-exercises.md), which also points to the Chapter 3 and 4 records.

The results registry remains [Entries.lean](../CslibFrontierResults/Entries.lean). A nearby theorem is
not counted as full coverage.

## Theory exercises: Chapter 3

Source: January 2007 `r2.pdf`, PDF pp. 15–20/printed pp. 131–136, SHA-256
`40c735ae7a67331b4b008e09b21bc7b65103937c05a148fac222e5b72d253704`.
The twelve exercise numbers and their subparts were read from the primary text. Mapping uses
`3611ca71f` plus the new envelope theorem below. This is a bounded exercise inventory, not a
book-wide classification. Christian Reitwiessner's scope includes theory-establishing exercises;
routine representation checks are recorded without creating proof work. Existing results are
reused. [Checked correspondence clients](../CslibFrontierTests/GoldreichExercises.lean) cover
3.2(2), 3.5 and the nonsparse-envelope specialization of 3.12.

Here `SPARSE` counts words of length at most $n$, while the source bounds each exact length.
Polynomial sparseness is unchanged: a prefix census sums at most $n+1$ per-length bounds,
and a per-length census is bounded by the prefix census. No coefficient-one identity is claimed.
`PWithOracle` means adaptive native polynomial-time oracle computation; it is not a many-one
reduction. Ordinary bit languages use `encBits` throughout the class identities.

| Exercise | PDF / printed page | Endpoint and disposition |
|---|---|---|
| 3.1 | 15–16 / 131–132 | **Routine representation reformulation, outside implementation scope.** The prompt changes devices from exact-length to up-to-length inputs with an explicit delimiter encoding. Its representation choice is relevant to 3.11; the existing exact-length/advice equivalence alone is not recorded as that encoding bridge. |
| 3.2(1) | 16 / 132 | **Covered.** `Cslib.Circuits.Boolean.PPoly.of_sparse` in [Boolean/Sparse](../CslibFrontier/Computability/Circuit/Boolean/Sparse.lean) takes a polynomial bound on each slice, matching the source's census; `PPoly.of_mem_SPARSE` accepts the prefix-census class. No decidability is required. |
| 3.2(2) | 16 / 132 | **Covered.** `Cslib.Complexity.mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle` in [Sparse/Meyer](../CslibFrontier/Computability/Complexity/Classes/Sparse/Meyer.lean) is P/poly = P with a suitable sparse oracle. The checked client converts the `encBits` agreement interface to ordinary circuit languages. |
| 3.3 | 16 / 132 | **Endpoint not located.** The source asks for $\mathrm{P}/\ell \subsetneq \mathrm{P}/(\ell+\delta)$ when $\ell(n)<2^{n-1}$ and $\delta$ is unbounded; this is separate from polynomial advice and circuit-size hierarchies. A formal endpoint must retain the possibility that the additional-length function oscillates; eventual monotonic growth must not silently replace unboundedness. This direction is already proposed in [#4777](https://github.com/cslib-community/cslib-frontier/pull/4777), alongside its numbered-result audit. |
| 3.4 | 16 / 132 | **Covered.** `Cslib.Complexity.PWithOracle_subset_SigmaP_two` in [PH/OracleNP](../CslibFrontier/Computability/Complexity/Classes/PH/OracleNP.lean) applies to every NP oracle, so includes every Cook reduction to an NP set. |
| 3.5 | 16 / 132 | **Covered.** `Cslib.Complexity.iUnion_PWithOracle_NP_inter_coNP` in [Oracle/Lowness](../CslibFrontier/Computability/Complexity/Classes/Oracle/Lowness.lean) identifies exactly the union of these oracle classes with NP ∩ coNP; the existential formulation is checked in the client. |
| 3.6 | 16 / 132 | **Covered by the existing characterization.** `PiP`, `mem_PiP`, `IsAlternatingVerifier.compl` and `PiP_eq_preimage_compl_SigmaP` in [PH](../CslibFrontier/Computability/Complexity/Classes/PH.lean) give universal-first alternating verification. The source's common polynomial block length is a specialization of the independent block bounds. |
| 3.7 | 17 / 133 | **Endpoint not located.** No bounded-alternation `kQBF` language and Σₖ-completeness endpoint was found. Unrestricted `TQBF_pspaceComplete` and `TQBFCNF_pspaceComplete` do not supply it. |
| 3.8(1–2) | 17–18 / 133–134 | **Endpoints not located.** Neither the PH-to-highly-uniform depth-k circuit/succinct-input reduction nor the converse evaluation theorem was found. Generic circuit evaluation does not certify the source's polynomial-time local gate/edge query interface. |
| 3.9(1–2) | 18 / 134 | **Partial.** `mem_PWithOracle_self` supplies the lower inclusions. At k=1 the NP-oracle bounds in `PH/OracleNP` supply the upper inclusions; the all-k oracle simulations were not located. |
| 3.9(3–4) | 18 / 134 | **Covered by existing hierarchy/duality APIs.** `SigmaP_subset_PiP_succ`, `PiP_subset_SigmaP_succ`, `PH_eq_iUnion_PiP`, `PiP_eq_SigmaP_of_PiP_subset_SigmaP` and the complement identities in `PH` give the inclusions, union and equality from either same-level inclusion. |
| 3.10(1–2) | 19 / 135 | **Endpoints not located.** No defined `1QBF` equivalence with SAT or general bounded-level QBF oracle identities were found. SAT's NP-completeness and unrestricted QBF completeness do not establish these particular interfaces. |
| 3.11(1) | 19 / 135 | **Endpoint not located.** A generic downward-self-reduction interface with coNP certification of circuit correctness was not found. The guideline uses the up-to-length representation from 3.1; an exact-length circuit alone does not provide all shorter answers. |
| 3.11(2) | 19 / 135 | **Conclusion covered; alternative proof route remains open.** `NP_subset_PPolyOn_iff_SAT` and `PiP_two_eq_SigmaP_two_of_SAT` in [PH/KarpLipton](../CslibFrontier/Computability/Complexity/Classes/PH/KarpLipton.lean) yield the collapse. They do not certify Part 1's circuit-correctness construction. |
| 3.12 | 19–20 / 135–136 | **New formalization.** `Cslib.Complexity.SAT_mem_P_of_sparse_diff` in [Sparse/Envelope](../CslibFrontier/Computability/Complexity/Classes/Sparse/Envelope.lean) proves SAT ∈ P from a many-one reduction to S ⊆ G, G ∈ P and sparse G ∖ S. G itself need not be sparse or S decidable. The proof reuses Fortune through a guarded reduction of UNSAT, with the empty-difference case separate; it does not reproduce the source's DFS proof. |

Negative searches inspected the PH, Oracle, Sparse, SAT/QBF, advice and circuit interfaces for
these endpoints. “Not located” is a scoped search result, not proof of semantic absence.
The remaining theory exercises, source-model bridges and book-wide formalization stay open in
[#4772](https://github.com/cslib-community/cslib-frontier/issues/4772); this exercise layer does
not complete the numbered-result audit or take ownership of its other proposals.

## Exact advice-length comparison: a model qualification

The January 2007 draft defines advice strings of exactly $\ell(n)$ bits (Definition 3.5,
`r2.pdf` PDF4/printed120). Exercise 3.3 (PDF16/printed132) and Theorem 4.1 (PDF22/printed138)
display an unbounded additive gap. Prose following Theorem 3.7 also writes a positive difference,
which may express an intended extra condition. These formulations must be distinguished when
the length functions are arbitrary and not assumed computable.

[Advice/LengthComparison](../CslibFrontier/Computability/Complexity/Classes/Advice/LengthComparison.lean)
proves an **original counterexample for the exact-length model**. Its
`exists_nonmonotone_advice_bounds` supplies polynomially bounded lower/gap functions, both source
capacity bounds, an unbounded gap, and a language in P/lower that is outside P/(lower+gap).
This refutes containment from an unbounded nonnegative gap alone; it does not refute a theorem
with an additional strictly positive-gap hypothesis. The length functions and advice families
are not claimed computable. Since the bounds are polynomial, the complete-pair running-time
convention does not introduce a superpolynomial input-time allowance in this counterexample.

The mechanism is explicit. At selected odd lengths the upper bound is exactly one bit, giving
any fixed decider only two possible output patterns on the all-false and all-true words. A lower
decider uses three codes (empty, `[false]`, `[true]`) for the patterns 00, 11 and 01. Choosing a
missing pattern diagonalizes against a countable enumeration of native P predicates. On even
lengths the lower advice is empty and the upper bound grows linearly, making the gap unbounded.
Length metadata, rather than a new gate model or unbounded running time, supplies the third code.

The author's [official tighter Theorem 4.1 addendum](https://www.wisdom.weizmann.ac.il/~oded/CC/ad-hier.txt)
uses a constant one-bit gap. It is not contradicted here: `PWithAdvice_subset_succ` proves the
safe inclusion direction for arbitrary lower bounds. More generally,
`PWithAdvice_subset_of_lt` proves containment under strict pointwise growth, with no
computability assumptions on either bound: append a true delimiter and false padding, then
normalize the binary word and remove its last bit.
[Advice/Hierarchy](../CslibFrontier/Computability/Complexity/Classes/Advice/Hierarchy.lean)
now proves the positive-gap strict hierarchy: `PWithAdvice_ssubset_of_lt` requires strict
pointwise growth and only eventual upper capacity. `PWithAdvice_pred_ssubset` specializes it
to one fewer bit, with positivity explicit so natural subtraction actually removes a bit.
`PWithAdvice_const_ssubset_succ` handles all constant lengths, without a short-input capacity
restriction. The
[checked clients](../CslibFrontierTests/AdviceLengthComparison.lean) state the failed universal
containment contract and verify zero-baseline, fixed-bit and variable positive-gap inclusions.
The positive-gap, upper-capacity versions of Exercise 3.3 and Theorem 4.1 are therefore
covered under the exact full-pair model. Exercise 3.3 places upper capacity in its guideline,
rather than its displayed hypotheses; that restriction is material to this coverage claim. Their unqualified displayed nonnegative-gap formulations remain
subject to the counterexample above; they are not silently reported as proved. The
book-wide objective remains open.

The strict hierarchy proof maps the source argument directly. Enumerate the countable native
P predicates on advice/input pairs. At each assigned length, lower advice gives at most
$2^{\mathrm{lower}(n)}$ patterns on the first $\mathrm{upper}(n)$ binary inputs. There are
$2^{\mathrm{upper}(n)}$ higher advice words, so choose a missing pattern. The fixed decoder
reads that pattern by a capped, zero-based most-significant-bit-first binary index (the
source numbers inputs from one); its certificate is polynomial in the complete
pair length, not in the numeric index or solely the ordinary input length. Each predicate
fails at one assigned length, sufficient under the exact/no-exception convention explicitly
allowed by the official addendum. No effective enumeration or computation of the advice is
asserted, and no infinitely-often separation against arbitrary-time lower machines is claimed.

[Boolean/Advice/Hierarchy](../CslibFrontier/Computability/Circuit/Boolean/Advice/Hierarchy.lean)
combines constant-length strictness with the existing polynomial-advice/circuit bridge.
`PWithAdvice_const_ssubset_PPoly 1` supplies the strict P/1 versus P/poly assertion following
Theorem 3.7 (PDF6/printed122). Together with the one-bit undecidable language already proved
in [Advice/OneBit](../CslibFrontier/Computability/Complexity/Classes/Advice/OneBit.lean), this
covers that draft theorem's endpoints in the stated model. The
[checked hierarchy clients](../CslibFrontierTests/AdviceHierarchy.lean) extract a two-bit
separating language and check zero, short constant and exponential-capacity boundaries.

## Theory exercise 4.3: sublinear time

Source: January 2007 `r2.pdf`, PDF35/printed151, SHA-256
`40c735ae7a67331b4b008e09b21bc7b65103937c05a148fac222e5b72d253704`.
The complete Chapter 4 theory-exercise pass and remaining endpoints are recorded in
[#4772](https://github.com/cslib-community/cslib-frontier/issues/4772#issuecomment-6841285129).
This bounded formalization is tracked by [#4906](https://github.com/cslib-community/cslib-frontier/issues/4906);
it does not complete that inventory or the book-wide objective.

**Covered in the native sequential-input model.**
[MultiTape/Complexity/Sublinear](../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/Sublinear.lean)
proves `exists_uniform_time_of_isLittleO`: a fixed deterministic machine halting on every
word within a uniform clock $p(n)=o(n)$ has a global constant halt bound. Neither computability
nor monotonicity of `p`, nor finiteness of the alphabet or control, is needed for this run theorem.
`exists_uniform_time_of_fast_length` is stronger: one width with $p(N)\le N$ suffices under
the uniform total clock on every word, including all shorter inputs.

The source's input-length caveat is explicit. Native control reads only tape symbols;
length is not supplied as another argument. The
[input-prefix theorem](../CslibFrontier/Computability/Machines/Turing/MultiTape/InputPrefix.lean)
compares natural-valued head positions across different input-dependent configurations,
including both boundaries, and preserves state, heads, work tapes and output through the
prefix's length. A finite supremum over shorter lengths gives the constant.

`ComputableInTimeAndSpace.exists_const_time_of_isLittleO` preserves the computed function,
output encoding and original independent workspace bound for input encoding `encBits`.
[Time/Sublinear](../CslibFrontier/Computability/Complexity/Classes/Time/Sublinear.lean) derives
`DTIME_eq_const_of_isLittleO`, including affine clock constants. Arbitrary encodings may have
invalid prefixes, so no encoding-general extension is asserted. Models with free input
length or random input access are outside this claim.

The [checked clients](../CslibFrontierTests/SublinearTime.lean) exhibit input-sensitive constant
time, the inclusive prefix boundary, the necessary extension restriction and the zero-bound
class. The source's philosophical quantification over reasonable models is represented by
this precise native model, not by a theorem over all computational models.

## Chapter 4: exact step-counter exercise

Exercise 4.5 (January 2007 `r2.pdf`, PDF page 36 / printed page 152) is covered by
`Turing.MultiTapeTM.exists_stepCounter` in
[StepCounter](../CslibFrontier/Computability/Machines/Turing/MultiTape/Combinators/StepCounter.lean).
The fixed finite native machine receives `encNat n` (least-significant-first binary), visits one
designated signal state exactly $n$ times, starts outside that state and leaves every visit on
the next transition. It halts within $c(n+1)$ steps for one uniform constant, including all
preparation and $n=0$. The draft's default binary-number convention is in December 2006
`r1.pdf`, PDF page 45 / printed page 20; this differs only in binary digit order.

The construction reuses exact binary-to-unary conversion and the existing native clock, rather
than counting a rounded budget or output length. The source's displayed endpoint asks for total
runtime; no logarithmic workspace or per-prefix latency guarantee is inferred. The
[checked clients](../CslibFrontierTests/StepCounter.lean) instantiate the full machine and check
zero and positive counts. This completes this exercise endpoint only; the chapter-wide audit
and other theory-establishing exercises remain under [#4772](https://github.com/cslib-community/cslib-frontier/issues/4772).

## Chapter 1: Introduction and preliminaries

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.

The PDF heading-font scan found seven numbered result headings in chapter 1 and none in
chapter 0. Both the glyph-position extraction and the original Type 3 heading spans were checked;
proof references and exercise references were excluded. The draft file digests match #4772.
Printed pages in `r1.pdf` are PDF pages minus 25. The native machine model uses finite states,
read-only input, write-only output and bidirectional work tapes. Descriptions, pair encodings,
and partial-recursive codes are identified only where the row says so; no model conversion is
silently charged zero time. Negative findings are qualified searches of the named modules,
neighboring APIs, pinned CSLib and selected Mathlib computability modules, not proofs that no equivalent theorem exists anywhere.
No Lean builds, checked client additions, or whole-library semantic/axiom audit were performed.
Names are in `Cslib.Complexity` unless qualified otherwise. A Covered row may use explicit
specialization or elementary consequences of the cited statements; it does not claim a newly
checked client for those consequences.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 1.4 | `r1.pdf` / 54 / 29 | **Partial.** `Turing.MultiTapeTM.countable_setOf_isDecidable` in [Countable.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting/Countable.lean) counts decidable sets under any fixed encoding. Mathlib’s [PartrecCode.lean](https://github.com/leanprover-community/mathlib4/blob/69552756cd8a2d2d48763cf7279fd814d6a1224d/Mathlib/Computability/PartrecCode.lean) also provides `Countable {f : ℕ → ℕ // Computable f}` and its partial-function analogue. The heading counts string-valued functions and contrasts them with the continuum of all functions; the full encoded-string cardinality statement was not located. Finite descriptions explain the extension, but it is not a checked client here. |
| 1.5 | `r1.pdf` / 55 / 30 | **Covered.** `Turing.MultiTapeTM.not_isDecidable_haltingProblem` and `not_isDecidable_selfHaltingProblem` in [Halting.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting.lean) give both pair and diagonal versions for native descriptions. The pair uses `encPair encBits encBits`; the draft does not fix the same description encoding. |
| 1.6 | `r1.pdf` / 57 / 32 | **Covered.** `Turing.MultiTapeTM.rice` and `not_isDecidable_of_behavior` in [Rice.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting/Rice.lean) quantify over extensional properties with explicit descriptions witnessing nontriviality. Native behavior is the graph of partial output on bit inputs, with natural-symbol outputs; this realizes the semantic property formulation, rather than a property of syntax. |
| 1.7 | `r1.pdf` / 57 / 32 | **Covered.** `Cslib.PostCorrespondence.not_computablePred_solvable_bool` and `not_computablePred_solvable` in [Undecidable.lean](../CslibFrontier/Computability/PostCorrespondence/Undecidable.lean) prove ordinary PCP undecidability over Bool, or any primcodable alphabet with two distinct letters. `Solvable` requires a nonempty tile sequence; the theorem uses Mathlib computability, not a native time bound. |
| 1.9 | `r1.pdf` / 58 / 33 | **Partial.** `Turing.MultiTapeTM.Universal.computableInO_universal_nlogn` in [WindowedComplexity.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Universal/WindowedComplexity.lean) certifies a **clocked** native interpreter. `Turing.MultiTapeTM.Universal.Desc.partrec_eval` in [Partrec.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Halting/Partrec.lean) supplies unbounded partial evaluation as a partial-recursive function. Neither statement alone is an unclocked native TM realizing that partial function; retain the distinction under [#800](https://github.com/cslib-community/cslib-frontier/issues/800). |
| 1.10 | `r1.pdf` / 59 / 34 | **Partial.** `Cslib.Kolmogorov.DescriptionMethod.isAdditivelyOptimal_universal` in [Partrec.lean](../CslibFrontier/Computability/Kolmogorov/Partrec.lean) establishes additive optimality for the constructed universal description method over partial-recursive methods; `Simulation.ecomplexity_le` in [Invariance.lean](../CslibFrontier/Computability/Kolmogorov/Invariance.lean) gives the general compiler bound. These use extended-natural complexity and explicit bounded-length compilation. Mere universality without the draft proof’s adequate pair encoding is insufficient: a compiler-length/optimality hypothesis must accompany an arbitrary $U$. No arbitrary-native-$U$ endpoint was located. |
| 1.13 | `r1.pdf` / 70 / 45 | **Partial.** `Cslib.Circuits.Boolean.PPoly.of_slice_const` in [PPoly.lean](../CslibFrontier/Computability/Circuit/Boolean/PPoly.lean) gives circuits for any length-dependent bit sequence. A one-bit-advice undecidable function, with an explicit noncomputability proof, was not located in the advice or countability modules; this would also supply the core of 3.7. Polynomial circuit membership alone does not prove that separation. |

## Chapter 2: P, NP and NP-completeness

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.

All 19 top-level numbered results were checked against the original heading-font scan and
the extracted statements. PC corresponds to balanced polynomially decidable relations (`FNP`);
PF search includes correct failure on empty solution sets. Candid search in 2.33 is a different
contract. Karp, Levin and adaptive Cook reductions are distinguished below. The draft’s formula
language and the library’s encoded CNFs are polynomially related presentations, not literally
identical input types. No quasi-linear Cook–Levin claim is inferred from polynomial completeness;
that objective remains #4225.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 2.6 | `r1.pdf` / 85 / 60 | **Covered.** `FNP_subset_FPSearch_iff` and `FNP_subset_FPSearch_iff_SAT_mem_P` in [SearchToDecision.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP/SearchToDecision.lean) express the search/decision collapse. The former quantifies over all encoded instance types; [TFNP.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP.lean) defines balanced polynomially decidable `FNP` and solvers returning `Option` witnesses, including a correct no-solution answer. The fixed-bit-language formulation still needs the standard encoding transfer if used literally. |
| 2.8 | `r1.pdf` / 87 / 62 | **Covered.** `mem_NP_iff_decidableInPolyTime` in [Nondeterministic.lean](../CslibFrontier/Computability/Complexity/Classes/NP/Nondeterministic.lean) is the verifier/native NTM equivalence under the same explicit encoding. Certificates have fixed polynomial length (padding handles shorter witnesses), binary nondeterminism, and all-branch polynomial running time. |
| 2.10 | `r1.pdf` / 90 / 65 | **Partial.** `prefixSearch_mem_FNP`, `rel_prefixSearchRun`, and `FNP_subset_FPSearch_of_NP_subset_P` in [SearchToDecision.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP/SearchToDecision.lean) provide the prefix relation and algorithm under a polynomial-time prefix decider. A certified oracle computation for every FNP relation was not located there. SAT’s actual oracle certificate exists (2.15); replacing a decider assumption by an oracle resource certificate is a remaining step. Related foundations: [#151](https://github.com/cslib-community/cslib-frontier/issues/151). |
| 2.13 | `r1.pdf` / 93 / 68 | **Partial.** [ThresholdSearch.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/ThresholdSearch.lean) proves `computableInPolyTimeWithOracleQueries_solveMaxSAT` for a concrete MaxSAT threshold oracle and `solveMaxSAT_spec`. The general equivalence between threshold search and maximization for any balanced relation and polynomial-bit rational objective was not located. The preceding source paragraph explicitly restricts represented real outputs to rationals, so arbitrary exact-real computation is not claimed. |
| 2.15 | `r1.pdf` / 96 / 71 | **Covered.** `SAT.exists_search_withOracle`, `SAT.computableInPolyTimeWithOracle_search`, and `SAT.verifier_search_image` in [SelfReduction.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/SelfReduction.lean) certify search relative to the bit-language oracle `encCNF '' SAT` (image). Assignments are occurrence certificates for encoded CNFs. Correctness is an iff, so a failed verification also detects unsatisfiability; general formula syntax requires a conversion. |
| 2.16 | `r1.pdf` / 98 / 73 | **Partial.** The prefix construction of 2.10 and witness-preserving `CookLevin.SAT_levinHard` in [Levin.lean](../CslibFrontier/Computability/Complexity/CookLevin/Levin.lean) are ingredients. No inspected theorem certifies generic search relative to the original domain oracle when that domain is NP-complete, including oracle substitution/composition. SAT self-reducibility alone is not this assertion for every relation. |
| 2.19 | `r1.pdf` / 100 / 75 | **Covered.** `CookLevin.SAT_npComplete` in [Completeness.lean](../CslibFrontier/Computability/Complexity/CookLevin/Completeness.lean) and `CookLevin.SAT_levinHard` in [Levin.lean](../CslibFrontier/Computability/Complexity/CookLevin/Levin.lean) establish existence of complete decision and witness relations (the latter has both witness maps). This covers the existential heading; the proof’s particular universal relation on $(M,x,1^t)$ was not located as a complete problem. This overlaps the unary-clock TMSAT proposal in [#4766](https://github.com/cslib-community/cslib-frontier/pull/4766), with a different witness-length layout; binary-clock deterministic bounded halting is not a substitute. |
| 2.20 | `r1.pdf` / 103 / 78 | **Partial.** `NPHard.trans` and `PolyTimeReducible.trans` in [Reduction.lean](../CslibFrontier/Computability/Complexity/Reduction.lean) transfer decision hardness; `LevinHard.trans` and `LevinReduction.trans` in [Levin.lean](../CslibFrontier/Computability/Complexity/Reduction/Levin.lean) transfer witness hardness. Membership in the target completes these variants. The bundled unrestricted Cook-reduction variant is not established by these many-one APIs (reduction infrastructure is tracked in [#1351](https://github.com/cslib-community/cslib-frontier/issues/1351)); the library’s Levin reduction additionally carries a forward witness map. |
| 2.21 | `r1.pdf` / 103 / 78 | **Partial.** `CircuitSAT_npComplete` in [CircuitSAT.lean](../CslibFrontier/Computability/Complexity/Problems/CircuitSAT.lean) covers the decision endpoint for De Morgan circuits encoded by `encCircuit 1`. Circuit evaluation is certified, but no inspected witness-preserving completeness theorem for the circuit satisfaction relation was located. The SAT witness-preserving endpoint does not automatically supply circuit witness translation. |
| 2.22 | `r1.pdf` / 106 / 81 | **Covered.** `CookLevin.SAT_npComplete` in [Completeness.lean](../CslibFrontier/Computability/Complexity/CookLevin/Completeness.lean) and `CookLevin.SAT_levinHard` in [Levin.lean](../CslibFrontier/Computability/Complexity/CookLevin/Levin.lean) provide decision and relation completeness for CNFs under `encCNF`, with an explicit polynomial-time verifier. Both witness directions are provided, stronger than the draft’s backward-only search reduction. Formula assignments are represented by finite occurrence certificates, not infinite functions on variable names. |
| 2.23 | `r1.pdf` / 109 / 84 | **Covered.** `ThreeSAT_npComplete` in [ThreeSAT.lean](../CslibFrontier/Computability/Complexity/Problems/ThreeSAT.lean) and `ThreeSATThree_npComplete` in [ThreeSATThree.lean](../CslibFrontier/Computability/Complexity/Problems/ThreeSATThree.lean) prove both clauses: width at most three and at most three total variable occurrences. This implies at most three clauses per variable. Binary linking clauses are allowed, as in the draft; exact-width-three occurrence-three SAT is a different problem. |
| 2.24 | `r1.pdf` / 110 / 85 | **Partial.** `SetCover_mem_NP` in [SetCover.lean](../CslibFrontier/Computability/Complexity/Problems/SetCover.lean) uses a finite set-system encoding and an at-most-$k$ threshold. No ordinary `SetCover_npComplete` was located. Promise gap hardness in [LundYannakakis.lean](../CslibFrontier/Computability/PCP/Approximation/SetCover/LundYannakakis.lean) is nearby but needs an explicit decision bridge; [#2904](https://github.com/cslib-community/cslib-frontier/issues/2904) already owns ordinary set-cover completeness. |
| 2.25 | `r1.pdf` / 110 / 85 | **Endpoint not located.** No 3-exact-cover NP-completeness endpoint was located in the problem modules. The source requires sets of size at most three, and discusses unrestricted and bounded numbers of chosen sets. Exact cover is already a remaining objective of [#2904](https://github.com/cslib-community/cslib-frontier/issues/2904); checked size-three and threshold variants should be included there, rather than opening duplicate issues. |
| 2.26 | `r1.pdf` / 112 / 87 | **Covered.** `VertexCover_npComplete`, `IndependentSet_npComplete`, and `Clique_npComplete` in [VertexCover.lean](../CslibFrontier/Computability/Complexity/Problems/VertexCover.lean), [IndependentSet.lean](../CslibFrontier/Computability/Complexity/Problems/IndependentSet.lean), and [Clique.lean](../CslibFrontier/Computability/Complexity/Problems/Clique.lean) use finite listed graphs, binary cardinality parameters, and `encPair encGraph encNat`. All three native predicates require exactly $k$ declared vertices: `VertexCover` has `S.card = k`, and the others use `IsNIndepSet k` / `IsNClique k`. The draft defines covers with at most $k$ vertices (r1 PDF 111 / printed 86) and independent sets/cliques with at least $k$ (Exercise 2.26, PDF 136 / printed 111). For covers, pad a smaller cover to $k$ when $k\le\#V$, or clamp the threshold to $\min(k,\#V)$; for independent sets/cliques, take a $k$-element subset. Without clamping, an edgeless one-vertex graph at $k=2$ separates the at-most and exact cover predicates. This is decision completeness, not a claim about the draft’s specific gadgets. |
| 2.27 | `r1.pdf` / 112 / 87 | **Covered.** `ThreeColoring_npComplete` in [Coloring.lean](../CslibFrontier/Computability/Complexity/Problems/Coloring.lean) is graph 3-colorability under `encGraph`. Vertices have three possible colors and edges require distinct colors; using fewer than all three colors is allowed. |
| 2.28 | `r1.pdf` / 114 / 89 | **Partial.** `Ladner.exists_NP_not_P_not_npComplete` in [Ladner.lean](../CslibFrontier/Computability/Complexity/Classes/Ladner.lean) gives an NP language outside P and not **many-one** NP-complete. Goldreich excludes hardness even for adaptive Cook reductions; that stronger nonhardness endpoint was not located. [#3142](https://github.com/cslib-community/cslib-frontier/issues/3142) explicitly uses many-one reductions, so it does not own the stronger oracle-degree theorem. |
| 2.33 | `r1.pdf` / 123 / 98 | **Endpoint not located.** No Levin optimal candid-search theorem was located in search, universal-machine, or Kolmogorov modules: a fixed solver for each PC relation, pointwise time $O(t_{A\prime}(x)+p(\|x\|))$ on positive instances, with competitor-dependent constant. The paragraph after the theorem (same page) assumes a model admitting constant-overhead bounded simulation for this ordinary-$O$ bound; polylogarithmic simulation overhead instead gives $\widetilde O(t_{A\prime}(x)+p(\|x\|))$. A native-TM target must retain its certified simulation overhead rather than assume the sharp bound. Clocked universality and abstract Blum speed-up do not give this endpoint. Candid solvers may diverge on negative instances; do not replace them by total `FPSearch` solvers. |
| 2.34 | `r1.pdf` / 126 / 101 | **Partial.** `NPComplete.compl` in [Reduction.lean](../CslibFrontier/Computability/Complexity/Reduction.lean) makes the complement coNP-complete; `PolyTimeReducible.mem_NP` in [Witness.lean](../CslibFrontier/Computability/Complexity/Classes/NP/Witness.lean) transfers NP membership back along reductions. The stated contraposition follows with encoding-uniform NP/coNP collapse assumptions. A direct fixed-bit-language checked consequence was not located; no new diagonal theorem is needed. |
| 2.35 | `r1.pdf` / 126 / 101 | **Covered.** `PWithOracle_subset_NP_inter_coNP` and `iUnion_PWithOracle_NP_inter_coNP` in [Lowness.lean](../CslibFrontier/Computability/Complexity/Classes/Oracle/Lowness.lean) establish that reductions to NP ∩ coNP remain in that intersection, including a different oracle for each language. Thus the source hypothesis forces NP ⊆ coNP and equality by complement. This uses ordinary decision-language oracles; the draft explicitly excludes promise problems. |

## Chapter 3: Variations on P and NP

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.

All eight numbered headings were checked against the PDF heading spans and extracted text.
Printed pages in `r2.pdf` equal PDF pages plus 116. Polynomial hierarchy verifiers use polynomial
blocks on framed instance/witness encodings; fixed-domain collapse hypotheses do not silently
become hypotheses over every encoding. The $P/1$ and arbitrary advice-length assertions are
kept distinct from polynomial-union advice/circuit equivalence.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 3.1 | `r2.pdf` / 2 / 118 | **Covered.** `Cslib.Circuits.Boolean.computableInPolyTime_evalCode`, `computableInPolyTime_evalOutput`, and `Circuit.eval_eq_evalOutput` in [EvaluationTime.lean](../CslibFrontier/Computability/Circuit/Boolean/EvaluationTime.lean) certify encoded gate-list evaluation and arbitrary output-wire access. Circuit indices are binary, arities encoded explicitly, and the basis is De Morgan; producing all outputs uses polynomially many such accesses, not unit-cost evaluation of a whole circuit. |
| 3.4 | `r2.pdf` / 4 / 120 | **Covered.** `Cslib.Circuits.Boolean.computableInPolyTime_evalCircuit` in [EvaluationTime.lean](../CslibFrontier/Computability/Circuit/Boolean/EvaluationTime.lean) certifies evaluation of an efficiently generated typed circuit on an efficiently computed bit list. Specialize the generator to depend on unary input length. Inputs are padded/truncated by the library, whereas the draft supplies exactly the circuit’s arity; under that premise they agree. No converse uniform synthesis theorem is inferred from nonuniform membership. |
| 3.6 | `r2.pdf` / 5 / 121 | **Covered.** `Cslib.Circuits.Boolean.PPoly_eq_PAdvice` in [Advice.lean](../CslibFrontier/Computability/Circuit/Boolean/Advice.lean) and `mem_PPoly_iff_exists_circuits` in [PPoly.lean](../CslibFrontier/Computability/Circuit/Boolean/PPoly.lean) establish the polynomial-advice/circuit equivalence. Advice is framed before the input and bounded polynomially; gates include constants. This covers the numbered polynomial-advice assertion, not the subsequent informal extension to arbitrary possibly superpolynomial advice lengths. |
| 3.7 | `r2.pdf` / 6 / 122 | **Partial.** `Cslib.Circuits.Boolean.PPoly.of_slice_const` in [PPoly.lean](../CslibFrontier/Computability/Circuit/Boolean/PPoly.lean) and polynomial-advice equivalence in [Advice.lean](../CslibFrontier/Computability/Circuit/Boolean/Advice.lean) provide the length-dependent circuit/advice ingredients. No inspected theorem isolates P/1 with an undecidable language, or P/1 strictly below P/poly. This shares the 1.13 gap; the ensuing general advice hierarchy needs a separate counting/diagonal argument (4.1). |
| 3.9 | `r2.pdf` / 8 / 124 | **Covered.** `exists_mem_PiP_of_mem_SigmaP_succ` in [Projection.lean](../CslibFrontier/Computability/Complexity/Classes/PH/Projection.lean) gives one direction. For the converse, `PiP_subset_SigmaP_succ` in [PH.lean](../CslibFrontier/Computability/Complexity/Classes/PH.lean) followed by `mem_SigmaP_of_exists` in [Collapse.lean](../CslibFrontier/Computability/Complexity/Classes/PH/Collapse.lean) projects a Pi-level relation into the next Sigma level. The latter has positive level $k+1$, so includes the source’s $k=0$ case. Witness lengths are exact polynomial lengths relative to explicit framed pair encodings; the projection proof performs the necessary rebounding. |
| 3.10 | `r2.pdf` / 9 / 125 | **Partial.** `SigmaP_succ_subset_SigmaP`, `PH_eq_SigmaP_of_PiP_subset_SigmaP`, and `PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP` in [Collapse.lean](../CslibFrontier/Computability/Complexity/Classes/PH/Collapse.lean) prove collapse under hypotheses uniform over encoded types. The draft states equality of bit-language classes and also a converse. A checked transport of that fixed-domain hypothesis and the full bundled iff was not located; [#4766](https://github.com/cslib-community/cslib-frontier/pull/4766) records the same encoding boundary. |
| 3.11 | `r2.pdf` / 10 / 126 | **Endpoint not located.** No general equality $\Sigma_{k+1}^P=NP^{\Sigma_k^P}$ was located. [OracleNP.lean](../CslibFrontier/Computability/Complexity/Classes/PH/OracleNP.lean) proves the smaller endpoint $P^{NP}\subseteq\Sigma_2^P\cap\Pi_2^P$. The general quantified-SAT/oracle characterization is already a proposed development issue in [#4766](https://github.com/cslib-community/cslib-frontier/pull/4766); [#4086](https://github.com/cslib-community/cslib-frontier/issues/4086) owns related alternating-resource simulations, not this oracle equality. |
| 3.12 | `r2.pdf` / 13 / 129 | **Covered.** `PiP_two_eq_SigmaP_two_of_SAT` and `NP_subset_PPolyOn_iff_SAT` in [KarpLipton.lean](../CslibFrontier/Computability/Complexity/Classes/PH/KarpLipton.lean) give the stated equality from NP bit-language circuit containment via the SAT encoding bridge. `PH_eq_SigmaP_two_of_SAT` gives the further collapse. This avoids assuming containment separately for every encoding. Circuit guesses and SAT witness verification are polynomially certified; advice need not be computable. |

## Chapter 4: More resources, more power?

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib pin `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`.

All eight numbered headings were checked against the PDF heading spans and extracted text;
the rendered pages for 4.1, 4.3–4.5 were also inspected to recover superscripts and logarithms.
Goldreich §1.2.3.5 (`r1.pdf` / PDF 63 / printed 38) counts work-tape cells scanned,
including blank cells, with read-only input and write-only output excluded. This agrees with
native visited-cell accounting in [Space/Basic.lean](../CslibFrontier/Computability/Complexity/Classes/Space/Basic.lean),
which sums visited cells over the work tapes; there is no scanned-versus-visited measure gap.
In particular 4.9 records the asymptotic hierarchy with this common measure. Its remaining
model qualification is the conversion from native arbitrarily many fixed work tapes to the
draft’s three-tape machine (input, output and one work tape); no such space-exact compiler is
certified here. “Covered” refers to that stated native-model variant.
Abstract computability of a bound is not time/space constructibility, and abstract program cost
is not automatically worst-case time at a string length.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| 4.1 | `r2.pdf` / 22 / 138 | **Endpoint not located.** No strict advice-length hierarchy for arbitrary $\ell_0,\delta$ with $\ell_0(n)+\delta(n)\le 2^n$ and unbounded $\delta$ was located in advice, circuit counting, or hierarchy modules. Existing `PAdvice` is a polynomial union, not the fixed-length class P/$\ell$. The proof must allow unbounded oscillation, rather than assume $\delta(n)\to\infty$. |
| 4.3 | `r2.pdf` / 25 / 141 | **Partial.** `DTIME_ssubset_DTIME` in [Time.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/Time.lean) requires eventual $(n+1)^8(f(n)+1)^3\le g(n)$, not the source’s $t_2\ge t_1(\log t_1)^2$ with constructible lower bound. [#4211](https://github.com/cslib-community/cslib-frontier/issues/4211), under [#1572](https://github.com/cslib-community/cslib-frontier/issues/1572) and [#800](https://github.com/cslib-community/cslib-frontier/issues/800), owns sharp time hierarchy. Native machines have arbitrarily many fixed work tapes, not exactly two tapes; near-linear fixed-description interpretation alone does not establish the sharp diagonal. |
| 4.4 | `r2.pdf` / 25 / 141 | **Partial.** The polynomial-overhead separation `DTIME_ssubset_DTIME` in [Time.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/Time.lean) supplies a native-model instance. The corollary quantifies over every reasonable general model and a model-dependent polynomial simulation bound. No formal quantification over that informal model class or general compiler transport theorem was located; “reasonable” must become explicit simulation hypotheses. |
| 4.5 | `r2.pdf` / 28 / 144 | **Partial.** [BoundedHalting.lean](../CslibFrontier/Computability/Complexity/Problems/BoundedHalting.lean) proves `BoundedHalting.polyTimeComplete_EXP`, a related binary-clock bounded-acceptance endpoint. No inspected theorem gives the claimed fixed-machine-sensitive lower bound excluding $o((t+\|x\|)f(M)/\log^2(t+\|x\|))$ for universal output evaluation. EXP-completeness and a hierarchy separation do not themselves record this exact quantitative interpreter lower bound; coordinate with [#800](https://github.com/cslib-community/cslib-frontier/issues/800) and [#4211](https://github.com/cslib-community/cslib-frontier/issues/4211). |
| 4.6 | `r2.pdf` / 29 / 145 | **Partial.** `NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le` in [NondeterministicTime.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/NondeterministicTime.lean) gives separation when $6d+14\le e$. The source allows $t_2(n)\ge t_1(n+1)\log^2 t_1(n+1)$ for monotone constructible $t_1>n$. The sharp arbitrary-function endpoint and precise two-tape convention remain [#4213](https://github.com/cslib-community/cslib-frontier/issues/4213); coarse polynomial separation is not coverage. |
| 4.7 | `r2.pdf` / 31 / 147 | **Partial.** `Cslib.BlumComplexity.BlumMeasure.gap_theorem` in [Gap.lean](../CslibFrontier/Computability/BlumComplexity/Gap.lean) gives a computable strictly increasing $t$ above any computable lower bound with abstract $C_{g\circ t}=C_t$, assuming $g(m)\ge m$. These classes concern total Nat functions and eventual pointwise costs, not native bit-language DTIME with constant-factor budgets. No native time-measure/length-uniform class bridge was located. Abstract gap work is [#2866](https://github.com/cslib-community/cslib-frontier/issues/2866); a native bridge is an additional objective. |
| 4.8 | `r2.pdf` / 33 / 149 | **Partial.** `Cslib.BlumComplexity.BlumMeasure.speedup'` in [Speedup.lean](../CslibFrontier/Computability/BlumComplexity/Speedup.lean) gives a computable Boolean-valued Nat function and, for each program, another faster program with $g(\Phi(c\prime,n))<\Phi(c,n)$ eventually. It is program/input-wise for an abstract Blum measure, not the source’s worst-case string-length DTIME assertion. Transferring code numbering, step cost, lengthwise worst case and multiplicative constants is still required; abstract speed-up is not absent. |
| 4.9 | `r2.pdf` / 34 / 150 | **Covered.** `DSPACE_ssubset_DSPACE` in [Space.lean](../CslibFrontier/Computability/Complexity/Classes/Hierarchy/Space.lean) gives the hierarchy with constructible upper bound, $\log_2 n\le g(n)$ and eventual domination of every $cf+c$. This uses read-only input, write-only output and visited work-cell space, agreeing with Goldreich’s scanned-cell measure (§1.2.3.5, r1 PDF 63 / printed 38), with additive/multiplicative constants absorbed. It realizes the asymptotic space hierarchy in the native arbitrary-fixed-work-tape model. The remaining model qualification is conversion to the draft’s three tapes (one input, one output and one work tape), not a difference of space measures; that compiler is not certified here. |

## Chapter 5: Space Complexity

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342` and Mathlib
`69552756cd8a2d2d48763cf7279fd814d6a1224d`. This is a source-level statement comparison,
not a new Lean build, checked-client proof or whole-library semantic/axiom audit.
Source: `r2.pdf`, January 2007. The scan of chapter text includes the standalone claims 5.7
and 5.9; 5.8 and 5.13 are definitions, not missing theorems. Printed pages are PDF pages plus 116.
Space convention: the library’s `RunPath.space` sums distinct work-head positions visited on
each tape, including blank cells and the initial/final configurations. Input/output tapes and
finite control are excluded. Goldreich’s §5.1.1 (`r2` PDF 41 / printed 157) also counts **scanned**
work cells, then weights them by the logarithm of the fixed alphabet size and charges finite
control. Thus the cell measures coincide for the same run; fixed alphabet/control costs disappear
in asymptotic classes, but not in coefficient-one bounds. This differs from Arora–Barak’s
ever-nonblank convention discussed in [#4766](https://github.com/cslib-community/cslib-frontier/pull/4766).
On blank-initialized tapes, ever-nonblank cells are a subset of visited cells, so membership
upper bounds transfer in that direction. A simulation, completeness result or class equality
needing the reverse direction would remain Partial without a measure bridge; no such reverse
conversion is inferred here. The 13 rows below use Goldreich’s scanned-cell convention and
separately qualify its binary-storage costs and special global/local oracle tapes.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Lemma 5.1 | `r2.pdf` / 43 / 159 | **Partial.** The native visited-cell time/space composition calculus stores intermediate outputs, but no declaration with the displayed binary-space bound $\max(s_1(n),s_2(n+\ell(n)))+\ell(n)+\delta(n)$ was identified. The draft counts binary storage, including control; the library uses fixed finite-control multitape machines and constants in resource bounds. |
| Lemma 5.2 | `r2.pdf` / 44 / 160 | **Partial.** `ComputableInTimeAndSpace.comp_space` in [SmallSpace](../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/Composition/SmallSpace.lean) recomputes intermediate bits with visited-cell space a constant times the sum of the two workspaces and binary lengths of the input/intermediate lengths. It supports logspace composition, but does not assert the draft’s coefficient-one additive bound or its $\delta=o(s)$ refinement. |
| Theorem 5.3 | `r2.pdf` / 46 / 162 | **Partial.** `Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE` in [Space/Time](../CslibFrontier/Computability/Complexity/Classes/Space/Time.lean) yields time $(n+2)2^{cs(n)}$ for some machine-dependent $c$. It assumes a visited-cell bound, which agrees with Goldreich’s scanned-cell measure up to the fixed alphabet/control costs disclosed above. It supplies the exponential consequence, not the exact $n2^{s(n)+\log_2 s(n)}$ bound for the draft’s binary-space accounting. |
| Theorem 5.4 | `r2.pdf` / 52 / 168 | **Covered.** `Cslib.Complexity.CircuitValue.logSpaceComplete` in [CircuitValue/Completeness](../CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean) proves logspace $P$-completeness, with native deterministic machines, explicit circuit codes and encoded inputs. Its logspace reduction counts visited cells; Goldreich also counts scanned cells, so this asymptotic reduction bound transfers with fixed alphabet/control factors. The circuit-value language includes a circuit and its assignment. |
| Theorem 5.5 | `r2.pdf` / 53 / 169 | **Partial.** `CircuitValue.Construction.exists_uniformCircuits` in [CircuitValue/Completeness](../CslibFrontier/Computability/Complexity/Problems/CircuitValue/Completeness.lean) gives polynomial-time generation from unary input length; `computableInLogSpace_tableauInstance` constructs the tableau instance in visited-cell logspace, also a scanned-cell bound in Goldreich’s convention. Neither statement supplies the draft’s strongly explicit local-label/children interface (polynomial time and linear space in the local query encoding). Uniform circuit work is [#4224](https://github.com/cslib-community/cslib-frontier/issues/4224). |
| Theorem 5.6 | `r2.pdf` / 54 / 170 | **Partial.** The draft defines UCONN as whole-graph connectivity immediately before the theorem (`r2` PDF 53 / printed 169). `Cslib.Complexity.USTCON_mem_L` in [LogSpace/USTCON](../CslibFrontier/Computability/Complexity/Classes/LogSpace/USTCON.lean) instead decides reachability between designated vertices. Its visited-cell membership bound supplies the corresponding scanned-cell upper bound, but does not identify the whole-graph language. A native whole-graph theorem or encoded iteration bridge, including the empty-graph convention, was not located. |
| Claim 5.7 | `r2.pdf` / 57 / 173 | **Endpoint not located.** The constant-space oracle evaluator for one powering/zig-zag stage, counting the state as storage, was not located as a separate machine theorem. The native visited-cell designated-vertex Reingold endpoint is present; its existence does not establish this specific oracle/control-space contract. |
| Claim 5.9 | `r2.pdf` / 59 / 175 | **Endpoint not located.** The global-tape oracle evaluator with global length $\log_2(d^2|V_{i+1}|)$ and constant local tape was not located. This is a special oracle-tape model, not ordinary visited-cell logspace reducibility. |
| Lemma 5.10 | `r2.pdf` / 60 / 176 | **Endpoint not located.** The global/local-tape recursive composition theorem with space $L+\sum_i(\ell_i+\log_2\ell_i)$ was not located; ordinary visited-cell composition constants do not establish this additive recursion theorem. |
| Theorem 5.11 | `r2.pdf` / 63 / 179 | **Covered.** `Cslib.Complexity.STCON.logSpaceReducible_of_mem_NL` and `logSpaceComplete` in [STCON/Completeness](../CslibFrontier/Computability/Complexity/Problems/STCON/Completeness.lean) cover directed reachability hardness and membership, with `encSTCON` and the native all-branches-halting, visited-cell NL convention. Goldreich’s scanned-cell measure agrees up to fixed alphabet/control costs, so the source-class hardness does not require a reverse ever-nonblank-to-visited conversion. |
| Theorem 5.12 | `r2.pdf` / 64 / 180 | **Covered.** `Cslib.Complexity.NSPACE_subset_DSPACE_sq` in [Space/Nondeterministic/Savitch](../CslibFrontier/Computability/Complexity/Classes/Space/Nondeterministic/Savitch.lean) proves the quadratic-space simulation whenever `Nat.log2 n ≤ s n`; it even removes constructibility, using recognizer simulation. The input and output space classes both count visited cells. Goldreich’s scanned-cell measure agrees up to fixed alphabet/control costs, absorbed by NSPACE/DSPACE; this is not a simulation from an ever-nonblank bound. `NPSPACE_eq_PSPACE` is in [Space/Savitch](../CslibFrontier/Computability/Complexity/Classes/Space/Savitch.lean). This covers the stated inclusion, not the draft’s particular recursive program. |
| Theorem 5.14 | `r2.pdf` / 67 / 183 | **Covered.** `Cslib.Complexity.NL_eq_coNL` in [LogSpace/Complement](../CslibFrontier/Computability/Complexity/Classes/LogSpace/Complement.lean) and `NSPACE_eq_coNSPACE` in [Space/Nondeterministic](../CslibFrontier/Computability/Complexity/Classes/Space/Nondeterministic.lean) cover both the named equality and the subsequent general-space extension. The latter assumes pointwise logarithmic domination, not constructibility; encodings and fixed machine constants are explicit. Both sides count visited cells, agreeing asymptotically with Goldreich’s scanned-cell/binary-space convention; no reverse ever-nonblank measure transfer is assumed. |
| Theorem 5.15 | `r2.pdf` / 72 / 188 | **Covered.** `Cslib.Complexity.TQBF_pspaceComplete` in [Space/TQBF](../CslibFrontier/Computability/Complexity/Classes/Space/TQBF.lean) and `TQBFCNF_pspaceComplete` in [Space/TQBF/Prenex](../CslibFrontier/Computability/Complexity/Classes/Space/TQBF/Prenex.lean) cover general quantified syntax and a prenex-CNF complete language, respectively, with distinct explicit encodings and polynomial-time many-one reductions. Membership uses a visited-cell upper bound; source PSPACE-hardness also transfers because Goldreich counts scanned cells, with fixed alphabet/control factors absorbed by polynomial space. |

## Chapter 6: Randomness and Counting

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342` and Mathlib
`69552756cd8a2d2d48763cf7279fd814d6a1224d`. This is a source-level statement comparison,
not a new Lean build, checked-client proof or whole-library semantic/axiom audit.
Source: `r3.pdf`, February 2007. Printed pages are PDF pages plus 202. The 19 numbered
results include propositions whose extracted headings split “Proposition” into “Prop osition”.
Promise-problem error orientation, expected versus bounded time, binary count outputs and
self-reduction assumptions are material to this comparison.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Theorem 6.3 | `r3.pdf` / 9 / 211 | **Covered by subsequent formalization.** `Cslib.Circuits.Boolean.BPP_ssubset_PPoly` in [NonuniformSeparation](../CslibFrontier/Computability/Circuit/Boolean/NonuniformSeparation.lean) proves strict containment on ordinary bit languages under `encBits`. Its reusable `exists_mem_PPoly_not_isDecidable` supplies an undecidable circuit language, using uncountably many P-selective sets and Ko’s theorem; BPP decidability follows through the existing PH/PSPACE/EXP inclusions. This is a nonconstructive class separation, with no efficient separator. [Clients](../CslibFrontierTests/NonuniformSeparation.lean) check that finite instance domains instead have BPP = P/poly, preventing that invalid generalization. |
| Proposition 6.5 | `r3.pdf` / 10 / 212 | **Source issue.** The oracle specification immediately below the proposition asks for a square root $r<s/2$ of the residue $s$ modulo prime $P$. For $P=5,s=1$, the roots are 1 and 4; neither satisfies $r<1/2$. Construction 6.4 instead requests the smaller root (bounded by $P/2$). The intended primality-to-promised-square-root randomized reduction was not located; existing primality algorithms do not certify this reduction. |
| Lemma 6.8 | `r3.pdf` / 12 / 214 | **Covered.** `schwartz_zippel_totalDegree_fintype` in [SchwartzZippel](../CslibFrontier/Foundations/Data/MvPolynomial/SchwartzZippel.lean) bounds the zero fraction by total degree divided by sample-set cardinality over an integral domain. Taking a finite field and its full universe yields the draft’s $d/|F|$ bound; the nonzero hypothesis is present. |
| Theorem 6.9 | `r3.pdf` / 13 / 215 | **Partial.** [Promise/Probabilistic](../CslibFrontier/Computability/Complexity/Classes/Promise/Probabilistic.lean) defines PromiseBPP/PromiseCoRP and [Promise/Randomized](../CslibFrontier/Computability/Complexity/Classes/Promise/Randomized.lean) defines one-sided randomized reductions. The specific PromiseBPP-to-PromiseCoRP Karp reduction was not located. The draft requires zero error on no-instances; the library’s uncomplemented `RPReducible` uses the opposite orientation, so the name alone cannot establish coverage. The total-language Sipser–Lautemann containment is a different endpoint. |
| Theorem 6.10 | `r3.pdf` / 17 / 219 | **Covered.** `Cslib.Complexity.ZPP_eq_RP_inter_coRP` in [ZPP](../CslibFrontier/Computability/Complexity/Classes/ZPP.lean) proves the equality for bounded polynomial-time partial-answer algorithms. The draft’s definition immediately above 6.10 has exactly this convention: every answer is correct, failure is allowed, and an answer is returned with probability at least $1/2$. This matches `DecidesWithZeroError`, with `none` representing failure. Expected polynomial time appears only as an alternative definition on PDF 18 / printed 220; its bridge remains separate work proposed in [#4767](https://github.com/cslib-community/cslib-frontier/pull/4767), not a gap in 6.10. |
| Proposition 6.13 | `r3.pdf` / 20 / 222 | **Endpoint not located.** The $O(|V||E|)$ cover-time/high-probability traversal bound for a simple undirected graph was not located. Expander hitting estimates are different statements. Classical random-walk USTCON work is already within [#459](https://github.com/cslib-community/cslib-frontier/issues/459) (M2), with [#1444](https://github.com/cslib-community/cslib-frontier/issues/1444) first in its current sequencing. |
| Proposition 6.15 | `r3.pdf` / 21 / 223 | **Partial.** [Oracle/ThresholdSearch](../CslibFrontier/Computability/Complexity/Classes/Oracle/ThresholdSearch.lean) exposes `computableInPolyTimeWithOracleQueries_bisect` for certified bounded monotone predicates. A complete specialization to binary-output arbitrary #P functions and the language $f(x)\ge N$, including both oracle directions and count bit bounds, was not located. This generic bisection infrastructure should be reused. |
| Theorem 6.16 | `r3.pdf` / 22 / 224 | **Covered.** `Cslib.Complexity.PH_subset_PWithSharpPOracle` in [Toda](../CslibFrontier/Computability/Complexity/Classes/Toda.lean) proves Toda’s containment. Its oracle answers bits of one SharpP function, with encoded queries and polynomial time; reconstructing a polynomial-bit count is the usual full-value interface interpretation, not unit-cost unbounded integer arithmetic. |
| Theorem 6.18 | `r3.pdf` / 22 / 224 | **Partial.** `Cslib.Complexity.SharpSAT_sharpPComplete` in [CookLevin/Counting](../CslibFrontier/Computability/Complexity/CookLevin/Counting.lean) and `SharpPHard.trans` in [SharpP/Completeness](../CslibFrontier/Computability/Complexity/Classes/SharpP/Completeness.lean) provide count-preserving completeness and transfer. The draft quantifies over PC search relations and solution-bijection reductions; the general relation-to-count interface and its transfer theorem were not located. |
| Theorem 6.19 | `r3.pdf` / 23 / 225 | **Partial.** [SharpDNF](../CslibFrontier/Computability/Complexity/Problems/SharpDNF.lean) has efficient relative approximation, and [SharpSAT](../CslibFrontier/Computability/Complexity/Problems/SharpSAT.lean) has exact #P membership. The existence of a #P-complete count attached to a polynomial-time solvable search relation (e.g. DNF) still needs its nonparsimonious counting hardness and search certificate; those were not located. Approximation alone is not exact-count hardness. |
| Theorem 6.20 | `r3.pdf` / 23 / 225 | **Endpoint not located.** Boolean permanent/bipartite perfect-matching #P-completeness under counting reductions was not located. Arithmetic VNP membership and [#321](https://github.com/cslib-community/cslib-frontier/issues/321)’s VNP-hardness objective use another class and reduction. The same verified gap is proposed in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769); deduplicate there. |
| Proposition 6.21 | `r3.pdf` / 24 / 226 | **Endpoint not located.** The explicit integer-matrix reduction with $\operatorname{perm}(M)=c^m\#3\mathrm{SAT}(\varphi)$ for fixed even $c$ and fixed finite entry set was not located. Formula-to-permanent projections do not by themselves give this count-preserving weighted gadget construction. Batch with the permanent counting proposal in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769). |
| Proposition 6.22 | `r3.pdf` / 24 / 226 | **Endpoint not located.** The polynomial-time conversion of a binary integer matrix to a 0/1 matrix, recovering the former permanent from the latter, was not located. Negative weights, magnitude encoding and output recovery all matter. This is another milestone of the permanent proposal in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769). |
| Proposition 6.23 | `r3.pdf` / 31 / 233 | **Partial.** Finite sampling/concentration is available in [Probability/Chernoff](../CslibFrontier/Probability/Chernoff.lean). The generic PC-relation additive estimator, scaled by $2^{\ell(|x|)}$, with native polynomial time in input length and $\log(1/\delta)$, was not located as a complete theorem. A probability estimate alone omits sampling, membership-testing and rational-output costs. |
| Proposition 6.26 | `r3.pdf` / 33 / 235 | **Covered.** `Cslib.Complexity.SharpDNF.mem_FPRAS`, `isFPRAS` and `approx_estimate` in [SharpDNF](../CslibFrontier/Computability/Complexity/Problems/SharpDNF.lean) establish native relative approximation of DNF model counts, including zero counts; unary inverse-accuracy/confidence parameters replace informal real inputs. This is the endpoint of [#2858](https://github.com/cslib-community/cslib-frontier/issues/2858), not necessarily the same estimator as Construction 6.25. |
| Theorem 6.27 | `r3.pdf` / 33 / 235 | **Partial.** `one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate` in [ApproximateCounting/Relative](../CslibFrontier/Probability/ApproximateCounting/Relative.lean) proves the finite relative-accuracy hashing guarantee. The full native randomized polynomial-time NP-oracle algorithm was not located; ROADMAP explicitly retains the oracle-algorithm form. Polynomial query construction, answer access, estimation arithmetic and negligible-error schedules remain to be certified. |
| Theorem 6.29 | `r3.pdf` / 37 / 239 | **Partial.** `Cslib.Complexity.NP_subset_RPWithPromiseOracle_PromiseUSAT` in [ValiantVazirani](../CslibFrontier/Computability/Complexity/Classes/ValiantVazirani.lean) and the concrete [Reduction](../CslibFrontier/Computability/Complexity/Classes/ValiantVazirani/Reduction.lean) supply SAT isolation and decision simulation, preserving unsatisfiability and allowing arbitrary off-promise answers. The draft’s general parsimoniously complete PC relation and search-output reduction were not located. Its inverse-polynomial success does not demand the sharper Arora–Barak constant proposed in [#4769](https://github.com/cslib-community/cslib-frontier/pull/4769). |
| Theorem 6.31 | `r3.pdf` / 41 / 243 | **Partial.** `Cslib.Complexity.SelfReducible.mem_FPAUS_iff_mem_FPRAS` in [FPAUS/OfFPRAS](../CslibFrontier/Computability/Complexity/Classes/FPAUS/OfFPRAS.lean) proves class equivalence for one-bit self-reducible families. The draft assumes a strong parsimonious prefix reduction and states fixed-accuracy oracle reductions with $1/(5\ell)$ and $\epsilon/(7\ell)$; neither the bridge from that assumption nor these exact interfaces was located. [#3039](https://github.com/cslib-community/cslib-frontier/issues/3039) owns the original sampling-to-counting milestone. The converse is now present despite that issue’s historical remaining-work text. |
| Proposition 6.33 | `r3.pdf` / 46 / 248 | **Partial.** [FPAUS/ExactSampler](../CslibFrontier/Computability/Complexity/Classes/FPAUS/ExactSampler.lean) has `SelfReducible.exactSample_eq_uniformWitness` for exact-count conditional sampling, and bounded oracle-PPT samplers within total variation $2^{-q}$. It does not implement Construction 6.32’s NP-oracle hashing/enumeration sampler for every PC relation, whose successful outputs are exactly uniform and whose failure probability is separately bounded. An exact-count oracle is stronger than the NP oracle here; a capped approximate sampler does not establish exact conditional uniformity. |

## Chapter 7: The Bright Side of Hardness

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342` and Mathlib
`69552756cd8a2d2d48763cf7279fd814d6a1224d`. This is a source-level statement comparison,
not a new Lean build, checked-client proof or whole-library semantic/axiom audit.
Source: **`r4.pdf`, March 2007, preferred over the overlapping earlier `r3.pdf` chapter 7**.
Printed pages are PDF pages plus 264. The table has 15 main results and six proof-internal
claims. Internal claims are retained for traceability, not counted as independent missing
research objectives. Eventual hardness means all sufficiently large lengths; it is not replaced
by infinitely-often hardness or by uniform algorithmic hardness.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Proposition 7.2 | `r4.pdf` / 5 / 269 | **Partial.** [OneWay](../CslibFrontier/Crypto/Computational/OneWay.lean) defines uniform one-wayness; related distributional search infrastructure is in [AverageCase](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Distributional.lean). The equivalence with efficiently generating solved intractable instances of an NP relation was not located. It needs the generator’s joint instance/witness distribution and the random-coin-length reindexing, not merely worst-case NP hardness; coordinate with [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865). |
| Theorem 7.5 | `r4.pdf` / 7 / 271 | **Covered.** `Cslib.Crypto.WeakOneWay.exists_oneWay` and `exists_oneWay_iff_exists_weakOneWay` in [OneWay/Amplification](../CslibFrontier/Crypto/Computational/OneWay/Amplification.lean) prove weak-to-strong amplification against uniform PPT inverters. Fixed-output-length normalization and reindexing handle every input length, rather than only exact product lengths. This does not claim the nonuniform variant mentioned separately in the chapter. |
| Claim 7.5.1 | `r4.pdf` / 8 / 272 | **Partial.** Not separately mapped: this proof-internal success estimate uses the draft’s good-input set and inverter construction. The parent existential amplification endpoint is covered, but its proof does not expose this exact auxiliary contract. |
| Claim 7.5.2 | `r4.pdf` / 8 / 272 | **Partial.** Not separately mapped: the high density of the draft’s good-input set belongs to its particular reduction. Covered parent 7.5 does not certify equality with that construction. |
| Theorem 7.7 | `r4.pdf` / 12 / 276 | **Covered.** `Cslib.Crypto.GoldreichLevin.padded_hardCore` in [GoldreichLevin/HardCore](../CslibFrontier/Crypto/Computational/GoldreichLevin/HardCore.lean) gives parity as a hard-core predicate for padded $(x,r)\mapsto(f(x),r)$ against uniform PPT. The implementation splits even/odd total lengths and handles the spare bit; dot-product and list-pair conventions are explicit. It is not an unpadded hard-core predicate for $f$ itself. |
| Theorem 7.8 | `r4.pdf` / 15 / 279 | **Partial.** [GoldreichLevin/Decoding](../CslibFrontier/Crypto/Computational/GoldreichLevin/Decoding.lean) has `decode_failure_le_half` for a fixed target; [WordDecoder](../CslibFrontier/Crypto/Computational/GoldreichLevin/WordDecoder.lean) has `polyTime_wordCandidates` and `wordDecode_success_ge_half` for efficient supplied predictors/functions. A single polynomial-time oracle machine simultaneously listing **all** correlated strings, with the optional exclusion of low-correlation strings, was not located. A per-target success event of probability one half is not a simultaneous guarantee. |
| Theorem 7.10 | `r4.pdf` / 18 / 282 | **Partial.** [HardnessAmplification/WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean) supplies finite reconstruction and [XorLemma](../CslibFrontier/Computability/Circuit/Boolean/XorLemma.lean) supplies finite amplification. The complete almost-everywhere polynomial-hardness family theorem in E, with the quantifier $\forall p\,\exists f$, was not located. The exponential premise of 7.19 is stronger. Coordinate with the general-hardness proposals in [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768). |
| Theorem 7.12 | `r4.pdf` / 21 / 285 | **Partial.** `Cslib.Circuits.Boolean.complexity_le_pow_of_agree_hardnessEncode` in [WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean) gives a quantitative finite Reed–Muller/Hadamard reconstruction bound. The exact general-$S$ family of length-nonexpanding multi-output functions with failure $>1/n^2$ and E evaluation was not located. [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768) already proposes general-$S$ worst-case/average-case schedules. |
| Theorem 7.13 | `r4.pdf` / 22 / 286 | **Partial.** `Cslib.Circuits.Boolean.card_eq_xorPower_div_le` in [XorLemma](../CslibFrontier/Computability/Circuit/Boolean/XorLemma.lean) and `isAverageCaseHard_xorPower` in [HardnessAmplification](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification.lean) give finite XOR bounds with explicit hard-core iteration/size hypotheses. The draft’s full family tradeoff $p_1(n)^{1/c}/t(n)^c$, also for arbitrary integer functions, was not derived here; the sharp size-tradeoff proposal in [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768) should own this qualification. |
| Theorem 7.14 | `r4.pdf` / 23 / 287 | **Partial.** [DirectProduct/Decode](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/DirectProduct/Decode.lean) exposes `card_filter_dpDecode_err_le_ge`; [DirectProduct/Complexity](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/DirectProduct/Complexity.lean) bounds Boolean decoder circuits via `complexity_dpDecode_le`. The arbitrary multi-output $f$, circuit-family direct-product theorem and full polynomial parameter transport were not located as a single endpoint. Do not infer this interface from OWF amplification, which can verify preimages. |
| Lemma 7.15 | `r4.pdf` / 24 / 288 | **Partial.** The same [direct-product decoder](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/DirectProduct/Decode.lean) supplies quantitative recovery ingredients. The asymmetric two-function theorem for arbitrary independent ensembles, retaining the first factor’s size bound without loss, was not located. |
| Claim 7.15.1 | `r4.pdf` / 26 / 290 | **Partial.** Not separately formalized under this mapping: fixing the second input yields the first-component bound in the proof of 7.15. This is an auxiliary consequence of its circuit/ensemble conventions, not the complete direct-product theorem. |
| Claim 7.15.2 | `r4.pdf` / 27 / 291 | **Partial.** Not separately mapped: the draft’s sample-and-weight circuit contradicting the second success bound depends on its asymmetric 7.15 construction. Existing decoder error bounds do not identify that circuit. |
| Proposition 7.16 | `r4.pdf` / 29 / 293 | **Partial.** [WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean) reconstructs from agreement with a concrete encoding, but the displayed arbitrary-$S$, arbitrary-$\epsilon$ multi-output family theorem was not located. Footnote 17 explicitly acknowledges impossible exact field/grid cardinalities for some parameters; integer rounding and padding must be specified before formalizing that construction. This is included in the general-$S$ proposal in [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768). |
| Theorem 7.18 | `r4.pdf` / 31 / 295 | **Source issue.** The definition $g(z)=g_{m^{-1}(|z|)}(z)$ is not total under the stated injectivity-only assumption on $m$. Its own example $\ell(N)=N^3$ gives $m(n)=3n$, so lengths $3k+1$ have no inverse. Pad/extend off-image lengths, and translate eventual hardness accordingly, before stating a Boolean-string function. Finite reconstruction exists in [WorstCase](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/WorstCase.lean); the general implicit-code compiler remains unmapped. |
| Theorem 7.19 | `r4.pdf` / 32 / 296 | **Covered.** `Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice` in [Schedule](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/Schedule.lean) gives eventual average-case hardness $2^{\lfloor N/c\rfloor}$ from eventual worst-case exponential De Morgan circuit hardness. `encodedLanguage_mem_E` in [HardnessEncoding/PolyTime](../CslibFrontier/Computability/Complexity/HardnessEncoding/PolyTime.lean) supplies E membership. The library uses agreement at most $1/2+1/s$, while the draft uses correlation at most $1/T$; reduce the output exponent to absorb the factor two and obtain strict eventual slack. Together these establish the existential exponential endpoint with explicit padding and rounding; they do not prove the separate derandomized-XOR lemmas below. |
| Theorem 7.21 | `r4.pdf` / 34 / 298 | **Partial.** `Cslib.Circuits.Boolean.exists_isHardCoreMeasure` in [HardCore](../CslibFrontier/Computability/Circuit/Boolean/HardCore.lean) supplies a weighted hard core for uniform bitstrings with explicit finite circuit losses. The draft allows arbitrary ensembles and asks for a restricted region of relative density $(1-o(1))\rho$; weighted uniform cores do not establish this. Set rounding is related to [#3557](https://github.com/cslib-community/cslib-frontier/issues/3557); general ensembles and asymptotic near-full density remain separate. |
| Claim 7.21.1 | `r4.pdf` / 34 / 298 | **Partial.** The weighted-core API above is a related uniform finite specialization. The draft’s dominated arbitrary-ensemble distribution with the stated family size guarantee is not separately mapped. |
| Claim 7.21.2 | `r4.pdf` / 35 / 299 | **Partial.** The dominated-to-critical-distribution/region step is not separately mapped. Footnote 25 already allows one exceptional atom; the exact critical-distribution restriction is not automatic in an atomic distribution. Weighted-core existence alone does not supply this rounding theorem. |
| Lemma 7.22 | `r4.pdf` / 37 / 301 | **Partial.** [GLAmp](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/GLAmp.lean) defines the independent-block parity construction, and [GLAmpDecode](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/GLAmpDecode.lean) has `dens_filter_glAmpCandidate_agree`. The **pairwise-correlated** block generator and family hardness gain $\Omega(n\rho)$ with linear input-length blowup were not located as this derandomized-XOR endpoint. Independent repetition is a different distribution. |
| Lemma 7.23 | `r4.pdf` / 38 / 302 | **Partial.** [Schedule](../CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/Schedule.lean) proves the final exponential worst-case/average-case consequence by a code-based route. It does not expose the draft’s constant-to-strong amplification using an exponential-time generator on linearly many seed bits, for a general hardness function $T$. A matching standalone derandomized-XOR theorem was not located. |

### Search scope and interpretation

The chapter scans used the glyph-reconstructed text for all three chapter ranges. An independent
scan of PDF glyph spans, grouped by baseline and ordered horizontally, checked result-label line
starts in `r2` pages 39–84, `r3` pages 1–64 and `r4` pages 1–50. It recovered Proposition 6.33,
which the first heading inventory missed, and checked propositions, proof claims and exercises; cross-references were excluded from
the inventory. Six rendered pages were additionally inspected for ambiguous formulae and
models (`r2` 43; `r3` 10, 13; `r4` 24, 31, 34). The three PDF digests match #4772.
This yields 47 main numbered results and six internal claims, more than the initial approximate
heading count. Definitions and constructions are not counted as results.

Searches used tracked Lean sources in the modules linked above and their neighboring machine,
probability, counting, circuit and crypto APIs. A same-revision CSLib checkout was also searched for Stockmeyer, Goldreich, hard-core, Savitch
and #P names; Mathlib searches included Schwartz–Zippel, cover time and Goldreich. These limited
searches do not assume dependencies supply a textbook endpoint merely because their mathematics
is general. “Endpoint
not located” is a qualified search result, not proof of semantic absence. “Partial” can mean a
missing client/interface or an unverified parameter derivation; it need not require a new proof.
No claim of full PDF visual inspection or exhaustive dependency search is made.

Open and closed issue searches checked endpoint names and related terms (Stockmeyer, DNF,
threshold oracles, cover time, primality/square roots, Goldreich–Levin, amplification and uniform
generation). The sibling Arora–Barak audit PRs #4764, #4766–#4770 were checked for proposed work.
In particular, permanent counting, expected-time ZPP, general-hardness schedules and sharp XOR
tradeoffs should be deduplicated with those proposals; none is opened as a new issue here.
The final exponential hardness endpoint is present even though several alternative-proof
auxiliaries are not mapped. Existing theorem statements, not historical issue checklists,
determine coverage.

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
| 8.22 | `r4.pdf` / 86 / 350 | **Endpoint not located.** Nisan–Zuckerman polynomial stretch with linear space $s(k)=k/O(1)$ and distinguishing error $2^{-\sqrt{s}}$, subexponential in space (and seed length), including linear-space/polynomial-time generation. Nisan’s seed proportional to space times log output is a different tradeoff. Consult extractor track [#895](https://github.com/cslib-community/cslib-frontier/issues/895); no dedicated endpoint owner located. |
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
`OneWay.exists_zkProof_of_npRelation`: the latter's generable-family guarantee
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

## Chapter 10: Relaxing the Requirements

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
CSLib `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342`, Mathlib
`69552756cd8a2d2d48763cf7279fd814d6a1224d`. The 16 numbered propositions and theorems
in r5, PDF 75–124 / printed 457–506, are catalogued below; definitions and exercises
are excluded. Headings were checked against the glyph-position text and an independent PDF label scan, with rendered-page
checks of the approximation statements and their parameter conventions. Searches used
`git grep` on the snapshot, the pinned dependencies, the results registry, ROADMAP and
open/closed issues and PRs, including the sibling Arora–Barak audits #4764–#4770.
“Endpoint not located” is a qualified search result, not a semantic absence theorem.
No Lean build, new checked client or whole-library axiom audit was performed.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Proposition 10.2, vertex-cover 2-approximation | r5 / 76–77 / 458–459 | **Covered.** `Cslib.Complexity.VertexCover.isCover_approxCover`, `length_approxCover_le_two_mul_vertexCoverNum` and `computableInPolyTime_approxCover` in [VertexCover/Approximation](../CslibFrontier/Computability/Complexity/Problems/VertexCover/Approximation.lean) give feasibility, factor two and native polynomial time. The input is an explicit finite graph with declared binary-natural vertices; loops are discarded by its simple-graph semantics. |
| Theorem 10.3, metric and Euclidean TSP | r5 / 77 / 459 | **Partial.** `Cslib.Complexity.TSP.christofidesTour_perm` and `two_mul_tourLength_christofidesTour_le_three_mul` in [TSP/Christofides](../CslibFrontier/Computability/Complexity/Problems/TSP/Christofides.lean) prove the 3/2 ratio on natural-valued metric matrices, but the matching step is exhaustive and has no polynomial-time certificate. [#3055](https://github.com/cslib-community/cslib-frontier/issues/3055) explicitly leaves that runtime continuation out of scope. No fixed-dimensional Euclidean approximation scheme was located. The PDF literally says $\epsilon>1$ in part 2; that weaker range does not express the PTAS described immediately afterward. |
| Theorem 10.5, almost-linear clique gap | r5 / 78 / 460 | **Partial.** `Cslib.Complexity.GapClique_npHard` in [IndependentSet](../CslibFrontier/Computability/PCP/Approximation/IndependentSet.lean) proves only a fixed gap relative to an input target $k$. It does not supply size-dependent thresholds $L(N)=N^{1-o(1)}$, $s(N)=N^{o(1)}$. Coordinate with [#886](https://github.com/cslib-community/cslib-frontier/issues/886) and the independent-set gap-amplification proposal in [#4770](https://github.com/cslib-community/cslib-frontier/pull/4770); that proposal is not already the full almost-linear gap. |
| Proposition 10.6, gap-to-approximation reduction | r5 / 79 / 461 | **Source issue.** Definition 10.4 permits real-valued thresholds with $g_2=0$ (maximization) or $g_1=0$ (minimization), so the displayed approximation factors need not be defined. Even nonzero thresholds need positivity to justify the division argument and a factor at least one. A corrected positive-threshold generic decision-to-search reduction was not located; problem-specific gap reductions do not establish it. |
| Theorem 10.7, vertex-cover gap above 4/3 | r5 / 79 / 461 | **Partial.** `Cslib.Complexity.GapVertexCover_npHard` in [IndependentSet](../CslibFrontier/Computability/PCP/Approximation/IndependentSet.lean) gives factor $1+1/(3\cdot2^{78})$, not fixed vertex-density thresholds $s,L$ with $L>4s/3$ (the source suggests $s=0.62,L=0.84$). Optimal linear-test/Label Cover work [#886](https://github.com/cslib-community/cslib-frontier/issues/886) is related, not this reduction. |
| Theorem 10.8, optimal MAX-3SAT gap | r5 / 79 / 461 | **Source issue; partial for the intended positive range.** The literal “every $v<1/8$” includes $v=0$: every satisfiable nonempty 3-CNF then lies on both sides of the promise defined in 9.20 (every assignment violates at least zero clauses). Require $0<v<1/8$. `Cslib.Complexity.GapThreeSAT_npHard` in [MaxThreeSAT](../CslibFrontier/Computability/PCP/Approximation/MaxThreeSAT.lean) has only the fixed tiny gap $1/(3\cdot2^{77})$, not every such $v$; [#328](https://github.com/cslib-community/cslib-frontier/issues/328) and [#886](https://github.com/cslib-community/cslib-frontier/issues/886) own the optimal-hardness continuation. |
| Theorem 10.9, optimal linear-equation gap | r5 / 80 / 462 | **Source issue; partial for a corrected range.** For $\epsilon=1$, the literal thresholds $1-\epsilon,1/2+\epsilon$ put every system on both sides of the promise. Restrict the claim, for example to $0<\epsilon<1/4$. `Cslib.PCP.Hastad.gapLabelCover_dichotomy_lt_one` in [Hastad](../CslibFrontier/Computability/PCP/Approximation/Hastad.lean) proves the long-code test's completeness/soundness dichotomy, not the full encoded gapLin hardness reduction; [#886](https://github.com/cslib-community/cslib-frontier/issues/886) owns that continuation. |
| Theorem 10.12, dense graph testers and lower bound | r5 / 84 / 466 | **Partial.** `Cslib.DenseGraphTesting.oneSidedTestable_isBipartite` in [Bipartite](../CslibFrontier/Computability/PropertyTesting/DenseGraph/Bipartite.lean) covers the $k=2$ query guarantee. The higher-colorability, dense clique/independent-set, cut/bisection testers, polylogarithmic machine-time implementations and existential linear-time NP-property lower bound were not located. [#3118](https://github.com/cslib-community/cslib-frontier/issues/3118), [#3036](https://github.com/cslib-community/cslib-frontier/issues/3036) and [#3180](https://github.com/cslib-community/cslib-frontier/issues/3180) concern dense-model foundations and particular/canonical testers, not all these endpoints. |
| Theorem 10.13, bounded-degree graph testers | r5 / 85–86 / 467–468 | **Endpoint not located.** Bounded-incidence-list connectivity in polylogarithmic time, bipartiteness in $\widetilde O(\sqrt N)$ time and its $\Omega(\sqrt N)$ lower bound for suitable fixed degree/distance. Dense adjacency-matrix testers use a different oracle and distance normalization. Searches checked property-testing modules and the graph-testing issues above. |
| Theorem 10.17, distNP completeness | r5 / 94 / 476 | **Covered, with explicit distribution convention.** `Cslib.Complexity.BoundedHalting.distComplete_problem` in [Completeness](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Completeness.lean) exhibits a DistNP-complete problem under deterministic many-to-one distributional reductions with polynomial pointwise domination. [Ensemble](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Ensemble.lean) uses length-exact distributions with an exactly rational polynomial-time CDF; the bounded-halting target uses framed machine/input headers and unary clock padding, not the draft's particular universal language. This covers the existential completeness claim, not the later tpcBPP consequences. |
| Proposition 10.18, monotone length-regular transfer | r5 / 99–100 / 481–482 | **Partial.** `Cslib.Complexity.DistReducible.trans` in [Reduction](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Reduction.lean) composes supplied distributional reductions. No theorem constructs a simple pushforward ensemble and efficient inverse from the source's strictly lexicographically monotone, length-regular Karp map. Existing completeness alone does not supply that CDF computation. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) is the average-case umbrella. |
| Theorem 10.19, Karp's 21 problems | r5 / 101 / 483 | **Endpoint not located.** Simple ensembles making each of Karp's 21 named problems distNP-complete. Worst-case NP-completeness and bounded-halting distributional completeness do not establish the required monotone marking/pushforward construction for the 21 encodings. Related umbrella: [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865). |
| Proposition 10.21, randomized uniform-ensemble target | r5 / 101 / 483 | **Partial.** Distributional bounded-halting completeness exists, but its target distribution is `uniformBH`, not the perfectly uniform ensemble on all words of a length. No randomized reduction of every distNP problem to a fixed NP language under that uniform ensemble was located. See [Completeness](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Completeness.lean) and [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865). |
| Theorem 10.23, distributional search-to-decision | r5 / 103–104 / 485–486 | **Partial.** [Distributional](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Distributional.lean) defines `Cslib.Complexity.DistNP`, `SampNP`, `AvgP` and `HeurP`. It does not state distPC $\subseteq$ tpcBPPF iff distNP $\subseteq$ tpcBPP, or the two distributional search/decision reductions. Confidence-parameter heuristic schemes are not by definition one algorithm with negligible bad-instance mass. Related contract/equivalence work is [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) and [#4764](https://github.com/cslib-community/cslib-frontier/pull/4764). |
| Theorem 10.25, sampNP completeness | r5 / 105 / 487 | **Partial.** `Cslib.Complexity.SampNP` in [Distributional](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Distributional.lean) supplies the class. The theorem deriving a complete sampled ensemble for each NP language admitting nonshrinking Karp reductions was not located. Length-exact sampling requires care when output lengths vary. [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865) explicitly records the samplable extension as remaining work. |
| Theorem 10.26, sampNP versus distNP typical feasibility | r5 / 106–111 / 488–493 | **Partial.** Existing DistNP/SampNP and pointwise domination reductions do not establish the contrapositive tpcBPP containment transfer. The draft explicitly does not claim ordinary randomized reduction of sampNP to distNP. The Impagliazzo–Levin continuation is recorded in [#2865](https://github.com/cslib-community/cslib-frontier/issues/2865); the current [Completeness](../CslibFrontier/Computability/Complexity/Classes/AverageCase/Completeness.lean) is only for polynomial-time computable CDFs. |

The average-case mapping deliberately separates existence of a complete distributional problem
from the class of algorithms used to solve it. The Lean completeness theorem uses native polynomial
time and explicit encodings; no equivalence with the draft's negligible exceptional-input,
randomized typical-time convention is inferred from the shared name “average-case.”

## Appendix A: Glossary of Complexity Classes

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12).
Appendix A is r6, PDF 1–8 / printed 509–516. It gives definitions and discussion of
algorithmic and nonuniform complexity classes, not numbered Theorem/Proposition/Lemma/
Corollary/Claim/Fact results. There are therefore no result rows or coverage counts here.
This is not a claim that all glossary definitions have matching Lean conventions; in particular,
its opening promise-problem convention must not be silently identified with language-only classes.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| No numbered results | r6 / 1–8 / 509–516 | Scope note only; glossary definitions are outside this numbered-result audit. |

## Appendix B: On the Quest for Lower Bounds

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
with the pins and search limits specified under chapter 10. Appendix B is r6, PDF 9–22 /
printed 517–530. Nine numbered results were located; B.2, B.6 and B.7 are explicitly
open problems, and B.1, B.11 and B.12 are definitions. Rendered pages checked the
superscripts and proof-size conventions, which the plain-text extraction loses.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Theorem B.3, monotone CLIQUE lower bound | r6 / 13–14 / 521–522 | **Covered via a source-inspected padding argument.** `Cslib.Circuits.Monotone.two_pow_two_mul_sqrt_lt_size` in [Clique/Asymptotic](../CslibFrontier/Computability/Circuit/Monotone/Clique/Asymptotic.lean) gives size $>2^{2\lfloor\sqrt k\rfloor}$ for $2\le k$, $k^4\le m$, on binary monotone AND/OR/constant circuits over the $\binom m2$ edge bits. Goldreich instead fixes target size $\lfloor\sqrt N\rfloor$ on $N$ vertices. The padding below transfers the bound to that family, yielding $\exp(\Omega(N^{1/8}))$; merely substituting $k=\lfloor m^{1/4}\rfloor$ would not suffice. The parameters $m,N$ count vertices, not input bits. |
| Theorem B.4, PAR and MAJ outside constant depth | r6 / 14 / 522 | **Covered.** `Cslib.Circuits.Boolean.parity_notMem_AC0` in [AC0](../CslibFrontier/Computability/Circuit/Boolean/AC0.lean) and `majority_notMem_AC0` in [Majority](../CslibFrontier/Computability/Circuit/Boolean/Majority.lean) exclude nonuniform polynomial-size constant-depth unbounded-fanin AND/OR/NOT circuits. [Hastad/Sharp](../CslibFrontier/Computability/Circuit/Boolean/Hastad/Sharp.lean), `Unbounded.two_rpow_le_two_mul_size_of_computes_parity_of_depth_le`, supplies the sharper parity bound under explicit positive-depth/size hypotheses; the theorem row does not claim MOD-gate extensions. |
| Theorem B.5, quadratic formula lower bounds | r6 / 15 / 523 | **Covered.** `Cslib.Circuits.Boolean.sq_le_leafSize_of_computes_parity` and `sq_div_four_le_leafSize_of_computes_majority` in [Khrapchenko](../CslibFrontier/Computability/Circuit/Boolean/Khrapchenko.lean) give $n^2$ and $\lfloor(n+1)^2/4\rfloor$ leaves. This is the binary De Morgan formula basis, not arbitrary Boolean gates (a primitive XOR changes parity's complexity); binary-tree leaf and total-node sizes differ by a constant factor. |
| Proposition B.8, factorial polynomial and factoring | r6 / 17 / 525 | **Endpoint not located.** Polynomial-size circuits for $q_d(X)=\prod_{i=1}^d(X+i)$, measured as poly$(\log d)$, imply nonuniform polynomial-size integer-factoring circuits. Existing arithmetic circuit evaluation and separate factoring algorithms do not certify the modular factorial/binary-search reduction. Constant encodings and the arithmetic coefficient domain must be fixed before transferring arithmetic circuits to Boolean circuits. |
| Theorem B.9, power-sum lower bound | r6 / 17 / 525 | **Partial.** `Cslib.Circuits.Circuit.le_three_mul_mulCost_of_psum` in [Gradient](../CslibFrontier/Computability/Circuit/Arithmetic/Gradient.lean) transfers a lower bound on the simultaneous power map to its power sum when the exponent is invertible in the coefficient field. The file explicitly leaves Strassen's $\Omega(n\log n)$ power-map lower bound unformalized; Baur–Strassen differentiation alone does not prove it. [#2906](https://github.com/cslib-community/cslib-frontier/issues/2906) records that continuation. |
| Theorem B.10, subcubic matrix multiplication | r6 / 18 / 526 | **Partial.** `Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_nine_quarters` in [NineQuarters](../CslibFrontier/Computability/Circuit/Arithmetic/MatrixMultiplication/NineQuarters.lean) yields a stronger exponent over characteristic-zero fields, with epsilon slack. B.10 quantifies over every field and uses $n$ for the number of scalar variables ($n$ is proportional to the square of the matrix dimension), asserting $o(n^{3/2})$. [Exponent](../CslibFrontier/Computability/Circuit/Arithmetic/MatrixMultiplication/Exponent.lean), `admissibleExponent_of_rank`, is a generic block-recursion theorem; the full all-characteristic subcubic specialization was not verified here. |
| Theorem B.13, polynomially bounded proof systems | r6 / 19 / 527 | **Partial.** `Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded` in [ProofSystem](../CslibFrontier/Computability/Complexity/ProofSystem.lean) proves the existential Cook–Reckhow equivalence for CNF refutations, with native encoded polynomial time; `coNP_subset_NP_iff_exists_polynomiallyBounded` covers any nonempty decodable coNP-complete set. The draft instead fixes one tautology system $M$ whose polynomial boundedness is equivalent to NP=coNP. A fixed universal system/tautology presentation is not furnished by that existential statement alone. |
| Theorem B.14, Frege versus resolution PHP | r6 / 21 / 529 | **Partial.** `Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole` in [Resolution/Pigeonhole](../CslibFrontier/Logics/Propositional/Resolution/Pigeonhole.lean) gives $2^{\lfloor n/24\rfloor}\le s$ for $(n+1)$-pigeon/$n$-hole refutations, in clause-line size. [Frege](../CslibFrontier/Logics/Propositional/Frege.lean) defines a sound Hilbert-style system, but no polynomial-size Frege PHP proof family was located. The source's total-symbol proof length needs an explicit comparison to line count; [#271](https://github.com/cslib-community/cslib-frontier/issues/271) owns resolution lower bounds and [#3069](https://github.com/cslib-community/cslib-frontier/issues/3069) supplied the basic Frege/simulation API. |
| Theorem B.15, polynomial-calculus PHP | r6 / 22 / 530 | **Partial.** [FunctionalPigeonhole](../CslibFrontier/Logics/Propositional/Algebraic/FunctionalPigeonhole.lean) supplies `Cslib.Logic.PL.Algebraic.algFPHP` and its semantics, not the displayed $2^{n/2}$ size lower bound for every $m>n$ over every field. [#3569](https://github.com/cslib-community/cslib-frontier/issues/3569) explicitly owns the degree/size continuation. Preserve its distinction between ordinary PC, PCR, functional/algebraic PHP, and total monomial size; CNF resolution hardness cannot be substituted. |

### Padding to Goldreich's clique-size regime

For $N\ge25$, put $s=\lfloor\sqrt N\rfloor$, $m=N-s$ and
$k=\lfloor m^{1/4}\rfloor$. Then $2\le k\le s$ and $k^4\le m$, so the cited Lean
theorem applies to $k$-CLIQUE on $m$ vertices. Given such a graph $G$, retain its $m$
vertices, add $s-k$ vertices forming a clique and adjacent to every original vertex,
and add $k$ isolated vertices. The padded graph has exactly $N$ vertices. A $k$-clique
in $G$ extends with all $s-k$ added clique vertices to an $s$-clique. Conversely, an
$s$-clique cannot use an isolated vertex, since $s\ge2$, and uses at most $s-k$ added
clique vertices, so at least $k$ of its vertices form a clique in $G$.

Thus $k$-CLIQUE is a monotone projection of Goldreich's $s$-CLIQUE: original edge
inputs remain variables, edges within the added clique or between it and original vertices
are set to one, and all edges incident to isolated vertices are set to zero. Restricting
an $N$-vertex circuit of size $S$ by this substitution gives an $m$-vertex circuit of size
at most $S+2$, using at most two shared constant gates. Constants are operations of the
library's [monotone basis](../CslibFrontier/Computability/Circuit/Monotone/Basic.lean).
The theorem therefore gives $S+2>2^{2\lfloor\sqrt k\rfloor}$. Since $m=\Theta(N)$ and
$\lfloor\sqrt k\rfloor=\Theta(N^{1/8})$, the additive overhead preserves
$S=\exp(\Omega(N^{1/8}))$, hence the absence of polynomial-size circuits for the exact
source family. This projection and its asymptotic specialization are inspection arguments;
no new Lean bridge or checked client was added under the documentation-only brief.

## Appendix C: On the Foundations of Modern Cryptography

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12),
with the same pinned dependencies. Appendix C is r6, PDF 23–68 / printed 531–576.
It has five numbered theorems; its numerous numbered definitions and unnumbered protocol
claims are not additional theorem rows. Searches read the actual GGM, nonuniform GMW,
Rompel, MAC and encryption contracts. In particular, C.4/C.7 use uniform PPT security,
whereas C.10 expressly assumes nonuniformly hard OWFs.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Theorem C.8, PRFs from PRGs | r6 / 35 / 543 | **Covered.** `Cslib.Crypto.PseudorandomGenerator.exists_pseudorandomFunction` and `.ggm` in [GGM/Security](../CslibFrontier/Crypto/Computational/GGM/Security.lean) prove adaptive uniform strict-oracle-PPT security and efficient evaluation. The arbitrary-stretch existence theorem first stretches/truncates to two labels; `.ggm` needs output length at least $2n$. Keys and queries are $n$-bit words, and surplus bits are ignored. This matches C.7's uniform oracle-machine convention. |
| Theorem C.10, auxiliary-input ZK for NP | r6 / 38 / 546 | **Covered.** `Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_npRelation` in [Nonuniform/ZeroKnowledge](../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean) supplies an honest prover using the relation's own witnesses, negligible soundness $(1/3)^{n+1}$ and auxiliary-input zero knowledge. The language form is `.exists_zkProof_of_mem_NP`; the `ZKProof` API supplies unbounded/instance-indexed auxiliary-input consequences. Native strict PPT is stronger than merely expected polynomial runtime. The completed owning track is [#2316](https://github.com/cslib-community/cslib-frontier/issues/2316); the older uniform generable-input theorem alone would not cover this result. |
| Theorem C.13, private-key CCA encryption from OWFs | r6 / 50 / 558 | **Covered by composition of existing theorems.** `Cslib.Crypto.OneWay.exists_pseudorandomFunction` in [OneWayToPRF](../CslibFrontier/Crypto/Computational/OneWayToPRF.lean), followed by `PseudorandomFunction.indcca_prfEncryptThenMAC` in [EncryptThenMAC](../CslibFrontier/Crypto/Computational/Encryption/EncryptThenMAC.lean), yields a strict-PPT symmetric cipher secure against adaptive CCA. The latter theorem discharges the CPA and strong-MAC hypotheses, rather than assuming secure components exist. The game has explicit challenge-ciphertext exclusion and parameterized equal-length messages. This is a source-inspected consequence, not a newly compiled client. |
| Theorem C.14, public-key CCA from enhanced trapdoors | r6 / 50 / 558 | **Partial.** [Encryption/CCA](../CslibFrontier/Crypto/Computational/Encryption/CCA.lean) supplies CCA notions; Cramer–Shoup, KEM–DEM and other concrete constructions use different hypotheses. No generic construction from the draft's enhanced trapdoor permutations was located. [#1000](https://github.com/cslib-community/cslib-frontier/issues/1000) owns the CCA track, not an automatic equivalence between these assumptions. |
| Theorem C.16, OWFs/signatures/MAC equivalence | r6 / 54 / 562 | **Partial.** `Cslib.Crypto.exists_oneWay_iff_exists_wordSignature` in [Rompel](../CslibFrontier/Crypto/Computational/Rompel.lean) covers uniform stateless signatures on arbitrary-length words. `OneWay.exists_pseudorandomFunction` and `PseudorandomFunction.sufCma_prfMAC` in [MAC](../CslibFrontier/Crypto/Computational/MAC.lean) give secure authentication on the parameterized message domain. The converse from arbitrary secure MACs to OWFs, and a packaged three-way equivalence with the draft's general message convention, were not located. [#1001](https://github.com/cslib-community/cslib-frontier/issues/1001) completed the signature direction; it does not by itself prove the MAC converse. |

## Appendix D: Probabilistic Preliminaries and Advanced Topics in Randomization

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12).
Appendix D is r6, PDF 69–92 / printed 577–600. Four numbered lemmas/theorems occur;
D.1, D.7–D.9 are definitions and D.2–D.3 are constructions. The unnumbered probabilistic
inequalities and sampler discussion are background outside this inventory. Searches checked
pairwise/k-wise hashing, concentration and seeded-extractor modules, not only theorem names.
The useful hashing statements below presume a nonempty source set and a nonempty finite seed
family; formulas dividing by $|S|$ need that convention made explicit.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Lemma D.4, pairwise-independent bucket concentration | r6 / 76 / 584 | **Covered.** `Cslib.Probability.IsPairwiseIndependentHash.dens_filter_le_abs_sub_le` in [PairwiseIndependentHash](../CslibFrontier/Probability/PairwiseIndependentHash.lean) bounds absolute deviation from mean $\mu=|S|/|Y|$ by $\mu/a^2$. Substituting $a=\epsilon\mu$ gives $|Y|/(\epsilon^2|S|)$ for relative deviation; $|Y|=2^m$ gives D.4. The finite-family definition samples seeds uniformly and allows repeated functions, matching a uniformly indexed family. Strict good-event inequalities follow by complementing the weak bad-event inequality. |
| Theorem D.5, leftover hash lemma | r6 / 77–78 / 585–586 | **Covered by a stronger bound.** `Cslib.Probability.IsTwoUniversal.isStrongExtractor` in [Extractor/LeftoverHash](../CslibFrontier/Probability/Extractor/LeftoverHash.lean) gives joint seed/output total variation at most $\tfrac12\sqrt{|Y|2^{-k}}$ for min-entropy $k$, using independent uniform seeds. For a flat source on nonempty $S$, $2^{-k}=1/|S|$. This implies the draft's weaker $2(2^m/|S|)^{1/3}$: if the ratio is at most one use the power inequality, otherwise TV is at most one. The exact cubic-root specialization was not added or compiled. |
| Lemma D.6, high-independence simultaneous bucket concentration | r6 / 79 / 587 | **Partial.** [PairwiseIndependentHash](../CslibFrontier/Probability/PairwiseIndependentHash.lean) proves second-moment bucket estimates; polynomial hash families and k-wise independence are available. No $n$-th-moment theorem giving the displayed simultaneous failure bound $2^m(n2^m/(\epsilon^2|S|))^{n/2}$ was located. The source proof sets $t=n/2$, so a formal statement must handle parity/rounding and degenerate sizes explicitly. Related hashing owner: [#663](https://github.com/cslib-community/cslib-frontier/issues/663). |
| Theorem D.10, short-seed explicit extractors | r6 / 89–90 / 597–598 | **Partial.** [Extractor/Basic](../CslibFrontier/Probability/Extractor/Basic.lean) defines `Cslib.Probability.IsExtractor`/`IsStrongExtractor`; [LeftoverHash](../CslibFrontier/Probability/Extractor/LeftoverHash.lean) supplies universal-hashing constructions, not the asserted $d=O(\log(n/\epsilon))$, near-full output, or $d=(1+\alpha)\log_2 n$, $m=k/\mathrm{poly}(\log n)$ construction. The first source case additionally assumes $\epsilon>\exp(-k^{1-\alpha})$. [#895](https://github.com/cslib-community/cslib-frontier/issues/895) is the extractor umbrella; two-source or affine-disperser results are different contracts. |

## Appendix E: Explicit Constructions

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12).
Appendix E is r6, PDF 93–116 / printed 601–624. Eight numbered results occur, besides
Definitions E.5–E.6. Searches checked code-distance/list-decoding, expander-code and
rotation-map modules, with rendered checks of E.7's inequality and E.10's graph convention.
The library's `RotationMap` counts directed edge slots, permits multiplicity, and normalizes
the walk spectrum by degree; the source uses an unnormalized absolute nontrivial eigenvalue.
These conventions matter for every expander mapping below.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Proposition E.1, random linear-code distance | r6 / 96 / 604 | **Partial.** [Code/Linear](../CslibFrontier/Foundations/Data/Code/Linear.lean) provides linear-code representations and distance infrastructure, but no probability theorem under $n\ge\max(2d,(k+t)/(1-H_2(d/n)))$ giving success $>1-2^{-t}$. Shannon/BSC random-coding results concern decoding error under channel noise, not minimum distance of a uniform binary generator matrix. [#4666](https://github.com/cslib-community/cslib-frontier/issues/4666) concerns codes exceeding Gilbert–Varshamov, a related stronger direction rather than this exact random-linear-code contract. |
| Theorem E.2, explicit good binary linear codes | r6 / 100 / 608 | **Partial.** [Code/Justesen](../CslibFrontier/Foundations/Data/Code/Justesen.lean), `Cslib.Code.isAsymptoticallyGood_justesenCode`, supplies a binary family with rate at least $1/4$ and relative distance at least $1/128$; [Code/Concatenation](../CslibFrontier/Foundations/Data/Code/Concatenation.lean), `Cslib.Code.le_minDist_image_concat`, supplies distance multiplication; [ExpanderCode](../CslibFrontier/Foundations/Data/Code/ExpanderCode.lean) supplies rate/distance and flip-decoding mathematics. No assembled constant-rate, constant-distance family with both native polynomial-time encoder and decoder at the draft's unique-decoding radius was located. [#3278](https://github.com/cslib-community/cslib-frontier/issues/3278) owns the expander-code milestone; a conditional decoder on a supplied graph is not the full explicit-family endpoint. |
| Theorem E.3, locally testable and decodable codes | r6 / 101–102 / 609–610 | **Partial.** `Cslib.Code.minDist_reedMuller` in [ReedMuller](../CslibFrontier/Foundations/Data/Code/ReedMuller.lean) gives distance, and [LocalDecoding](../CslibFrontier/Foundations/Data/Code/LocalDecoding.lean), `Cslib.Code.card_filter_lineDecode_ne_le`, bounds the error of punctured-line recovery, while [ReedMullerDecoding](../CslibFrontier/Computability/Circuit/ReedMullerDecoding.lean) supplies arithmetic circuit-synthesis costs. No assembled explicit family with polynomial alphabet/block length and both polylogarithmic-time local testing and local decoding was located. Polynomial-time encoding, oracle queries and charged local runtime are separate obligations; [#2929](https://github.com/cslib-community/cslib-frontier/issues/2929) supplies local-decoder/query infrastructure, not this combined family/runtime theorem. PCP proximity/low-degree tests alone do not establish it. |
| Lemma E.4, q-ary list-size bound | r6 / 103 / 611 | **Covered by the general agreement inequality.** `Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le` in [Johnson](../CslibFrontier/Foundations/Data/Code/Johnson.lean) proves $M[(q-1)(n-e)^2+e^2-(q-1)n(n-d)]\le(q-1)nd$. With $e/n\le1-1/q-\eta$ and $d/n=1-1/q-\eta_C$, division by the positive denominator gives exactly E.3's ratio $[(1-1/q)^2-(1-1/q)\eta_C]/[\eta^2-(1-1/q)\eta_C]$. The source's E.2 ensures positivity. Integer-radius rounding only strengthens the bound; the weaker library corollary with list size $(q-1)nd$ alone would not establish this ratio. |
| Theorem E.7, vertex expansion versus spectrum | r6 / 105 / 613 | **Source issue.** Part 1 says $G$ is $c$-expanding for $c\ge(d-\lambda(G))/(2d)$, although E.6 demands $|\Gamma(S)|\ge(1+c)|S|$. Take two vertices, one edge between them and one loop at each, with $d=2$ in the source adjacency convention: the eigenvalues are $2,0$, yet $c=2\ge1/2$ fails on a singleton ($2<3$). The inequality must bound $c$ above, not below. [Cheeger](../CslibFrontier/Foundations/Combinatorics/Expander/Cheeger.lean) proves edge-expansion/spectral inequalities, not automatically the source's two vertex-neighborhood constants. |
| Lemma E.8, expander mixing | r6 / 107–108 / 615–616 | **Covered.** `Cslib.RotationMap.abs_card_interedges_sub_le_mul_sqrt` in [Mixing](../CslibFrontier/Foundations/Combinatorics/Expander/Mixing.lean) gives $|e(A,B)-d|A||B|/N|\le d\mu\sqrt{|A||B|}$; set $\mu=\lambda(G)/d$ and divide by $dN$ for E.5. It counts oriented edge slots, so parallel edges and loops require the same multiplicity convention on both sides. The bound also handles overlapping sets; it is not only a disjoint-cut lemma. |
| Lemma E.9, expander walk staying bound | r6 / 108–109 / 616–617 | **Partial.** `Cslib.RotationMap.dens_filter_forall_walkAt_mem_le` in [Hitting](../CslibFrontier/Foundations/Combinatorics/Expander/Hitting.lean), with constant set $W$, gives exactly $\rho(\rho+(1-\rho)\lambda/d)^{\ell-1}$ for $\ell\ge1$, uniform initial vertex and $\ell-1$ slot steps. The same page separately restates Exercise 8.43's varying-set product $\sqrt{\rho_0}\prod_{i=1}^{\ell-1}\sqrt{\rho_i+(\lambda/d)^2}$; that exact nonuniform-density product was not located. The library's common upper-density theorem should not be silently substituted for it. |
| Theorem E.10, degree-eight explicit expanders | r6 / 111 / 619 | **Partial.** `Cslib.RotationMap.secondEigenvalue_shearTranslation_le` in [ShearTranslation](../CslibFrontier/Foundations/Combinatorics/Expander/ShearTranslation.lean) gives a degree-eight graph on $(\mathbb Z/m\mathbb Z)^2$ with normalized second-largest eigenvalue $\le1-1/4096$. The absolute spectral bound is for its lazy version, which changes degree; neither result gives the source's degree-eight absolute bound $7.9999$ and logspace neighbor certificate. Explicitness of a formula is distinct from a native logspace theorem. The source construction is Gabber–Galil, while these moves use separate shears and translations. Coordinate the degree/spectrum/logspace refinements with the strongly explicit expander proposal in [#4768](https://github.com/cslib-community/cslib-frontier/pull/4768), also reused by [#4775](https://github.com/cslib-community/cslib-frontier/pull/4775). |

## Appendix F: Some Omitted Proofs

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12).
Appendix F is r6, PDF 117–136 / printed 625–644. It contains three numbered theorems
and Proposition F.5 inside the proof of F.2; Construction F.4 is not an extra result.
This appendix was included even though the original rough issue inventory mentioned only B–E.
Searches inspected Toda's random-parity representation and the input-dependent IP/AM game APIs.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| Theorem F.1, randomized many-one reduction PH to parity-P | r6 / 118 / 626 | **Covered through the arbitrary-error representation.** `Cslib.Complexity.Toda.exists_isRandomParityRep_alternation` in [Toda/Hierarchy](../CslibFrontier/Computability/Complexity/Classes/Toda/Hierarchy.lean) constructs a native polynomial-time parity verifier with error $2^{-e(n)}$ for every natural polynomial $e$; choosing $e(n)=n$ gives negligible error. Its `IsRandomParityRep` counts fixed-length witnesses with padded, explicitly encoded random strings. `PH_subset_BPOp_ParityP` packages only bounded error, so that theorem alone would omit F.1's negligible-error clause. The target parity verifier may depend on the fixed source language. |
| Theorem F.2, private-to-public coin round efficiency | r6 / 124 / 632 | **Partial.** `Cslib.Complexity.IPPolyRounds_subset_AMPolyRounds` in [IP/Games/PolyRounds](../CslibFrontier/Computability/Complexity/Classes/IP/Games/PolyRounds.lean) proves a stronger $k(n)+2$-move simulation for input-dependent, efficiently generated polynomial game shapes. The library fixes verifier-first alternating patterns, while the source states IP$(f)\subseteq$AM$(f+3)$ for its general message convention. The source allows any polynomially bounded $f$, with no efficient computability hypothesis; exact class-identification/padding for those conventions remains to be supplied. This is not an absent Goldwasser–Sipser theorem. |
| Theorem F.3, polynomial-round linear speedup | r6 / 124 / 632 | **Partial.** [ArthurMerlin/RoundCollapse](../CslibFrontier/Computability/Complexity/Classes/ArthurMerlin/RoundCollapse.lean), `Cslib.Complexity.AMk_eq_AM`, proves the fixed-constant round collapse. [Games/PolyRounds](../CslibFrontier/Computability/Complexity/Classes/ArthurMerlin/Games/PolyRounds.lean) defines input-dependent games but has no AM$(2f)\subseteq$AM$(f+1)$ speedup. [#2950](https://github.com/cslib-community/cslib-frontier/issues/2950) records this larger remaining direction; do not infer it by iterating a constant-pattern theorem polynomially many times. |
| Proposition F.5, soundness of Construction F.4 | r6 / 130 / 638 | **Partial; not separately formalized in the draft presentation.** [IP/Games/PolyRounds](../CslibFrontier/Computability/Complexity/Classes/IP/Games/PolyRounds.lean) proves the soundness needed for its different Goldwasser–Sipser emulation. It does not state F.5's exact accepting-random-tape-set hypothesis $|\mathrm{ACC}_x(\lambda)|<\delta2^\ell$, $\delta=1/p(\ell)$, and conclusion that Construction F.4 accepts with probability $<1/2$. Reproducing this proof-local protocol is optional if the class-level theorem is the desired endpoint; no independent coverage is claimed from the final containment alone. |

## Appendix G: Some Computational Problems

Snapshot: `e39c34b3413b2cd7e08053a14ff8bb36ded4c8dc` (`origin/main`, 2026-11-12).
Appendix G is r6, PDF 137–144 / printed 645–652 (the last page has only its running header);
references begin at PDF 145 / printed 653.
It discusses graphs, propositional formulae, number theory and algebraic problems. There are
no numbered Theorem/Proposition/Lemma/Corollary/Claim/Fact headings. Equation G.1 is a
matrix identity, not a numbered result heading. No claim of complete formalization of this
background or of all its informal assertions is made.

| Draft result | File / PDF page / printed page | Disposition and remaining endpoint |
|---|---|---|
| No numbered results | r6 / 137–144 / 645–652 | Scope note only; background problem definitions are outside this numbered-result audit. |
