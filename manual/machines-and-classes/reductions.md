# Reductions and information access

Reduction interfaces determine which computation may translate instances and how answers from the target problem may be used. Complexitylib separates these choices: total many-one maps, invertible or length-increasing maps, nonadaptive truth tables, adaptive word-oracle programs, and parameter-sensitive resource-transfer rules. Their encodings and query conventions are part of their semantics. This page surveys interfaces rather than enumerating reductions between individual problems. [complexitylib][complexitylib]

## Many-one maps and strengthened interfaces

The shared kernel [`ManyOneReducibleBy`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Reduction/ManyOne.lean#L53) is `∃ f, Good f ∧ ∀ a, a ∈ A ↔ f(a) ∈ B`. It has no built-in machine, encoding, or resource bound. Its composition theorem requires closure of the admissible maps under composition; [`lift`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Reduction/ManyOne.lean#L97) transfers a reduction to representations only when a supplied simulator respects partial decoding, including rejection of undecodable inputs. This generic interface is distinct from Mathlib's computable many-one relation on `Primcodable` types.

[`PolyTimeReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction.lean#L151) instantiates `Good` with a native polynomial-time transducer under source and target encodings. [`LogSpaceReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/LogSpace.lean#L176) uses the native output-uncharged logspace predicate: input and append-only output are not workspace, but producing output consumes time. [`HardUnder`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/ManyOne.lean#L120) and `CompleteUnder` abstract the class-level quantifiers, ranging over source instance types and encodings. They do not impose a hidden universal representation. The Cook–Levin endpoint uses this typed polynomial-time many-one interface, as detailed in [Major endpoints](endpoints-and-hierarchies.md).

Several stronger predicates retain the same membership equivalence while adding computational structure:

| Interface | Additional requirement |
|---|---|
| [`PolyTimeOneOneReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/OneOne.lean#L63), [`LogSpaceOneOneReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/OneOne.lean#L107) | The map is injective, with the indicated native resource bound. |
| [`PolyTimeInvertibleOneOneReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L183) | A total polynomial-time left inverse `g : β → α` satisfies `g(f(a)) = a`. |
| [`PolyTimeLengthIncreasingOneOneReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L254) | The injective map strictly increases encoded length on every input. |
| [`PolyTimeInvertibleLengthIncreasingOneOneReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L311) | Both a total polynomial-time left inverse and strict encoded-length increase. |
| [`PolyTimeIsomorphic`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L116) | An equivalence of the entire ambient instance types, with both directions polynomial time and membership preserved. |

A left inverse is defined even outside the image of the forward map; its behavior there need not recover a meaningful source instance. An isomorphism requires surjectivity as well as injectivity. The isomorphism API proves preservation of [P](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L169) and [NP](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L174) and basic composition laws. It does not turn mutual one-one reducibility into an isomorphism theorem.

## Nonadaptive query batches

[`PolyTimeTruthTableReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTable.lean#L84) uses three total native polynomial-time functions: a count `r(a)`, an indexed query `q(a,i)`, and a Boolean evaluator `d(a,answers)`. The count and index use unary encodings. Before seeing any answers, the reduction determines `q(a,0), …, q(a,r(a)-1)`. The semantic answer word contains the membership bits of those typed target instances; the evaluator receives the original input and that full word. Unary count output makes a polynomially bounded number of queries part of the native contract. Queries outside the used index range do not affect acceptance.

The answer word is a semantic oracle result, not a claim that target membership can be computed without an oracle. [`truthTable_mem_P`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTable.lean#L140) supplies that computation when the target is in `P`. The restrictions below change the permitted query bound or answer combination:

| Polynomial-time predicate | Meaning |
|---|---|
| [`PolyTimeKTruthTableReducible k`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L77) | At most the fixed `k` queries on every input. |
| [`PolyTimeBTTReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L86) | Some single constant `k` bounds all query counts. |
| [`PolyTimeDTTReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L273) | Accept iff at least one query belongs to the target. |
| [`PolyTimeCTTReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L280) | Accept iff every query belongs to the target. |
| [`PolyTimePTTReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L367) | The evaluator is monotone under coordinatewise `false ≤ true`, for every pair of answer words related by `List.Forall₂`. |

Zero queries are allowed. They make the disjunctive predicate false and the conjunctive predicate true; a general evaluator may decide from the original input alone. Composing fixed bounds multiplies them: [`PolyTimeKTruthTableReducible.trans`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L250) gives `k₁k₂`, rather than retaining either bound. Bounded, disjunctive, and conjunctive composition and the embeddings into unrestricted truth-table and Turing reducibility are proved.

The [logspace family](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L113) has all six corresponding predicates: unrestricted truth-table, `k`-truth-table, bounded, disjunctive, conjunctive, and positive. It substitutes native `ComputableInLogSpace` for the count, query generator, and evaluator. Thus the evaluator's space is measured on the encoding of `(a,answers)`, where the answer word is an input, rather than storage automatically supplied to an oracle machine for free. The module explicitly adopts an `L` evaluator and does not claim equivalence to a Boolean-formula/`NC¹` evaluator convention.

The proven [bounded-query closure in L](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L469) and [fixed-bound composition](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L480) preserve this model. All six notions have polynomial-time counterparts. This source does not provide an unrestricted-logspace-truth-table `mem_L` theorem, so the bounded closure result must retain its bounded-query hypothesis.

For a fixed bound with an OR or AND evaluator, import
[`LogSpaceBoundedTruthTable`](../../Complexity/Computability/Complexity/Reduction/LogSpaceBoundedTruthTable.lean).
`LogSpaceKDTTReducible k` and `LogSpaceKCTTReducible k` retain the same unary count and indexed
query generator and require that count to be at most `k` on every input. Their
`logSpaceKTruthTableReducible` lemmas preserve that bound when introducing an explicit evaluator.

## Adaptive word-oracle access

[`PolyTimeTuringReducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L120) defines `A ≤T B` by membership in `PWithOracle (encB '' B) encA`. The underlying algorithm is a deterministic adaptive `WordQueryComp` with a native `IsOraclePPTOn` realization. Its polynomial clock charges query-symbol writes and bounds both query lengths and query count; the oracle evaluation itself is one step. The machine realization is efficient for arbitrary admissible handlers, while correctness of the reduction is stated for the designated language oracle.

The oracle recognizes the **encoded image** of `B`: a word outside the image of `encB` receives “no.” This matters for an arbitrary encoding whose image need not be efficiently recognizable. The source therefore states [Turing composition](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L467) through an intermediate word language with `encBits`, and [closure in P](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L501) for a word-language target. These are not encoding-free claims for every typed target. Typed many-one precomposition remains available because it supplies valid encoded queries.

[The truth-table-to-Turing bridge](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L270) executes a batch of typed queries and evaluates the replies. One-one and all restricted truth-table variants also embed. Hardness consequences include [`NPHard.P_eq_NP_of_turing_mem_P`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L565), with the word-target assumption visible in the theorem. These are conditional transfer principles, not new separations or collapses.

## Autoreductions and splitting

An autoreduction is a reduction to the same language that avoids asking its original instance. [Polynomial-time](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L83) and [logspace](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L101) many-one versions require a fixed-point-free map. The polynomial-time truth-table variants—`k`-bounded, bounded, disjunctive, conjunctive, and unrestricted—require `q(a,i) ≠ a` only for indices actually used, `i < r(a)`. The same resource and answer semantics described above apply.

To turn a bounded disjunctive or conjunctive reduction from `Aᶜ` to `A` into an autoreduction,
import [`LogSpaceBoundedAutoreducibility`](../../Complexity/Computability/Complexity/Reduction/LogSpaceBoundedAutoreducibility.lean)
and apply `LogSpaceKDTTReducible.autoreducible_of_compl` or
`LogSpaceKCTTReducible.autoreducible_of_compl`. The result is
`LogSpaceKTruthTableAutoreducible k encA A`, with the same at-most-`k` bound. An active self-query
forces rejection for OR and acceptance for AND; the construction then asks zero queries.
Otherwise it negates the aggregate oracle answer. The test for self-queries uses certified
logspace equality of encoded instances and ignores unused indices.

The [complete checked client](../../ComplexityTests/LogSpaceBoundedAutoreducibility.lean), including
imports, exercises both membership branches, active and inactive self-queries, and the zero-query
full-language OR and empty-language AND witnesses. Its `L`-complete Boolean singleton examples
also show how to apply the complement-closed-class completeness corollaries. These establish
Proposition 2.7(2,3) of the expanded ECCC TR13-047 version; the theorem module maps the exact
source and conventions. The remaining full-paper objective stays on [issue #2468](https://github.com/cslib-community/complexitylib/issues/2468).

[`PolyTimeTuringAutoreducible`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TuringAutoreducible.lean#L80) has a more specific execution quantifier: no encoded self-query occurs along the run with the language's actual oracle, measured by `OracleComp.queriesWith`. It does not demand absence of self-queries along every counterfactual oracle-response path. Its native efficiency certificate still applies across handlers. [Every P language](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TuringAutoreducible.lean#L135) has such an autoreduction, using zero queries. In contrast, [singletons](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L379) and their complements fail fixed-point-free many-one autoreducibility.

[`MitoticWith`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L595) asks for an efficient separator `S` such that `A` is mutually reducible with each of `A ∩ S` and `A \ S`. The module specializes this to polynomial-time and logspace many-one reductions, and to polynomial-time `k`-bounded, bounded, disjunctive and unrestricted truth tables. For a fixed `k`, it requires equivalence of each part with `A`; it does not additionally require a direct `k`-query equivalence between the two parts, because composition can square the bound. [Fixed-query mitoticity implies autoreducibility](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L881), with analogous bounded, disjunctive, and unrestricted results. The many-one implication has an explicit [co-singleton boundary](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L1059).

## Local logspace self-reducibility

Import `Complexity.Computability.Complexity.Reduction.LocalSelfReducibility` for
`LocalSelfReductionQuery` and the indexed tt, disjunctive and conjunctive self-reducibility
predicates. The query word has the same encoded length, is strictly lexicographically smaller,
and agrees before the last ceiling-logarithm-many symbols. Only active query indices are
restricted. OR/AND self-reductions allow either Boolean answer when the count is zero.
They embed into tt self-reductions, which give query-avoiding tt autoreductions of the same
language. The count, generator and evaluator retain their native logspace certificates.
The [checked client](../../ComplexityTests/LocalSelfReducibility.lean) includes a nonzero-query
word instance and a zero-query singleton, as well as invalid-query edge cases.

The source is the expanded ECCC TR13-047 version (18 March 2013), Definitions 3.1–3.2,
printed page 6. The predicates cover the unbounded indexed tt/OR/AND clauses; bounded-query
and many-one specializations are not added here. The indexed tagged-base presentation is
explicit; equivalence to serialized source transducer output is not proved. Word reconstruction,
suffix length and well-founded descent are semantic results. Likewise the unary dependency
and id/negation invariant from Lemma 3.3(1) have no oracle resource certificate.
Import `Complexity.Computability.Complexity.Reduction.LocalSelfReducibility.VirtualWord` for
native one-bit access to a fixed original prefix and an already stored suffix.
`LocalSelfReductionQuery.access_output` connects the actual machine output to the query word;
`access_state_bound` charges only two binary counters, the literal suffix and a halting bit.
The [accessor](../../Complexity/Computability/Machines/ReadMachine/VirtualWord.lean) certifies
all five query-machine components in space linear in that state and compiles each fixed-data
accessor to a native multi-tape machine. With a suffix of at most $\lceil\log_2 n\rceil$ bits
and an address at most $n$, the encoded state has length at most $16(\log_2 n+1)$.
The prefix remains read-only input; no reconstructed query is placed in workspace.
[Checked clients](../../ComplexityTests/VirtualWord.lean) execute empty, length-one,
non-power-of-two, prefix/suffix boundary and default reads and instantiate native certificates.
For runtime parameters, import
`Complexity.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeAccess`.
The [runtime accessor](../../Complexity/Computability/Machines/ReadMachine/VirtualWord/Runtime.lean)
is one fixed query machine with a fixed initial state. Its input encoding is a framed binary
cut/suffix/address header followed by the literal original word. It loads only that header,
then reads one bit of the original-word tail.
`Turing.VirtualWord.Runtime.access_inSpace` compiles the whole operation with constants shared by all runtime parameters and explicitly charges the actual
header length plus a logarithmic input-position counter. Binary addresses never allocate a
word or unary counter of the indicated length.

`Turing.VirtualWord.Runtime.access_inOriginalLogSpace` measures workspace against the original
length $n$ when cut and address are at most $n$ and the suffix has at most $\lceil\log_2 n\rceil$ bits.
The physical query-machine states have length at most $272(\log_2 n+1)$; compilation adds a
fixed multiplicative constant. `LocalSelfReductionQuery.runtime_output` consumes exact query
reconstruction, including out-of-range false defaults; `runtime_admissible` checks the size
conditions for this compiler domain. All natural parameters have total behavior. With an
invalid cut beyond the original length, the operation still uses that declared cut as the
suffix offset and reads false in the intervening gap; virtual-word reconstruction is asserted
only for valid cuts. Large parameters retain the general charged-header bound.
[Runtime clients](../../ComplexityTests/VirtualWordRuntime.lean) check a nonconstant parameter
family, native certificates, boundaries and invalid data. These results initialize and execute
an individual read. For a whole-word consumer, import
`Complexity.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeEvaluator`.
`Turing.VirtualWord.Evaluator.machine δ` loads the same supplied header, then scans all
`cut + suffix.length` virtual positions twice with a saved Boolean transition state. Its counter
is binary, each read goes back to the original input, and it never stores the reconstructed
word. A zero-length virtual word halts after initialization. For valid cuts,
`value_word` identifies every transition with the corresponding virtual bit and
`evaluate_word` gives the ordinary finite-state fold of two copies of the virtual word;
`LocalSelfReductionQuery.runtime_evaluate` identifies actual output with the fold of two complete
passes over the exact reconstructed query.

`Evaluator.evaluate_inSpace` supplies a native program with shared constants and charges the
actual header plus a logarithmic encoded-input counter. `evaluate_inOriginalLogSpace` uses the
same admissibility conditions as the accessor; physical consumer states have length at most
$816(\log_2 n+1)$ against the original length $n$, before a fixed compiler factor.
The header's address field is used only by initialization's discarded read; the evaluator
computes its own addresses. Invalid cuts retain the accessor's declared-offset/false-gap
behavior and general charged-header bound. The
[complete checked client](../../ComplexityTests/VirtualWordEvaluator.lean) runs nonconstant OR
and NAND-state consumers, changing runtime families, empty and length-one words, non-power-of-two
lengths, oversized suffixes and invalid cuts. `family_terminates` certifies the read loop for
unbounded lengths, rather than only those finite executions.

This consumer is restricted to two passes and one Boolean of saved state. General native
logspace predicate substitution, generating the supplied header from a query generator and
regenerating an answer word remain open.

**The transfer lemma remains open**: native virtual-input/answer regeneration for the unbounded
evaluator and the adaptive-to-tt conversion still need proofs. No desired autoreduction is
assumed as a substitute. Complete NL/P instances, Theorem 3.5, and Sections 4–5 remain under
[issue #2468](https://github.com/cslib-community/complexitylib/issues/2468).

## Parameter-sensitive transfer rules

[FPT reductions and kernels](parameterized-complexity.md) separately bound the target parameter by a function of the source parameter. Fine-grained transfer uses more quantitative contracts without defining a new reduction datatype. [`DecidableInExpTime.of_reduction`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L117) takes a native polynomial-time membership-preserving map with `μB(f(a)) ≤ c μA(a)+c`. A target time rate `2^(δ μB)` yields source rate `2^(cδ μA)`, up to encoded-length polynomial factors, for `δ ≥ 0`. [`DecidableInSubexpTime.of_reduction`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L181) transfers the predicate that permits a decider for each positive rate.

[`DecidableInSubexpTime.of_expReduction`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L252) permits the map itself to cost `2^(C m(a)) (L+1)^D`, under `ComputableInO` with that time and output-charged space bound. If the output parameter is at most `c m(a) floor(log₂(m(a))) + c`, target subexponential time implies source subexponential time in `m floor(log₂ m)`. The smaller exponential preprocessing cost is absorbed at each positive target rate. Neither rule introduces an oracle reduction or an unrestricted subexponential-reduction-family notion. ETH-based lower-bound transport in this module remains an implication from its displayed ETH premise; the snapshot's independent [native counting endpoints](native-counting.md) must be considered when interpreting that premise.

## Source examples and evidence

The inspected [ReductionVariants tests](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ReductionVariants.lean#L1) give concrete prefix queries with OR, AND, XOR, and majority evaluators, including composition from two to four queries. These exhibit evaluator forms, not a separation theorem between the resulting reducibility relations. [LogSpaceReductions](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/LogSpaceReductions.lean#L1) supplies native logspace prefix and pair-query instances. [ReductionIsomorphism](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ReductionIsomorphism.lean#L1) uses word reversal as an isomorphism and bit-prefixing with `tail` as a length-increasing map with a total left inverse.

[Autoreducibility](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Autoreducibility.lean#L1) gives a concrete mitotic co-singleton and proves its many-one autoreducibility obstruction; [TuringAutoreducible](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/TuringAutoreducible.lean#L1) instantiates zero-query and parity-preserving examples. These are static inspections of existing test sources. The [model map](../model-map.md) indexes the semantic/resource variants and their explanations, with no fresh Lean compilation claim. The generic reduction kernel and the local bounded-reduction modules carry candidate upstream markers.

[complexitylib]: ../sources.md#complexitylib
