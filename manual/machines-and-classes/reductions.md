# Reductions and information access

Reduction interfaces determine which computation may translate instances and how answers from the target problem may be used. cslib-frontier separates these choices: total many-one maps, invertible or length-increasing maps, nonadaptive truth tables, adaptive word-oracle programs, and parameter-sensitive resource-transfer rules. Their encodings and query conventions are part of their semantics. This page surveys interfaces rather than enumerating reductions between individual problems. [cslib-frontier][complexitylib]

## Many-one maps and strengthened interfaces

The shared kernel [`ManyOneReducibleBy`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Reduction/ManyOne.lean#L53) is `∃ f, Good f ∧ ∀ a, a ∈ A ↔ f(a) ∈ B`. It has no built-in machine, encoding, or resource bound. Its composition theorem requires closure of the admissible maps under composition; [`lift`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Reduction/ManyOne.lean#L97) transfers a reduction to representations only when a supplied simulator respects partial decoding, including rejection of undecodable inputs. This generic interface is distinct from Mathlib's computable many-one relation on `Primcodable` types.

[`PolyTimeReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction.lean#L151) instantiates `Good` with a native polynomial-time transducer under source and target encodings. [`LogSpaceReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/LogSpace.lean#L176) uses the native output-uncharged logspace predicate: input and append-only output are not workspace, but producing output consumes time. [`HardUnder`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/ManyOne.lean#L120) and `CompleteUnder` abstract the class-level quantifiers, ranging over source instance types and encodings. They do not impose a hidden universal representation. The Cook–Levin endpoint uses this typed polynomial-time many-one interface, as detailed in [Major endpoints](endpoints-and-hierarchies.md).

Several stronger predicates retain the same membership equivalence while adding computational structure:

| Interface | Additional requirement |
|---|---|
| [`PolyTimeOneOneReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/OneOne.lean#L63), [`LogSpaceOneOneReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/OneOne.lean#L107) | The map is injective, with the indicated native resource bound. |
| [`PolyTimeInvertibleOneOneReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L183) | A total polynomial-time left inverse `g : β → α` satisfies `g(f(a)) = a`. |
| [`PolyTimeLengthIncreasingOneOneReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L254) | The injective map strictly increases encoded length on every input. |
| [`PolyTimeInvertibleLengthIncreasingOneOneReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L311) | Both a total polynomial-time left inverse and strict encoded-length increase. |
| [`PolyTimeIsomorphic`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L116) | An equivalence of the entire ambient instance types, with both directions polynomial time and membership preserved. |

A left inverse is defined even outside the image of the forward map; its behavior there need not recover a meaningful source instance. An isomorphism requires surjectivity as well as injectivity. The isomorphism API proves preservation of [P](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L169) and [NP](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Isomorphism.lean#L174) and basic composition laws. It does not by itself turn mutual one-one reducibility into an isomorphism theorem.

### Berman–Hartmanis isomorphism theory

The source version is the 1975 Cornell technical report of Berman and Hartmanis [bermanhartmanis75][bermanhartmanis75]. Locators below refer to that report; the numbering of the 1977 journal version has not been checked. The report works with languages of strings and with polynomial-time partial inverses defined on the range of a reduction. The library works with typed instances under injective encodings, total polynomial-time left inverses, and forward-image tests such as `f (f' y) = y` that decide the range. The padding results also need a total decoder, described below.

[`polyTime_schroeder_bernstein`](../../CslibFrontier/Computability/Complexity/Reduction/Isomorphism/SchroederBernstein.lean) is the polynomial-time Cantor–Schröder–Bernstein theorem of Berman and Hartmanis (§III, Theorem 1). Suppose maps `f : α → β` and `g : β → α` are polynomial time, strictly increase encoded length, and have polynomial-time left inverses. Then some `e : α ≃ β` has `e` and `e.symm` polynomial time and `e a = f a ∨ g (e a) = a` for every `a`. The proof decides the side on which the backward chain of preimages from `a` stops, by a fuelled walk through the iteration combinator. Length increase bounds the walk by the encoded length of `a`. Only left inverses are assumed, and the instance types are arbitrary types with injective encodings. Its corollary [`PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeIsomorphic`](../../CslibFrontier/Computability/Complexity/Reduction/Isomorphism/SchroederBernstein.lean) turns mutual `≤₁,ᵢₗ` reducibility into `≅ᵖ`.

[`Paddable`](../../CslibFrontier/Computability/Complexity/Reduction/Isomorphism/Paddable.lean) asks for polynomial-time maps `pad : α → List Bool → α` and `unpad : α → List Bool` with `unpad (pad a y) = y` and `pad a y ∈ A ↔ a ∈ A`. This is the typed form of the report's two-argument padding and read-back condition (Lemmas 3 and 5). The padding lemma upgrades a many-one reduction into a paddable language to `≤₁,ᵢₗ`: it pads the reduct with the framed source encoding and enough filler to exceed every polynomial bound on the read-back. Inverting it decodes a word back to a typed source instance, so the lemma and its corollaries assume a total polynomial-time `Decoder` for each source encoding. This hypothesis is the typed-model counterpart of working over strings. The module proves that interreducible paddable languages, and in particular paddable `NP`-complete languages, are `≅ᵖ`. It also proves that paddability is invariant under `≅ᵖ`, and that an `NP`-complete language is `≅ᵖ` to a paddable `NP`-complete one exactly when it is paddable. A nonempty paddable language is infinite. Reading words through a total decoder preserves paddability and `NP`-completeness, and gives a `≅ᵖ` between a paddable typed language and its word language.

[`SAT.pad`](../../CslibFrontier/Computability/Complexity/Problems/SAT/Paddable.lean) prepends the tautological clause `[(N, true), (N, false), (N, true)]`, where `N` has binary digits `y ++ [true]`. This gadget differs from the CNF construction for the report's Theorem 7, which pads with clauses over fresh variables: here one clause over a single variable records the padding in the variable's binary digits, and `N` need not be fresh because the clause is always true. The clause has width three and contains both literals of `N`, so `SAT`, `UNSAT`, `ThreeSAT`, `ExactThreeSAT` and `NAEThreeSAT` are paddable, and `SAT` is `≅ᵖ` to each of the three `NP`-complete variants under `encCNF`. The construction does not apply to languages that require distinct variables in a clause, such as `EUThreeSAT`, or exactly one true literal per clause. [`BermanHartmanisConjecture`](../../CslibFrontier/Computability/Complexity/Reduction/Isomorphism/Conjecture.lean) states the conjecture of the report's §I as a hypothesis for languages of bit strings, following the source's string formulation; like the source's, it implies `P ≠ NP`. The module proves that the conjecture is equivalent to paddability of every `NP`-complete word language, and that it implies `SAT ∉ P` and `P ≠ NP` for formulas and for bit strings. Berman's theorem that `EXP`-complete sets are complete under one-one length-increasing reductions, and the Agrawal–Allender–Rudich `AC⁰` isomorphism theorem, are not formalized. The [BermanHartmanis tests](../../CslibFrontierTests/BermanHartmanis.lean) check an isomorphism between even- and odd-length words obtained from the theorem, a paddable and a nonpaddable language, concrete runs of the SAT padding, and client uses of the SAT-variant isomorphisms.

## Nonadaptive query batches

[`PolyTimeTruthTableReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTable.lean#L84) uses three total native polynomial-time functions: a count `r(a)`, an indexed query `q(a,i)`, and a Boolean evaluator `d(a,answers)`. The count and index use unary encodings. Before seeing any answers, the reduction determines `q(a,0), …, q(a,r(a)-1)`. The semantic answer word contains the membership bits of those typed target instances; the evaluator receives the original input and that full word. Unary count output makes a polynomially bounded number of queries part of the native contract. Queries outside the used index range do not affect acceptance.

The answer word is a semantic oracle result, not a claim that target membership can be computed without an oracle. [`truthTable_mem_P`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTable.lean#L140) supplies that computation when the target is in `P`. The restrictions below change the permitted query bound or answer combination:

| Polynomial-time predicate | Meaning |
|---|---|
| [`PolyTimeKTruthTableReducible k`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L77) | At most the fixed `k` queries on every input. |
| [`PolyTimeBTTReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L86) | Some single constant `k` bounds all query counts. |
| [`PolyTimeDTTReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L273) | Accept iff at least one query belongs to the target. |
| [`PolyTimeCTTReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L280) | Accept iff every query belongs to the target. |
| [`PolyTimePTTReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L367) | The evaluator is monotone under coordinatewise `false ≤ true`, for every pair of answer words related by `List.Forall₂`. |

Zero queries are allowed. They make the disjunctive predicate false and the conjunctive predicate true; a general evaluator may decide from the original input alone. Composing fixed bounds multiplies them: [`PolyTimeKTruthTableReducible.trans`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TruthTableVariants.lean#L250) gives `k₁k₂`, rather than retaining either bound. Bounded, disjunctive, and conjunctive composition and the embeddings into unrestricted truth-table and Turing reducibility are proved.

The [logspace family](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L113) has all six corresponding predicates: unrestricted truth-table, `k`-truth-table, bounded, disjunctive, conjunctive, and positive. It substitutes native `ComputableInLogSpace` for the count, query generator, and evaluator. Thus the evaluator's space is measured on the encoding of `(a,answers)`, where the answer word is an input, rather than storage automatically supplied to an oracle machine for free. The module explicitly adopts an `L` evaluator and does not claim equivalence to a Boolean-formula/`NC¹` evaluator convention.

The proven [bounded-query closure in L](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L469) and [fixed-bound composition](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/LogSpaceTruthTable.lean#L480) preserve this model. All six notions have polynomial-time counterparts. This source does not provide an unrestricted-logspace-truth-table `mem_L` theorem, so the bounded closure result must retain its bounded-query hypothesis.

For a fixed bound with an OR or AND evaluator, import
[`LogSpaceBoundedTruthTable`](../../CslibFrontier/Computability/Complexity/Reduction/LogSpaceBoundedTruthTable.lean).
`LogSpaceKDTTReducible k` and `LogSpaceKCTTReducible k` retain the same unary count and indexed
query generator and require that count to be at most `k` on every input. Their
`logSpaceKTruthTableReducible` lemmas preserve that bound when introducing an explicit evaluator.

Both families instantiate the resource-free kernels in
[Reduction/TruthTable](../../CslibFrontier/Computability/Reduction/TruthTable.lean), as the
many-one notions instantiate `ManyOneReducibleBy`. `TruthTableReducibleBy Good` asks for a count,
query generator and evaluator satisfying `Good`, while `DTTReducibleBy` and `CTTReducibleBy` drop
the evaluator. The unrestricted, `k`-truth-table, disjunctive, conjunctive and positive predicates,
and the fixed-bound `LogSpaceKDTTReducible` and `LogSpaceKCTTReducible`, spell out their bodies
with the resource conditions and any query bound or monotonicity condition grouped into one
conjunct, so each is by definition a kernel instance and the kernel lemmas apply to it directly.
`PolyTimeBTTReducible` and `LogSpaceBTTReducible` are `∃ k, …KTruthTableReducible k …`; their
lemmas unpack that single uniform bound before applying the kernel. Monotonicity in `Good`,
complementation, one-query many-one embeddings, the `List.any id` and `List.all id` evaluators
and disjunctive/conjunctive duality are proved once at kernel level; the named lemmas such as
`PolyTimeTruthTableReducible.compl_left` apply them, so clients never supply a `Good`. A new
resource bound needs only the closure facts of its own `Good`. Transitivity stays per family,
sharing the combiner in
[TruthTable/Composition](../../CslibFrontier/Computability/Complexity/Reduction/TruthTable/Composition.lean).

## Adaptive word-oracle access

[`PolyTimeTuringReducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L120) defines `A ≤T B` by membership in `PWithOracle (encB '' B) encA`. The underlying algorithm is a deterministic adaptive `WordQueryComp` with a native `IsOraclePPTOn` realization. Its polynomial clock charges query-symbol writes and bounds both query lengths and query count; the oracle evaluation itself is one step. The machine realization is efficient for arbitrary admissible handlers, while correctness of the reduction is stated for the designated language oracle.

The oracle recognizes the **encoded image** of `B`: a word outside the image of `encB` receives “no.” This matters for an arbitrary encoding whose image need not be efficiently recognizable. The source therefore states [Turing composition](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L467) through an intermediate word language with `encBits`, and [closure in P](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L501) for a word-language target. These are not encoding-free claims for every typed target. Typed many-one precomposition remains available because it supplies valid encoded queries.

[The truth-table-to-Turing bridge](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L270) executes a batch of typed queries and evaluates the replies. One-one and all restricted truth-table variants also embed. Hardness consequences include [`NPHard.P_eq_NP_of_turing_mem_P`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Turing.lean#L565), with the word-target assumption visible in the theorem. These are conditional transfer principles, not new separations or collapses.

## Autoreductions and splitting

An autoreduction is a reduction to the same language that avoids asking its original instance. [Polynomial-time](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L83) and [logspace](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L101) many-one versions require a fixed-point-free map. The polynomial-time truth-table variants—`k`-bounded, bounded, disjunctive, conjunctive, and unrestricted—require `q(a,i) ≠ a` only for indices actually used, `i < r(a)`. The same resource and answer semantics described above apply. These variants add that avoidance condition to the kernel's `Good`, so their forgetful maps, closure under complement and disjunctive/conjunctive duality are kernel corollaries.

To turn a bounded disjunctive or conjunctive reduction from `Aᶜ` to `A` into an autoreduction,
import [`LogSpaceBoundedAutoreducibility`](../../CslibFrontier/Computability/Complexity/Reduction/LogSpaceBoundedAutoreducibility.lean)
and apply `LogSpaceKDTTReducible.autoreducible_of_compl` or
`LogSpaceKCTTReducible.autoreducible_of_compl`. The result is
`LogSpaceKTruthTableAutoreducible k encA A`, with the same at-most-`k` bound. An active self-query
forces rejection for OR and acceptance for AND; the construction then asks zero queries.
Otherwise it negates the aggregate oracle answer. The test for self-queries uses certified
logspace equality of encoded instances and ignores unused indices. The logspace autoreducible
notions add query avoidance to the kernel's `Good`, so `LogSpaceKTruthTableAutoreducible.compl`
is a kernel corollary, and the conjunctive case follows from the disjunctive one by duality.

The [complete checked client](../../CslibFrontierTests/LogSpaceBoundedAutoreducibility.lean), including
imports, exercises both membership branches, active and inactive self-queries, and the zero-query
full-language OR and empty-language AND witnesses. Its `L`-complete Boolean singleton examples
also show how to apply the complement-closed-class completeness corollaries. These establish
Proposition 2.7(2,3) of the expanded ECCC TR13-047 version; the theorem module maps the exact
source and conventions. The remaining full-paper objective stays on [issue #2468](https://github.com/cslib-community/cslib-frontier/issues/2468).

[`PolyTimeTuringAutoreducible`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TuringAutoreducible.lean#L80) has a more specific execution quantifier: no encoded self-query occurs along the run with the language's actual oracle, measured by `OracleComp.queriesWith`. It does not demand absence of self-queries along every counterfactual oracle-response path. Its native efficiency certificate still applies across handlers. [Every P language](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/TuringAutoreducible.lean#L135) has such an autoreduction, using zero queries. In contrast, [singletons](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L379) and their complements fail fixed-point-free many-one autoreducibility.

[`MitoticWith`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L595) asks for an efficient separator `S` such that `A` is mutually reducible with each of `A ∩ S` and `A \ S`. The module specializes this to polynomial-time and logspace many-one reductions, and to polynomial-time `k`-bounded, bounded, disjunctive and unrestricted truth tables. For a fixed `k`, it requires equivalence of each part with `A`; it does not additionally require a direct `k`-query equivalence between the two parts, because composition can square the bound. [Fixed-query mitoticity implies autoreducibility](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L881), with analogous bounded, disjunctive, and unrestricted results. The many-one implication has an explicit [co-singleton boundary](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Reduction/Autoreducibility.lean#L1059).

## Local logspace self-reducibility

Import `CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility` for
`LocalSelfReductionQuery` and the indexed tt, disjunctive and conjunctive self-reducibility
predicates. The query word has the same encoded length, is strictly lexicographically smaller,
and agrees before the last ceiling-logarithm-many symbols. Only active query indices are
restricted. OR/AND self-reductions allow either Boolean answer when the count is zero.
They embed into tt self-reductions, which give query-avoiding tt autoreductions of the same
language. The count, generator and evaluator retain their native logspace certificates.
The [checked client](../../CslibFrontierTests/LocalSelfReducibility.lean) includes a nonzero-query
word instance and a zero-query singleton, as well as invalid-query edge cases.

The source is the expanded ECCC TR13-047 version (18 March 2013), Definitions 3.1–3.2,
printed page 6. The predicates cover the unbounded indexed tt/OR/AND clauses; bounded-query
and many-one specializations are not added here. The indexed tagged-base presentation is
explicit; equivalence to serialized source transducer output is not proved. Word reconstruction,
suffix length and well-founded descent are semantic results. Likewise the unary dependency
and id/negation invariant from Lemma 3.3(1) have no oracle resource certificate.
Import `CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.VirtualWord` for
native one-bit access to a fixed original prefix and an already stored suffix.
`LocalSelfReductionQuery.access_output` connects the actual machine output to the query word;
`access_state_bound` charges only two binary counters, the literal suffix and a halting bit.
The [accessor](../../CslibFrontier/Computability/Machines/ReadMachine/VirtualWord.lean) certifies
all five query-machine components in space linear in that state and compiles each fixed-data
accessor to a native multi-tape machine. With a suffix of at most $\lceil\log_2 n\rceil$ bits
and an address at most $n$, the encoded state has length at most $16(\log_2 n+1)$.
The prefix remains read-only input; no reconstructed query is placed in workspace.
[Checked clients](../../CslibFrontierTests/VirtualWord.lean) execute empty, length-one,
non-power-of-two, prefix/suffix boundary and default reads and instantiate native certificates.
For runtime parameters, import
`CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeAccess`.
The [runtime accessor](../../CslibFrontier/Computability/Machines/ReadMachine/VirtualWord/Runtime.lean)
is one fixed query machine with a fixed initial state. Its input encoding is a framed binary
cut/suffix/address header followed by the literal original word. It loads only that header,
then reads one bit of the original-word tail.
`Turing.VirtualWord.Runtime.access_inSpace` compiles the whole operation with constants shared by all runtime parameters and explicitly charges the actual
header length plus a logarithmic input-position counter. Binary addresses never allocate a
word or unary counter of the indicated length.

For certificates of consumers that retain a runtime state, compose
`Runtime.header_inSpace` with the saved-state projection to decode its reversed header.
Then compose `Evaluator.width_data_inSpace` with that data certificate to compute the declared
virtual width. Both operations use space linear in their encoded argument; neither constructs
the virtual word. The concrete evaluator and generic simulation use these same certificates.

`Turing.VirtualWord.Runtime.access_inOriginalLogSpace` measures workspace against the original
length $n$ when cut and address are at most $n$ and the suffix has at most $\lceil\log_2 n\rceil$ bits.
The physical query-machine states have length at most $272(\log_2 n+1)$; compilation adds a
fixed multiplicative constant. `LocalSelfReductionQuery.runtime_output` consumes exact query
reconstruction, including out-of-range false defaults; `runtime_admissible` checks the size
conditions for this compiler domain. All natural parameters have total behavior. With an
invalid cut beyond the original length, the operation still uses that declared cut as the
suffix offset and reads false in the intervening gap; virtual-word reconstruction is asserted
only for valid cuts. Large parameters retain the general charged-header bound.
[Runtime clients](../../CslibFrontierTests/VirtualWordRuntime.lean) check a nonconstant parameter
family, native certificates, boundaries and invalid data. These results initialize and execute
an individual read. For a whole-word consumer, import
`CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeEvaluator`.
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
[complete checked client](../../CslibFrontierTests/VirtualWordEvaluator.lean) runs nonconstant OR
and NAND-state consumers, changing runtime families, empty and length-one words, non-power-of-two
lengths, oversized suffixes and invalid cuts. `family_terminates` certifies the read loop for
unbounded lengths, rather than only those finite executions.

For an arbitrary outer machine, import
[`VirtualWord.Simulation`](../../CslibFrontier/Computability/Machines/ReadMachine/VirtualWord/Simulation.lean).
`Simulation.machine M` first loads the same supplied header, then redirects every query of `M`
to the original tail and resumes its entire saved state. The virtual end produces `none`, even
when the physical tail continues; a present false symbol stays `some false`. `resume` applies
from any saved state, preserving the header and cursor. `run_loaded`, `first_halt` and `output`
give exact state, halt and output correspondence, including step emissions and final output.
The physical query still occurs for suffix and out-of-range addresses; the adapter ignores its
result when appropriate. Invalid cuts retain a total declared-offset implementation, but the
word-equivalence theorems require `cut ≤ original.length`.

To obtain a native certificate, supply `Simulation.computableInSpace` with the outer machine's
five native component certificates, its own first-halt clock/output proof and a bound $B(p)$ on
the encoding of every saved outer state through that clock. The result uses one native program,
with constants shared across runtime inputs and workspace
$O(B(p)+|\mathrm{encData}(p)|+\log_2|\mathrm{encInput}(p)|+1)$.
The header remains an explicit runtime input, and its full encoding is charged.
[The complete checked copier client](../../CslibFrontierTests/VirtualWordSimulation.lean) carries
an unbounded binary cursor and EOF flag, streams each virtual symbol, and appends its final
binary address. `native_copier` instantiates the compiler for every valid runtime header and
unbounded original length, with a logarithmic saved-counter budget. The finite checks cover
suffix substitution, virtual EOF before physical EOF, present false bits, empty words,
resumption from a noninitial cursor and an already halted state.

For an existing native machine, import
[`VirtualWord.Native`](../../CslibFrontier/Computability/Machines/ReadMachine/VirtualWord/Native.lean).
`Native.machine` reuses the universal simulator's finite work-tape zippers, finite control and
binary shifted input-head position, without keeping output history in its saved state.
`configuration_native`, `output_native` and `halted_native` preserve the original machine's
configuration, streaming output and halt flag at every clock. Initialization starts at native
position one; position zero is the left blank and the right blank is at input length plus one.
The adapter ignores any fetched bit at position zero, allows a right move from that boundary,
and blocks outward right moves at EOF. Present false symbols remain distinct from EOF.

`Native.computableInSpace_of_computes` takes a fixed native binary machine, an injective numbering
of its finite states, and its ordinary computation and workspace certificates on the specified
virtual words. It derives all five component certificates and selects a first-halt clock
internally. Its saved configuration budget is $O(s+\log_2(m)+1)$ for native workspace $s$ and
virtual input length $m$, by `length_native_run_le_of_space` and `budget_le`. The input-head term
follows from the native model's clamped boundary convention; no extra runtime bound is needed.
The original word, virtual word and emitted output history are absent from that saved encoding.
The description is fixed, so compiler constants may depend on the machine but not the runtime
header or input.

`Native.of_logSpace` directly accepts an ordinary `ComputableInLogSpace f encBits encOut`
certificate for a word function. It constructs a native certificate for applying `f` to the
virtual word on `Simulation.encInput`, in workspace
$O(\log_2(m)+|\mathrm{encData}(p)|+\log_2|\mathrm{encInput}(p)|+1)$.
This is a bound in the charged header and both input lengths; a specialization measuring space
only against the original word still needs appropriate header/virtual-length bounds.
[The complete native client](../../CslibFrontierTests/VirtualWordNative.lean) uses the existing
framing transducer's machine, including pending output and final EOF flushing, and also applies
the ordinary logspace bridge. It checks nonempty/empty output, present false, both boundary
movement conventions and already halted configurations.

Import
[`VirtualWord.Generate`](../../CslibFrontier/Computability/Machines/ReadMachine/VirtualWord/Generate.lean)
to generate the runtime frame. `Generate.prepare_logSpace` takes ordinary native logspace
programs for the tail and binary cut/suffix/address data and emits `frame (encData d) ++ tail`.
`Generate.consume` composes that generator with `Native.of_logSpace` through the existing
`comp_space` theorem. Each requested frame symbol is recomputed; neither the generated frame
nor the virtual word is allocated in workspace. Its premises bound the whole encoded header
by $H(\log_2 n+1)$ and the virtual length by $V(n+1)^D$, where $n$ is the caller's **actual encoded
input length**. Polynomial frame length follows from the generator's logspace certificate.
The resulting workspace is $O(\log_2 n+1)$, including both binary position counters.

For a live local-query generator, import
[`RuntimeGenerate`](../../CslibFrontier/Computability/Complexity/Reduction/LocalSelfReducibility/RuntimeGenerate.lean).
`localQueryData_logSpace` uses `bitsDrop'` to discard the generated query prefix and
`unaryToBinary` to emit binary cut metadata. Supply an ordinary query program, a cut program
with streamed unary output, and a binary address program. The unary cut is an intermediate
output consumed by recomputation; it does not inflate the caller's encoding or workspace.
`consume_localQuery` proves header and virtual-length bounds from `LocalSelfReductionQuery`,
the equation identifying that cut, and original-word length at most caller encoding length.
It still requires the cut program: a general ceiling-logarithmic cut implementation is not
provided here. Empty words cannot satisfy strict local-query descent; zero-query base cases
remain with the self-reduction interface.

[The complete generated-frame client](../../CslibFrontierTests/VirtualWordGenerate.lean) computes
a varying cut/address from the first live bit and a varying negated suffix, then consumes the
virtual word with the existing framing transducer. It checks empty and both first-bit cases,
exact header decoding and the unchanged tail. It also runs a nonconstant live query generator
through counter-program prefix dropping into a generated frame. From the repository root,
elaborate this test with the documented build procedure before reusing its imports and programs.

Unbounded virtual answer-word regeneration remains open. A Boolean family certificate is not
yet a polynomial-count answer-stream generator; the existing `mapToBits_range_of_le` API only
handles a fixed constant bound. Oracle answers also require a native oracle computation contract,
rather than an assumed ordinary logspace characteristic function for the target language.

**The transfer lemma remains open**: native virtual-input/answer regeneration for the unbounded
evaluator and the adaptive-to-tt conversion still need proofs. No desired autoreduction is
assumed as a substitute. Complete NL/P instances, Theorem 3.5, and Sections 4–5 remain under
[issue #2468](https://github.com/cslib-community/cslib-frontier/issues/2468).

## Selectivity

A P-selector for `A : Set α` is a function `f : α → α → α` that is polynomial-time on pairs encoded
with `encPair enc enc`, returns one of its two arguments, and returns a member of `A` whenever
either argument is one. Import
[`Classes.Selective`](../../CslibFrontier/Computability/Complexity/Classes/Selective.lean) for
`IsSelector` and `PSel enc`. `mem_PSel_iff_bool` converts to a Boolean selector
`g : α × α → Bool` that names the argument to pick; prove closure results in that form. `PSel`
contains `P` (`P_subset_PSel`) and is closed under complement (`compl_mem_PSel`). It is closed
downward under polynomial-time many-one reductions (`PolyTimeReducible.mem_PSel`). Every lower
set of a linear order compared in polynomial time is P-selective (`mem_PSel_of_isLowerSet`).

[`Selective.Selman`](../../CslibFrontier/Computability/Complexity/Classes/Selective/Selman.lean)
proves Selman's theorem: `NPHard.P_eq_NP_of_mem_PSel` turns an `NP`-hard P-selective set into
`P enc = NP enc` for every encoding. `NPComplete.mem_PSel_iff` gives the converse for complete
sets. The proof reduces `SAT` to the given set. It then decides `SAT` with the generalized
self-reduction lemma `SAT.verifier_search_of_step`, which needs only that each answer keeps the
formula satisfiable, not that the answers are correct; the verifier checks the result.
Searches that fix variables by unit clauses use
[`Problems/SAT/Units`](../../CslibFrontier/Computability/Complexity/Problems/SAT/Units.lean)
(`SAT.eval_units_append`, `SAT.length_encCNF_units_le`).

A verifier that reads `SAT.assignment` gets its certificate from
`SAT.assignment_vars_map_append` in
[`Problems/SAT`](../../CslibFrontier/Computability/Complexity/Problems/SAT.lean): the values of
an assignment listed along `φ.vars`, followed by any padding, describe it on the variables of `φ`.

[`Selective.Ko`](../../CslibFrontier/Computability/Complexity/Classes/Selective/Ko.lean) proves
`PSel_subset_PPolyOn`. The advice at length `n` is a list of at most `n + 1` members of length `n`,
using at most `(n + 1)(2n + 1)` bits (`exists_advice_polyTime_of_mem_PSel`), in the
`PPoly.of_advice` convention. Its combinatorial core is the finite tournament lemma
`Finset.exists_dominating_subset_of_card_lt_two_pow` in
[`Foundations/Data/Finset/Tournament`](../../CslibFrontier/Foundations/Data/Finset/Tournament.lean).

[`Selective.LeftCut`](../../CslibFrontier/Computability/Complexity/Classes/Selective/LeftCut.lean)
gives the standard nonvacuity family. `leftCut r` holds the bit strings that are lexicographically
at most the prefix of `r : ℕ → Bool` of the same length. It is P-selective for every `r`
(`leftCut_mem_PSel`), and the comparison uses `ComputableInPolyTime.bits_lex_le` on `encBits`.
`leftCut_injective` and `not_countable_PSel` show that there are uncountably many P-selective
sets. The [checked client](../../CslibFrontierTests/Selective.lean) covers concrete members and
non-members of a left cut, a non-selector, right cuts, Ko's theorem applied to left cuts, and
`P ≠ NP` ruling out a selector for `SAT`.

Undecidability of some left cut is not formalized, because no count of machines is proved. Also
open: self-reducible P-selective sets lie in `P`, and P-selective sets are not truth-table-hard for
`NP` unless `P = NP`.

## Sparse and tally oracles

Meyer's theorem `P/poly = P^SPARSE` is in two modules. The oracle is a word language
`S : Set (List Bool)`, sparse for `encBits` (`SPARSE encBits`) or tally (`TALLY`, all letters
`true`). The decided problem `A : Set α` is in `PPolyOn enc` for an arbitrary instance encoding
`enc`.
[`Sparse.Turing`](../../CslibFrontier/Computability/Complexity/Classes/Sparse/Turing.lean) proves
`PWithOracle_subset_PPolyOn`: the advice lists the short members of `S`.
[`Sparse.Meyer`](../../CslibFrontier/Computability/Complexity/Classes/Sparse/Meyer.lean) proves the
converse with a tally oracle. For `exists_polyTimeTruthTableReducible_adviceTally`,
`PPoly.exists_evalAdvice` provides advice `α` of polynomial length. Its oracle `adviceTally α` contains the unary word of
`Nat.pair n i` exactly when bit `i` of `α n` is `true` (`encUnary_pair_mem_adviceTally`). The
reduction is nonadaptive. On an input of length `n` it asks all `|α n|` bit queries and then
evaluates the listed circuits. `PolyTimeTruthTableReducible.polyTimeTuringReducible` turns it into
`PWithOracle` membership.

Use `mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle` or
`mem_PPolyOn_iff_exists_mem_TALLY_mem_PWithOracle` to move between circuits and oracles. For example,
`P^S ⊆ P^T` for some tally `T` when `S` is sparse. The class equalities are
`PPolyOn_eq_iUnion_PWithOracle_SPARSE` and `PPolyOn_eq_iUnion_PWithOracle_TALLY`, and
`mem_PPolyOn_iff_exists_mem_TALLY_polyTimeTruthTableReducible` gives `P/poly = R_tt(TALLY)`. The
oracle languages exist but need not be decidable, as for `P/poly` itself. The
[checked client](../../CslibFrontierTests/SparseMeyer.lean) shows members and non-members of a
concrete `adviceTally` and applies the theorem to every length-defined language, including
undecidable ones. Kadin's `P^{NP[O(log n)]}` consequences and Hemachandra's `P^NP_tt`
characterization remain open (see `ROADMAP.md`).

## Parameter-sensitive transfer rules

[FPT reductions and kernels](parameterized-complexity.md) separately bound the target parameter by a function of the source parameter. Fine-grained transfer uses more quantitative contracts without defining a new reduction datatype. [`DecidableInExpTime.of_reduction`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L117) takes a native polynomial-time membership-preserving map with `μB(f(a)) ≤ c μA(a)+c`. A target time rate `2^(δ μB)` yields source rate `2^(cδ μA)`, up to encoded-length polynomial factors, for `δ ≥ 0`. [`DecidableInSubexpTime.of_reduction`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L181) transfers the predicate that permits a decider for each positive rate.

[`DecidableInSubexpTime.of_expReduction`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/Reduction.lean#L252) permits the map itself to cost `2^(C m(a)) (L+1)^D`, under `ComputableInO` with that time and output-charged space bound. If the output parameter is at most `c m(a) floor(log₂(m(a))) + c`, target subexponential time implies source subexponential time in `m floor(log₂ m)`. The smaller exponential preprocessing cost is absorbed at each positive target rate. Neither rule introduces an oracle reduction or an unrestricted subexponential-reduction-family notion. ETH-based lower-bound transport in this module remains an implication from its displayed ETH premise; the snapshot's independent [native counting endpoints](native-counting.md) must be considered when interpreting that premise.

Polynomial-rate transfer from orthogonal vectors is a direct composition rather than a reduction datatype. `CslibFrontier.Computability.Complexity.FineGrained.Diameter` formalizes the orthogonal vectors form of Roditty and Vassilevska Williams's diameter two-versus-three construction (Section 4, Theorem 9, stated there from CNF-SAT for graphs with `m` edges). Partial assignments become vectors and clauses become coordinates; the clique on clause vertices and hubs is replaced by hub–coordinate edges, and two padding vertices are added. The graph `OV.toDiameter` has diameter three on instances with an orthogonal pair and two otherwise (`OV.ediam_toDiameter`). Its vertex and edge lists are written by two one-pass streams with binary counters, paired under `ComputableInO` within time `L (log L) ^ D` in the encoded instance length (`OV.exists_computableInO_toDiameter`). `DecidableInTimeO.decidableInTimeO_OV_of_diameter` then turns any procedure separating the two diameters within time `L ^ (2 - ε)` on encoded graphs into an `OV` decider within time `N ^ (2 - min ε 1 / 2) (d + 1) ^ 2`. This transfer is unconditional. The lower bounds are implications from `OVH`. `not_decidableInTimeO_diameter_of_OVH` states them in the encoded length `L`. `not_decidableInTimeO_diameter_size_of_OVH` uses `(n + m) ^ (2 - ε) + L`; the `L` term is needed, because a bound in the number of listed vertices and edges alone cannot read unbounded labels and would hold vacuously. The reduced graphs have `Θ(N d)` edges with unrestricted dimension, so the sparse-graph statement needs the low-dimension form of `OVH` and is not covered. The library neither proves nor refutes `OVH`; it refutes `SETH`, so hardness from `SETH` through `OVH_of_SETH` is vacuous.

Parameterized `Clique` hardness under `ETH` follows a uniform clause-grouping construction in [`CliqueGrouping`](../../CslibFrontier/Computability/Complexity/FineGrained/CliqueGrouping.lean) ([cygan2015][cygan2015]). For each `r ≥ 1` and CNF `φ` whose clauses all have width at most three, `SAT.groupClique r φ` partitions `φ` into `r` blocks of at most `⌈φ.length / r⌉ = (φ.length + r - 1) / r` clauses, creates one vertex per satisfying partial assignment per block (at most `r · 2 ^ (3 ⌈φ.length / r⌉)` vertices by `length_groupClique_vertices_le`), and connects compatible assignments across distinct blocks (`groupClique_mem_Clique_iff`). For `r ≥ 1`, a formula with a clause wider than three is sent to the empty graph with target `r`; when `r = 0`, every formula is sent to the empty graph with target one. Using `ComputableInPolyTime.exists_computableInO_pad` on `(r, φ)` gives a single polynomial exponent `D` independent of `r` (`exists_computableInO_groupClique`). The result uses `CliqueInstance` and `encCliqueInstance_mk_polyTime`, encoded by `encCliqueInstance`; its graph component uses the `Graph` record and `encGraph_mk_polyTime`. Vertex names and the clique target stay binary; the grouping count and explicit candidate bound supplied to the polynomial-time builder are unary. Choosing `r` large enough for each target rate `δ > 0` makes `DecidableInSubexpTime.threeSAT_of_clique_subexpVertex` and `threeSAT_of_clique_subexpEnc` transfer any `Clique` decider in time `f(k) · (|V| + 1) ^ o(k) · poly(|enc|)` or `f(k) · (|enc| + 1) ^ o(k)` (arbitrary real `f`) unconditionally to subexponential-time `ThreeSAT` in clause count. `ETH.not_clique_subexpVertex`, `ETH.not_clique_subexpEnc`, and `ETH.clique_not_mem_FPT` deduce the `ETH`-conditional exclusions (`Clique ∉ FPT`). As elsewhere, ETH consequences are implications from `ETH`; inspect the independent [native counting endpoints](native-counting.md) when interpreting that premise. The [CliqueGrouping tests](../../CslibFrontierTests/CliqueGrouping.lean) evaluate satisfiable, unsatisfiable, empty, and non-3-CNF inputs by `decide` and instantiate the reduction and `ETH` lower bounds.

## Source examples and evidence

The inspected [ReductionVariants tests](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ReductionVariants.lean#L1) give concrete prefix queries with OR, AND, XOR, and majority evaluators, including composition from two to four queries. These exhibit evaluator forms, not a separation theorem between the resulting reducibility relations. [LogSpaceReductions](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/LogSpaceReductions.lean#L1) supplies native logspace prefix and pair-query instances. [ReductionIsomorphism](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ReductionIsomorphism.lean#L1) uses word reversal as an isomorphism and bit-prefixing with `tail` as a length-increasing map with a total left inverse.

[Autoreducibility](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Autoreducibility.lean#L1) gives a concrete mitotic co-singleton and proves its many-one autoreducibility obstruction; [TuringAutoreducible](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/TuringAutoreducible.lean#L1) instantiates zero-query and parity-preserving examples. These are static inspections of existing test sources. The [model map](../model-map.md) indexes the semantic/resource variants and their explanations, with no fresh Lean compilation claim. The generic reduction kernel and the local bounded-reduction modules carry candidate upstream markers.

[complexitylib]: ../sources.md#complexitylib
[bermanhartmanis75]: ../sources.md#bermanhartmanis75
[cygan2015]: ../sources.md#cygan2015
