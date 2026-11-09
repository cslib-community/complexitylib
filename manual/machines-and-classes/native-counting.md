# Native exact counting and the SAT endpoints

The snapshot contains an unconditional native-machine theorem for exact fixed-width CNF counting, followed by the declarations `not_ETH`, `not_SETH`, and `satExponent_eq_zero`. These endpoints exercise the library's encodings, compositional cost calculus, algebraic algorithms, and statement-presentation machinery together. This chapter describes the actual contracts and their source correspondence. It is not an independent audit of every mathematical argument in their implementation. [complexitylib][complexitylib]

## Inputs, outputs and uniformity

A formula is a list of clauses; each clause is a list of natural-number variable labels paired with Boolean polarities. Repeated literals and clauses are allowed. Width counts literal occurrences, including repetitions. `numVars` counts distinct occurring variables, independent of the largest label. The output `modelCount` counts satisfying assignments on those occurring variables; setting all other variables to false supplies a total assignment for evaluation. [Displayed formula semantics](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L64)

There are two useful public contracts:

| Contract | Input and correctness domain | Result |
|---|---|---|
| [`exists_declaredCounter`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/CountingNativeEndpoint.lean#L721) | Unary declared variable count `N`, plus CNF with binary labels; a validity guard checks width and that every occurring label belongs to `range N` | Exact count over all `N` declared variables on valid inputs; zero on invalid inputs |
| [`exists_modelCounter`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/CountingNativeModelCount.lean#L190) | Plain CNF with arbitrary natural labels; correctness assumes clause width at most fixed `k` | Exact count over occurring variables; output unspecified outside the width bound, while resource bounds still apply there |

For each fixed `k`, the counter, constants and native machine are chosen before every input. This is neither a separate machine for each formula nor one asserted uniform bound over arbitrary varying `k`. The declared-variable counter accounts for unused declared variables; dense relabeling transfers it to the occurring-variable counter. The [composition proof](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/CountingNativeModelCount.lean#L179) proves the relabel-and-declare map polynomial-time and explicitly absorbs its time and space costs.

## Encoding and independent resource bounds

The input encoding nests framed lists and pairs with binary variable labels. Its exact length is

`L = number of clauses + sum over literal occurrences (10 + 8 * Nat.size(variable))`.

Thus a large label costs its binary length; arbitrary natural labels are not free. The natural output is binary. See [`length_encCNF`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L187) and the [encoding definitions](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L108).

Write `rho(n) = n * ln(ln(n + 16))^2 / sqrt(ln(n + 16))`. The occurring-variable theorem gives time `O(ceil(2^(A*rho(n))) * (L+1)^e)` and space `O((L+1)^b)`, for constants depending on `k`. The shift makes the expression defined at all natural sizes. The public statement includes widths zero and one, the empty formula, and formulas containing an empty clause. [Exact statement](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L194)

The [native machine contract](native-and-resources.md) supplies a finite deterministic multitape machine with read-only input and write-only output. Time counts transitions, and work space bounds visited cells over every run prefix. Here `ComputableInO` additionally charges encoded output length against the space budget. The two budgets are proved separately: polynomial workspace is not inferred from subexponential time. As with the underlying typed encoding predicates, there is no behavior requirement on arbitrary bitstrings outside the input encoding's image. [Displayed resource definition](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L139)

## Construction and correspondence to the manuscript

The [bridge's provenance account](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATBridge.lean#L22) identifies uniform disjoint counting sparsification, normalized sparse CNF counting, and a concrete bounded-incidence evaluator with exactness and native resource certificates. Disjointness supports summing leaf counts; support normalization and an outer declared-variable correction account for the assignment domain. The final public theorem discharges the internal branch-exactness premise by `evalBoundedIncidenceBranch_eq_rootCount`. It does not retain a hypothetical correct counter as a public assumption.

The cited manuscript is OpenAI's *The Exponential Time Hypothesis is False*, dated October 17 and revised October 25, 2026, pinned to `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Its TeX source was freshly retrieved and its title, dates, bound and proposition label checked in this review. [openaieth26][openaieth26]

| Manuscript claim or convention | Lean counterpart and material difference |
|---|---|
| Proposition 6.4, label `prop:interpolation-bound`: fixed-width exact counting with interpolation-scale exponent and polynomial space | `exists_declaredCounter` and `exists_modelCounter` expose this scale in native TM costs |
| Fixed `k >= 2`, declared `n >= 20`; small instances handled in the argument | Public Lean counter covers every fixed natural `k` and all natural sizes |
| Polynomial factor in declared variables and clauses | Lean uses the full encoded input length, including arbitrary binary labels; the plain-formula endpoint first relabels densely |
| Declared-variable count | Guarded declared-input endpoint first; occurring-variable endpoint obtained by a separately costed bridge |
| Theorem 1.1 and Appendix D give a sharper quantitative route | The inspected Lean endpoint asserts the weaker interpolation-scale bound; it must not be presented with that sharper exponent |

The source annotation locates Proposition 6.4 on manuscript pages 43–44 and cites Sections 3–6 and Appendices A–B. The TeX label and statement were checked; PDF pagination was not independently rendered in this pass. The inspected [pinned TeX statement](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex#L3570) is labelled `prop:interpolation-bound`; only its identity and selected statement were checked. This establishes the intended source mapping, not a fresh verification of the manuscript's full proof.

## Decision consequences and the ETH assumptions

The source defines `KSAT k` as the set of satisfiable formulas whose clauses all have length at most `k`. A decider must therefore reject formulas outside that width. The exponential-time class permits a polynomial factor in `L`, with rate measured in `numVars`. `satExponent k` is the infimum of attainable nonnegative exponential rates. These conventions follow the exponent-based treatment of fixed-width SAT; the historical source is Impagliazzo and Paturi. [impagliazzo01][impagliazzo01]

In the [displayed propositions](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/SubexponentialSATAbstract.lean#L152), ETH says some positive rate is unattainable for 3SAT; SETH says every improvement below rate one fails at some fixed width. The native endpoint proves [`decidableInSubexpTime_KSAT`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained/CountingNativeEndpoint.lean#L735), then the zero-exponent and negated-ETH/SETH declarations. These consequences quantify over the native machine model and the stated encoding. In the general definition, [`DecidableInSubexpTime`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/FineGrained.lean#L212) allows a different decider for each positive exponential rate. The exact-counter endpoint is stronger in this respect: it supplies one counter for each fixed width with the explicit interpolation-scale bound. Zero infimum exponent does not assert polynomial time or `P = NP`.

The library also retains [ETH-conditional Partial MCSP results](../circuits-logic-and-other-models/metacomplexity-and-methods.md). Their implications remain formal theorems, but, at this snapshot, the same library proves the negation of their ETH premise. They therefore do not supply an unconditional lower bound, and their premise cannot be described as an unrefuted assumption of this formal development. The underlying definitions and reductions remain separately inspectable; check this interaction before applying a conditional lower bound.

## Credit and assurance boundary

The abstract headers credit OpenAI, Samuel Schlesinger and Anton Kovsharov. The provenance docstring describes the joint port under issue #1226, including Erik Demaine and contributing Codex, Claude and Jetski workers, and credits Christian Reitwiessner for machine and encoding foundations. These are source-declared credits, not measured labor shares.

The dedicated abstract makes formula semantics, encodings, resource predicates and hypotheses visible, and its bridge transfers the native declarations without adding a mathematical premise. [Comparator contracts](../design-and-assurance/assurance.md) separately restate selected counting and ETH statements. This review read the endpoint, bridge and abstract and checked the manuscript's relevant statement. It did not rerun Lean, comparator, every constituent proof, or a specialist external review of the claimed refutation. This source-level account and the recorded CI evidence do not assert mathematical consensus.

[complexitylib]: ../sources.md#complexitylib
[impagliazzo01]: ../sources.md#impagliazzo01
[openaieth26]: ../sources.md#openaieth26
