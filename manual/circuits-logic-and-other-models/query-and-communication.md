# Query and communication complexity

Information-access models isolate the amount of input that an algorithm must inspect or exchange. They deliberately make local computation free. Complexitylib represents the procedures themselves, states correctness predicates, then minimizes a specific cost. The distinction between structural worst-case cost, input-specific cost and expected cost is explicit. [complexitylib][complexitylib]

## Deterministic and randomized queries

[DecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Basic.lean#L55) is a finite binary tree with a queried input coordinate at each internal node and an arbitrary output at each leaf. Evaluation follows the branch selected by that coordinate. Coordinates may be repeated. Structural depth is one plus the larger child depth, while input-specific path cost and the set of distinct queries are separate definitions. Normal-form results remove repeated tests when a statement needs a reduced tree.

The deterministic complexity of a function is its least possible depth. On a finite coordinate type every function can be computed by querying all coordinates; the minimum is attained. Parity attains the full input dimension. Other modules connect decision-tree depth to sensitivity, block sensitivity, certificate complexity, Fourier/real polynomial degree and approximate degree. Representative endpoints include Huang's `degree <= sensitivity^2`, Midrijanis's `D <= degree * blockSensitivity`, and consequences such as `D <= 2 degree^3`. See [Huang](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Huang.lean), [Midrijanis](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Midrijanis.lean) and [Nisan–Szegedy](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/NisanSzegedy.lean).

The [superquadratic sensitivity separation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/SensitivitySeparation.lean) is a further major endpoint, adapted from [OpenAI's formalization at its pinned revision](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity). For every real C it gives a nonconstant Boolean function with `bs(f) > C s(f)^2`; a stronger family statement has a fixed exponent alpha greater than two and unbounded block sensitivity. Bridges identify the internal construction's measures with the public maximum sensitivity and block-sensitivity definitions. Certificate and decision-tree separations follow. This is neither average sensitivity nor a finite search experiment. The public statements and direct measure bridge were inspected here; their large internal construction and original source require a separate expert audit before making an independent mathematical endorsement.

[BiMonotoneComparison](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Separable.lean#L58) uses the same tree syntax with coordinates interpreted as monotone two-sided comparisons or comparisons of separable real scores. The cost is number of comparisons, regardless of the work needed to compute a score. Rectangle geometry gives leaf-count lower bounds.

[RandomizedDecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized.lean#L78) is a finite-support real simplex over deterministic trees. Its cost is the largest structural depth of any supported tree, and its error bound holds separately on every input. This is a worst-case randomized-query model, not an expected-query model. The natural-valued infimum has the documented convention zero for an impossible negative-error requirement; normal theorems assume nonnegative error.

[distributionalComplexity](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Yao.lean#L74) instead fixes a distribution on inputs and minimizes deterministic depth subject to average error. Yao's theorem equates randomized complexity to the supremum of these distributional complexities on the finite domain and supplies an attaining hard distribution. The [Nisan relation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized/Nisan.lean) gives `D <= 27 R_(1/3)^3`; approximate degree and block-sensitivity lower bounds are stated over the same cost convention.

Quantum queries use arbitrary input-independent isometries and a controlled phase oracle, charging only oracle uses. Their definitions and BBBV/polynomial/adversary/Grover endpoints are described in [algebraic and quantum models](algebraic-and-quantum.md).

## Deterministic communication and its variants

[Protocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Protocol.lean#L92) is a two-party binary protocol tree. At an Alice node the next bit is any function of Alice's input; similarly for Bob. Leaves carry the output, so the transcript determines an answer known to both players. The principal cost is maximum transmitted bits. Rectangle partitions, fooling sets and matrix-rank methods support lower bounds. Deterministic equality costs n+1 bits for n at least one under this both-player-output convention.

The relation-solving predicate is defined on explicit input domains, and extended-natural complexity can be infinite if the relation has no valid answer on some pair. Local computations are uncharged. These choices make a communication lower bound precise without asserting anything about participants' running time.

| Variant | Representation and cost |
|---|---|
| [DagProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/DagProtocol.lean#L76) | Acyclic graph of local tree protocols; cost is graph size plus maximum local protocol depth, not total bits along a graph path. |
| [RoundProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/RoundProtocol.lean#L75) | At most a bounded number of messages from a chosen alphabet; message bits require an additional alphabet-size analysis. |
| [PublicCoin](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Randomized.lean#L84) | PMF over deterministic protocols; worst supported depth in extended naturals; countable support is allowed. |
| [PrivateCoin](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Randomized.lean#L221) | Deterministic protocol on inputs augmented by independent finite uniform private tapes. |
| [IsCover](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Nondeterministic/Basic.lean#L139) | Cover by valid monochromatic rectangles; k certificate bits provide at most `2^k` rectangles. |

The nondeterministic cover convention does not charge a final output announcement. Its relationship to a tree in which both parties know the answer therefore has an explicit small overhead. Public-coin PMFs and finite-support randomized query trees are different probability representations; neither should be silently substituted for the other.

## Major communication bridges and bounds

The Karchmer–Wigderson relation asks parties holding opposite outputs of a Boolean function to find a differing coordinate. The monotone version asks for the ordered 1-versus-0 coordinate. Circuit/formula modules prove correspondences with De Morgan or monotone formula depth and leaf count. This bridge turns lower bounds on communication into formula lower bounds, preserving the relevant cost convention. See [Boolean KW](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/KarchmerWigderson.lean) and [monotone KW](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Monotone/KarchmerWigderson.lean).

The communication development includes public-coin equality protocols and linear lower bounds for disjointness and inner product at bounded error, using corruption and discrepancy methods. Its Newman theorem replaces public randomness by a finite seed selection at an additive communication/error cost; the finite statement keeps the input-domain cardinalities and error increment visible. See [communication abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CommunicationAbstract.lean) for the precise finite statements and their hypotheses.

The deterministic lifting theorem composes a Boolean function with an index gadget. For the theorem's parameters m and tau, a protocol of cost c yields a decision tree of depth d with `(m/tau)^d <= 4^c`, assuming `4 <= tau`, `tau^2 <= m` and `320 n^2 (log2 m+1) <= tau`. Choosing tau around the square root of m gives a gadget on the order of `n^4 log^2 n`, rather than the smaller gadgets of more recent sharp lifting theorems. This is a documented quantitative scope choice. The source is [the lifting simulation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Lifting/Simulation.lean).

## Distributed rounds in the LOCAL model

Import `Complexity.Computability.Distributed.OrientedCycle.RoundComplexity` (or one of the
modules below it) for deterministic synchronous algorithms in Linial's LOCAL model on
consistently oriented cycles. The nodes of the oriented `n`-cycle are `ZMod n`: node `v` has
predecessor `v - 1` and successor `v + 1`, and `n = 0` gives the infinite oriented path `ℤ`. An
`Algorithm I S O` has an initial state from each node's input, a step function from the round
number and the predecessor's, own and successor's states, and an output map. Messages and local
computation are free, so exchanging whole states loses no generality. `MessageAlgorithm` with
explicit messages reduces to it (`MessageAlgorithm.toAlgorithm_state`). The cost is the number of
rounds. The round number is common knowledge. Algorithms are non-uniform: one may be chosen for
each `n`. Identifiers are natural numbers, and `Algorithm.ColorsCycle A n t c` asks for a proper
colouring with colours below `c` after `t` rounds for every bijection from the nodes onto
`{0, …, n - 1}`. The usual identifiers `{1, …, n}` are the same up to a shift:
`Algorithm.colorsCycle_comapInput_succ_iff` moves results between the two conventions through
`Algorithm.comapInput`. For `n = 0` no identifier assignment qualifies, so `ColorsCycle 0 t c` is
vacuous. Results for the infinite oriented path are stated for `Algorithm.run` directly, as in
`threeColoring_run` and `fastThreeColoring_run`.

The view formulation is proved rather than assumed. `Algorithm.state_eq_viewState` and
`Algorithm.run_eq_apply` say that `r` rounds compute a `LocalRule` of radius `r`, a function of
the input window at offsets `-r, …, r`. `LocalRule.toAlgorithm_run` gives the converse by flooding.
Lower bounds are therefore proved for rules and transferred to algorithms, and
`LocalRule.andThen` lets an algorithm first compute a rule and then continue.

[ColeVishkin.lean](../../Complexity/Computability/Distributed/OrientedCycle/ColeVishkin.lean)
proves the Cole–Vishkin upper bound. `cvColor a b = 2 i + aᵢ`, for the least bit `i` where `a`
and `b` differ, turns colours below `M` into colours below `2 ⌈log₂ M⌉`. `threeColoring_run`
3-colours in `log* N + 3` rounds from any proper colouring with colours below `N`, and
`fastThreeColoring_run` in `s + 3` rounds when `log* N ≤ 2 s`, performing two reduction steps per
round. [Linial.lean](../../Complexity/Computability/Distributed/OrientedCycle/Linial.lean) proves
Linial's lower bound `Algorithm.ColorsCycle.logStar_le_of_three`, `log* n ≤ 2t + 2`, by the
Laurinharju–Suomela speedup lemma on shift colourings (`Cslib.IsShiftColoring` in
`Complexity.Foundations.Combinatorics.ShiftColoring`). The general form
`Algorithm.ColorsCycle.logStar_le` allows `c` colours: `log* n ≤ 2t + log* c`.
`exists_colorsCycle_three_and_logStar_le` packages both directions: `⌈(log* n) / 2⌉ + 3` rounds
suffice for `n ≠ 1`, and any algorithm needs `log* n ≤ 2t + 2`, so the optimum is known up to an
additive `4`. `Nat.logStar` and `Nat.twoTower` live in `Complexity.Foundations.Data.Nat.LogStar`;
use `Nat.logStar_le_iff` rather than unfolding, and `decide` for small values. `Nat.twoTower` is a
structurally recursive copy of Mathlib's `hyperoperation 4 2` (`Nat.twoTower_eq_hyperoperation`),
kept because `decide` cannot evaluate the well-founded `hyperoperation`.
[Checked examples](../../ComplexityTests/Computability/Distributed/OrientedCycle.lean) run the
algorithms on a 5-cycle and on the infinite path. They also show that the one-node cycle has no
proper colouring and that two rounds fail on the cycle of length `2 ↑↑ 6 + 1`.

Only oriented cycles are covered. General graphs with port numbering, Linial's `O(Δ²)` colouring,
the CONGEST message-size bound and randomized LOCAL algorithms remain open; see `ROADMAP.md`.

## Locally decodable codes

[LocallyDecodable/Basic](../../Complexity/Computability/LocallyDecodable/Basic.lean) is the local-decoding model. A code is `C : (ι → Bool) → P → Γ`. A decoder for the bit `i` is a `ProbOracleComp (fun _ : P => Γ) Bool`: it draws private uniform coins and queries positions of a received word `y : P → Γ`, possibly adaptively. `decodeLaw program y` is its output law with the queries answered by `y`. The query budget is the worst-case `ProbOracleComp.IsQueryBounded`, which counts queries on every path and not private samples. `IsLocalDecoder C q δ ε A` asks for at most `q` queries and success probability at least `1/2 + ε` from every word within Hamming distance `δ |P|` of a codeword. `IsSmoothDecoder C q c ε A` asks only for success on codewords, and for each position to be read at most `c / |P|` times in expectation. `expectedReads` is an `OracleComp.expectedCost` from [QueryCount/Expected](../../Complexity/Languages/Probabilistic/QueryCount/Expected.lean). This expected-reads notion bounds the probability of reading a position, and it implies Katz–Trevisan smoothness. `nonadaptive coins Q output` builds a non-adaptive decoder, and its reads do not depend on the received word (`hasObliviousReads_nonadaptive`).

The [Hadamard decoder](../../Complexity/Computability/LocallyDecodable/Hadamard.lean) reads `y r` and `y (eᵢ + r)` for a uniform `r`. It is a `(2, δ, 1/2 − 2δ)` local decoder for every `δ` and a `(2, 2, 1/2)` smooth decoder. [Smoothing](../../Complexity/Computability/LocallyDecodable/Smoothing.lean) proves Katz–Trevisan smoothing: `isSmoothDecoder_mask_heavyPositions` turns a `(q, δ, ε)` local decoder with oblivious reads into a `(q, q/δ, ε)` smooth decoder. It does so by answering queries to the heavy positions from a fixed word. Every non-adaptive decoder and every one-query decoder has oblivious reads. Smoothing adaptive decoders that make several queries is not covered. [OneQuery](../../Complexity/Computability/LocallyDecodable/OneQuery.lean) gives an explicit form of the Katz–Trevisan one-query bound. `IsSmoothDecoder.four_mul_card_mul_sq_le` proves `4 |ι| ε² ≤ c² (|Γ| − 1)` for `(1, c, ε)` smooth decoders with `0 ≤ ε`. `IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le` proves `4 δ² |ι| ε² ≤ |Γ| − 1` for `(1, δ, ε)` local decoders, whatever the length `|P|`. The proof uses `BitString.sq_sum_sum_abs_fourierCoeff_fiber_le` from [FiberWeight](../../Complexity/Foundations/BooleanAnalysis/FiberWeight.lean), a bound on the degree-one weight of the fibers of a map from the cube. The [checked examples](../../ComplexityTests/LocallyDecodable.lean) include the Hadamard and smoothed Hadamard decoders and a repetition code that attains the one-query bound. They also show that no two-bit binary code is `(1, 1, 1/2)` smooth. The general Katz–Trevisan bound `n ≥ Ω(k^{q/(q−1)})` and the two-query exponential bounds remain open; see `ROADMAP.md`.

## Known Limitations

The surveyed lower bounds concern total Boolean functions or explicitly stated relation/promise domains. When applying a bound, identify whether it assumes both-party output, finite distributions, a bounded-round alphabet, or a gadget-size regime. No query/communication bound here supplies a native runtime without a separate compilation/resource theorem.

[complexitylib]: ../sources.md#complexitylib
