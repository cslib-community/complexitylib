# Query and communication complexity

Information-access models isolate the amount of input that an algorithm must inspect or exchange. They deliberately make local computation free. Complexitylib represents the procedures themselves, states correctness predicates, then minimizes a specific cost. The distinction between structural worst-case cost, input-specific cost and expected cost is explicit. [complexitylib][complexitylib]

## Deterministic and randomized queries

[DecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Basic.lean#L55) is a finite binary tree with a queried input coordinate at each internal node and an arbitrary output at each leaf. Evaluation follows the branch selected by that coordinate. Coordinates may be repeated. Structural depth is one plus the larger child depth, while input-specific path cost and the set of distinct queries are separate definitions. Normal-form results remove repeated tests when a statement needs a reduced tree.

The deterministic complexity of a function is its least possible depth. On a finite coordinate type every function can be computed by querying all coordinates; the minimum is attained. Parity attains the full input dimension. Other modules connect decision-tree depth to sensitivity, block sensitivity, certificate complexity, Fourier/real polynomial degree and approximate degree. Representative endpoints include Huang's `degree <= sensitivity^2`, Midrijanis's `D <= degree * blockSensitivity`, and consequences such as `D <= 2 degree^3`. See [Huang](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Huang.lean), [Midrijanis](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Midrijanis.lean) and [Nisan–Szegedy](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/NisanSzegedy.lean).

The [superquadratic sensitivity separation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/SensitivitySeparation.lean) is a further major endpoint, adapted from [OpenAI's formalization at its pinned revision](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity). For every real C it gives a nonconstant Boolean function with `bs(f) > C s(f)^2`; a stronger family statement has a fixed exponent alpha greater than two and unbounded block sensitivity. Bridges identify the internal construction's measures with the public maximum sensitivity and block-sensitivity definitions. Certificate and decision-tree separations follow. This is neither average sensitivity nor a finite search experiment. The public statements and direct measure bridge were inspected here; their large internal construction and original source require a separate expert audit before making an independent mathematical endorsement.

[BiMonotoneComparison](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Separable.lean#L58) uses the same tree syntax with coordinates interpreted as monotone two-sided comparisons or comparisons of separable real scores. The cost is number of comparisons, regardless of the work needed to compute a score. Rectangle geometry gives leaf-count lower bounds.

[RandomizedDecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized.lean#L78) is a finite-support real simplex over deterministic trees. Its cost is the largest structural depth of any supported tree, and its error bound holds separately on every input. This is a worst-case randomized-query model, not an expected-query model. The natural-valued infimum has the documented convention zero for an impossible negative-error requirement; normal theorems assume nonnegative error.

[distributionalComplexity](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Yao.lean#L74) instead fixes a distribution on inputs and minimizes deterministic depth subject to average error. Yao's theorem equates randomized complexity to the supremum of these distributional complexities on the finite domain and supplies an attaining hard distribution. The [Nisan relation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized/Nisan.lean) gives `D <= 27 R_(1/3)^3`; approximate degree and block-sensitivity lower bounds are stated over the same cost convention.

Quantum queries use arbitrary input-independent isometries and a controlled phase oracle, charging only oracle uses. Their definitions and BBBV/polynomial/adversary/Grover endpoints are described in [algebraic and quantum models](algebraic-and-quantum.md). That chapter also covers the exponential separation between quantum and randomized queries for Simon's problem, whose classical side is the randomized decision-tree lower bound [simon_randomized_lower_bound](../../Complexity/Computability/QueryComplexity/Simon.lean).

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

Import `Complexity.Computability.Distributed.OrientedCycle.RoundComplexity`,
`Complexity.Computability.Distributed.OrientedCycle.MIS` or
`Complexity.Computability.Distributed.OrientedCycle.LCL.Flexible` (or one of the modules below
them) for deterministic synchronous algorithms in Linial's LOCAL model on consistently oriented
cycles.
The nodes of the oriented `n`-cycle are `ZMod n`: node `v` has predecessor `v - 1` and successor
`v + 1`, and `n = 0` gives the infinite oriented path `ℤ`. An
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
[Graph.lean](../../Complexity/Computability/Distributed/OrientedCycle/Graph.lean) connects the
model to Mathlib's graphs. `OrientedCycle.graph n` is the circulant graph on `ZMod n` with jump `1`,
which is `SimpleGraph.cycleGraph (k + 1)` for `n = k + 1` (`graph_succ_eq_cycleGraph`). For
`n ≠ 1`, `isProperColoring_iff_adj` identifies `IsProperColoring` with proper colourings of this
graph. `IsProperColoring.toColoring` and `Algorithm.ColorsCycle.exists_coloring` produce
`SimpleGraph.Coloring`s. The one-node cycle is excluded because its graph has no edges while its
node is its own successor.

[MIS.lean](../../Complexity/Computability/Distributed/OrientedCycle/MIS.lean) treats maximal
independent sets. `IsMIS s` is the local description of a marked set `s : ZMod n → Bool`, and
`isMIS_iff_maximal` matches it with Mathlib's `Maximal (graph n).IsIndepSet` for `n ≠ 1`.
`misOfColoring_run` turns a proper colouring with colours below `k` into an MIS within `k - 1`
rounds by greedy colour classes, on every oriented cycle and on the infinite path.
`misAlgorithm s` runs `fastThreeColoring s` for `s + 3` rounds and then the greedy step, through
the sequential composition `Algorithm.seq` of `Basic.lean` (`LocalRule.andThen` is `seq` after the
flooding algorithm of a rule). `Algorithm.FindsMIS A n t` asks that `A` marks an MIS after `t`
rounds for every bijection from the nodes onto `{0, …, n - 1}`. For `n ≠ 1`,
`misAlgorithm_findsMIS` finds an MIS within `s + 5` rounds when `log* n ≤ 2 s`. Conversely,
`colorOfMIS` turns an MIS into a proper 3-colouring in one round, so
`Algorithm.FindsMIS.logStar_le` gives `log* n ≤ 2t + 4` for every `t`-round MIS algorithm.
`exists_findsMIS_and_logStar_le` packages both directions for `n ≠ 1`. These reductions are
standard consequences of the 3-colouring bounds. Compose algorithms with `Algorithm.seq`; do not
convert an algorithm to a `LocalRule` with `Algorithm.toLocalRule` just to compose it, since
flooding its whole window makes `decide` impractical.

[LCL/Basic.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Basic.lean) and
[LCL/Flexible.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Flexible.lean)
cover part of the classification of LCL problems without inputs on directed cycles by Chang,
Studený and Suomela (TCS 2023, Table 1). A problem is a relation `R : L → L → Prop`, and
`LCL.IsSolution R ℓ` asks `R (ℓ v) (ℓ (v + 1))` at every node. Their node-edge-checkable problems
are the instance `LCL.nodeEdge` (`isSolution_nodeEdge_iff`, `nodeEdge_iff`), and MIS is an example
with `L = Bool × Bool` in the tests. `Algorithm.SolvesLCL A R n t` quantifies over identifier
bijections onto `{0, …, n - 1}`, like `ColorsCycle`. With a loop `R a a`, `Algorithm.const a`
solves `R` in `0` rounds (`Algorithm.solvesLCL_const`). Without a loop every solution is a proper
colouring, so `Algorithm.SolvesLCL.logStar_le` gives `log* n ≤ 2t + log* |L|` from Linial's bound,
and `Algorithm.SolvesLCL.exists_loop` is the resulting `ω(1)`/`o(log* n)` gap.
`LCL.IsFlexible R q K` asks for closed walks `q ⇝ q` of every length `m ≥ K`, stated with cslib's
`Relation.RelatesInSteps`; `IsFlexible.of_two_three` gives `K = 2` from walks of lengths `2` and
`3`.
`IsFlexible.exists_solvesLCL` solves such a problem for `n ≥ K` in
`(K - 1) (s + 2 · 3 ^ (K - 1) + 2) + 1` rounds when `log* n ≤ 2s`. The algorithm builds a
distance-`(K - 1)` colouring from `K - 1` dilated runs of `fastThreeColoringRule` (the
Cole–Vishkin algorithm as a `LocalRule`), takes its strict local minima as anchors and fills each
gap with a closed walk. These anchors are spaced like a ruling set but need not form the source's
maximal anchoring (Def. 3.8). `IsFlexible.exists_solvesLCL_and_logStar_le`
packages the `Θ(log* n)` bounds for flexible problems without a loop. The leading coefficient
`(K - 1) / 2` is not tight. These rules are compositions of `LocalRule`s (`LocalRule.comp`,
`LocalRule.apply_comp` in `Basic.lean`), so run them with `LocalRule.toAlgorithm_run` instead of
unfolding `Algorithm.run`. Problems with no flexible state (`Ω(n)` rounds, their Thm 6.5) are not
covered yet.

[Checked examples](../../ComplexityTests/Computability/Distributed/OrientedCycle.lean) run the
algorithms on a 5-cycle and on the infinite path. They also show that the one-node cycle has no
proper colouring and no MIS, and that two rounds of 3-colouring fail on the cycle of length
`2 ↑↑ 6 + 1`. The 5-cycle examples include the greedy MIS steps and the full `misAlgorithm 2` run.
[LCL examples](../../ComplexityTests/Computability/Distributed/LCL.lean) check that 3-colouring
and MIS are flexible without a loop, that 2-colouring has no flexible state, and the anchors and
filling on a 6-cycle.

Only oriented cycles are covered. General graphs with port numbering, Linial's `O(Δ²)` colouring,
`(Δ + 1)`-colouring and MIS on bounded-degree graphs, the CONGEST message-size bound,
randomized LOCAL algorithms and the `Ω(n)` row of the LCL classification remain open; see
`ROADMAP.md`.

## Known Limitations

The surveyed lower bounds concern total Boolean functions or explicitly stated relation/promise domains. When applying a bound, identify whether it assumes both-party output, finite distributions, a bounded-round alphabet, or a gadget-size regime. No query/communication bound here supplies a native runtime without a separate compilation/resource theorem.

[complexitylib]: ../sources.md#complexitylib
