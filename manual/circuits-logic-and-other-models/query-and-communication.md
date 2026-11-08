# Query and communication complexity

Information-access models isolate the amount of input that an algorithm must inspect or exchange. They deliberately make local computation free. Complexitylib represents the procedures themselves, states correctness predicates, then minimizes a specific cost. The distinction between structural worst-case cost, input-specific cost and expected cost is explicit. [complexitylib][complexitylib]

## Deterministic and randomized queries

[DecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Basic.lean#L55) is a finite binary tree with a queried input coordinate at each internal node and an arbitrary output at each leaf. Evaluation follows the branch selected by that coordinate. Coordinates may be repeated. Structural depth is one plus the larger child depth, while input-specific path cost and the set of distinct queries are separate definitions. Normal-form results remove repeated tests when a statement needs a reduced tree.

The deterministic complexity of a function is its least possible depth. On a finite coordinate type every function can be computed by querying all coordinates; the minimum is attained. Parity attains the full input dimension. Other modules connect decision-tree depth to sensitivity, block sensitivity, certificate complexity, Fourier/real polynomial degree and approximate degree. Representative endpoints include Huang's `degree <= sensitivity^2`, Midrijanis's `D <= degree * blockSensitivity`, and consequences such as `D <= 2 degree^3`. See [Huang](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Huang.lean), [Midrijanis](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Midrijanis.lean) and [Nisan–Szegedy](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/NisanSzegedy.lean).

The [superquadratic sensitivity separation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/SensitivitySeparation.lean) is a further major endpoint, adapted from [OpenAI's formalization at its pinned revision](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity). For every real C it gives a nonconstant Boolean function with `bs(f) > C s(f)^2`; a stronger family statement has a fixed exponent alpha greater than two and unbounded block sensitivity. Bridges identify the internal construction's measures with the public maximum sensitivity and block-sensitivity definitions. Certificate and decision-tree separations follow. This is neither average sensitivity nor a finite search experiment. The public statements and direct measure bridge were inspected here; their large internal construction and original source require a separate expert audit before making an independent mathematical endorsement.

[BiMonotoneComparison](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/DecisionTree/Separable.lean#L58) uses the same tree syntax with coordinates interpreted as monotone two-sided comparisons or comparisons of separable real scores. The cost is number of comparisons, regardless of the work needed to compute a score. Rectangle geometry gives leaf-count lower bounds.

[RandomizedDecisionTree](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized.lean#L78) is a finite-support real simplex over deterministic trees. Its cost is the largest structural depth of any supported tree, and its error bound holds separately on every input. This is a worst-case randomized-query model, not an expected-query model. The natural-valued infimum has the documented convention zero for an impossible negative-error requirement; normal theorems assume nonnegative error. `RandomizedDecisionTree.mapOutput g` post-processes the output by relabelling leaves with `DecisionTree.map g`. It adds no depth (`depth_mapOutput_le`) and no error against `g ∘ f` (`errorProb_mapOutput_le`), so lower bounds for `g ∘ f` transfer to `f`. More generally, `RandomizedDecisionTree.mapTree φ` applies a tree transformation `φ` to the drawn tree. It adds the depth that `φ` adds (`depth_mapTree_le`) and no error when `φ` preserves correctness (`errorProb_mapTree_le`). The Simon search lower bounds are derived from the decision version in these two ways: `mapOutput` for the variant that includes `s = 0`, and a verification appended by `mapTree` for the problem with `s ≠ 0`. For search problems with many distinct answers, `RandomizedDecisionTree.card_mul_one_sub_le_two_pow_depth` ([Randomized/Counting.lean](../../Complexity/Computability/QueryComplexity/Randomized/Counting.lean)) gives the counting lower bound `|S| (1 − ε) ≤ 2^q`; Bernstein–Vazirani uses it.

The [zero-error module](../../Complexity/Computability/QueryComplexity/Randomized/ZeroError.lean) adds the expected-query view on the same simplex type, not a second randomized-tree type. `RandomizedDecisionTree.expectedCost` is the weighted average of the queries the drawn tree actually makes on one input (`DecisionTree.cost`, counting repeats), and `QueryComplexity.zeroErrorComplexity` is the real-valued Las Vegas complexity `R₀`, which takes the infimum over always-correct trees of the worst-input expected cost. It satisfies `R₀ <= D`. Worst-case `randomizedComplexity 0` equals `D`, so `R₀` is the measure that can drop below it. `RandomizedDecisionTree.uniformMixture` builds the algorithm whose coins select a deterministic tree uniformly. For the complete binary AND–OR tree `T_{2,k}` on `n = 4^k` leaves, with AND at the root as in Motwani–Raghavan, every deterministic tree reads all leaves on some input, so `D = n`. This is in [AndOrTree](../../Complexity/Computability/QueryComplexity/AndOrTree.lean), via the Rivest–Vuillemin top-Fourier-coefficient criterion in [Evasive](../../Complexity/Computability/DecisionTree/Evasive.lean). The directional algorithm in [AndOrTree/Randomized](../../Complexity/Computability/QueryComplexity/AndOrTree/Randomized.lean) has an exact expected-cost recurrence. From it come Motwani–Raghavan's `R₀ <= 3^k = n^(log₄ 3)` and Snir's sharp `R₀ <= (α - 1/2) n^(log₂ α)` with `α = (1 + √33)/4`, about `n^0.7537`. Nonconstant functions have `1 <= R₀`. The AND-rooted and OR-rooted orientations transfer through [dual trees](../../Complexity/Computability/DecisionTree/Dual.lean), which swap children and negate leaves. The matching Saks–Wigderson lower bound `Ω(n^(log₂ α))` is not formalized.

[distributionalComplexity](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Yao.lean#L74) instead fixes a distribution on inputs and minimizes deterministic depth subject to average error. Yao's theorem equates randomized complexity to the supremum of these distributional complexities on the finite domain and supplies an attaining hard distribution. The [Nisan relation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/QueryComplexity/Randomized/Nisan.lean) gives `D <= 27 R_(1/3)^3`; approximate degree and block-sensitivity lower bounds are stated over the same cost convention.

Quantum queries use arbitrary input-independent isometries and a controlled phase oracle, charging only oracle uses. Their definitions and BBBV/polynomial/adversary/Grover endpoints are described in [algebraic and quantum models](algebraic-and-quantum.md). That chapter also covers the exponential separation between quantum and randomized queries for Simon's problem, whose classical side is the randomized decision-tree lower bound [simon_randomized_lower_bound](../../Complexity/Computability/QueryComplexity/Simon.lean). It also covers Deutsch–Jozsa. The deterministic bound `N/2 + 1` is in [DeutschJozsa](../../Complexity/Computability/QueryComplexity/DeutschJozsa.lean). Three random queries with error `1/4` on the promise ([Randomized/DeutschJozsa](../../Complexity/Computability/QueryComplexity/Randomized/DeutschJozsa.lean), through `RandomizedDecisionTree.errorProb_uniformMixture`) show that its quantum advantage holds only for exact algorithms.

## Adaptive cell-probe trees and schemes

[`Complexity.Computability.CellProbe.Defs`](../../Complexity/Computability/CellProbe/Defs.lean), [`Complexity.Computability.CellProbe.DecisionTree`](../../Complexity/Computability/CellProbe/DecisionTree.lean), and [`Complexity.Computability.CellProbe.Randomized`](../../Complexity/Computability/CellProbe/Randomized.lean) formalize the adaptive cell-probe model (`Cslib.CellProbe`), originating in Minsky and Papert and developed in dynamic form by Fredman and static form by Yao. In a time-invariant deterministic `Scheme`, persistent state between operations consists solely of `S` cells of `w`-bit words (`Mem S w := Fin S → Fin (2 ^ w)`), with no persistent registers across operation boundaries; `IndexedScheme` is a **time-aware relaxation** whose `step` additionally receives the global operation index `t : ℕ` (a free clock outside cell memory). Each deterministic operation is an adaptive read/write decision tree `ProbeTree S w α` (`OracleComp (@ProbeOp.Result S w) α`): reading cell `i` branches `2 ^ w`-ways on `m i`, writing `v` updates cell `i` and returns `PUnit`, reads and writes are charged separately at one probe each (at most twice the cost of combined read-and-write nodes), and local computation and initial memory (`Scheme.init`, equivalent for deterministic schemes to `zeroMem` via uncharged XOR relabeling) charge zero probes.

Structural worst-case height `ProbeTree.depth`, input-specific path cost `ProbeTree.probes m`, and the distinct accessed footprint `ProbeTree.probedCells m` are kept separate (`card_probedCells_le_probes`, `probes_le_depth`). Frame lemmas (`ProbeTree.nextMem_eq_of_notMem_probedCells`, `IndexedScheme.nextMem_runInterval_eq_of_notMem_probedCellsInterval`) show that unprobed cells retain their initial values, while `ProbeTree.run_eq_of_eq_on_probedCells` and `IndexedScheme.runInterval_eq_of_eq_on_probedCellsInterval` establish cell-probe locality: if two memories agree on the cells probed from the first memory, replaying the tree or operation slice from the second memory yields the same output transcript, probe count, probed-cell set, and post-memory contents on all probed cells. In `Complexity/Computability/CellProbe/Defs.lean`, `ProbeTree.card_le_pow_depth_of_injective` and `ProbeTree.clog_le_depth_of_injective` prove the standard `2 ^ w`-ary branching bound `K ≤ (2 ^ w) ^ t.depth` (`Nat.clog (2 ^ w) K ≤ t.depth`, for any `w : ℕ`) whenever `t` distinguishes `K` memory states, while in `DecisionTree.lean`, `ProbeTree.ofDecisionTree` embeds static 1-bit `DecisionTree (Fin S) α` trees as read-only `ProbeTree S 1 α` computations preserving output, `probes`, `probedCells`, and `depth`.

`RandProbeTree S w α` (`ProbOracleComp (@ProbeOp.Result S w) α`) adds private finite-uniform coin draws (`unifSpec`) at zero probe cost, with `ℝ≥0∞`-valued expectation `RandProbeTree.expectedProbes` and single-operation coin-fixing equivalence `RandProbeTree.run_eq_coinLaw_bind_fixCoins`. Over oblivious operation sequences, `Randomized.Scheme.exists_det_indexedScheme_le_expectedSeqProbes` gives the **averaging (coin-fixing) argument, the easy direction of Yao's principle, for zero-error (Las Vegas) schemes** (`Cslib.Probability.PMF.exists_mem_support_tsum_mul_le_tsum_mul`): `hcorr` requires every supported transcript on `correctSeqs` to satisfy `Good`, so bounded-error (Monte Carlo) schemes and adaptive sequence adversaries are out of scope. Taking an explicit finite `opsAlphabet : Finset Op` and `horizon : ℕ` and separating `correctSeqs` from `hardDist`, it produces a step-indexed `IndexedScheme` in `indexedSchemeLaw`'s support, so deterministic lower bounds paired with it must hold against time-aware `IndexedScheme`s. In the random-initial-memory / coin-free-step specialization (`IsCoinFree`, where randomness lives only in the initial-memory distribution `init` and operations observe it only by probing cells), `Randomized.Scheme.exists_det_scheme_le_expectedSeqProbes` returns a time-invariant `CellProbe.Scheme` without `opsAlphabet` or `horizon`.

The complete [checked client](../../ComplexityTests/CellProbe.lean) exercises read/write locality and frame lemmas on distinct memories, the `DecisionTree` adapter, a tight `K = 17` lower and upper bound in `Mem 3 2` (`3 ≤ t.depth`, plus `w = 0`), and zero-error coin-fixing over an infinite operation type where `correctSeqs` strictly extends `hardDist.support` (plus a non-trivial write-read check on uniform random initial memory). Run `scripts/build.sh --wfail --iofail ComplexityTests.CellProbe`. For `Cslib.DataStructure` state-transition and oblivious-sequence implementation certificates over `Cslib.CellProbe`, see [state transitions and memory](../algorithms-and-memory/memory-specifications.md#cell-probe-state-transition-and-oblivious-sequence-implementations); transferring a cell-probe lower bound to Word-RAM instruction counts requires a separate machine-to-cell-probe simulation bridge.

[`Complexity.Computability.CellProbe.Chronogram`](../../Complexity/Computability/CellProbe/Chronogram.lean) is the problem-independent bookkeeping behind Fredman and Saks's chronogram method for dynamic lower bounds (history in Pătraşcu–Demaine 2006, §3.1). An `IndexedScheme` runs consecutive operation segments `seg 0, seg 1, …` from step `t₀` and memory `m₀`; `segStart` and `segMem` give the step and memory at which segment `j` starts. `laterCells L j` collects the cells probed by segments `j + 1, …, L - 1`, and `lastCells L j` the cells probed by segment `j` and by no later segment. These sets are defined by *probes*, not writes: a later read also removes a cell from `lastCells`. This suffices because a cell that no later segment probes keeps its contents, and the cells probed later are exactly those whose final contents the overlay records. `overlayMem L j` lays the final contents of `laterCells` over the memory before segment `j`. It agrees with the memory after all `L` segments outside `lastCells L j` (`overlayMem_eq_of_notMem_lastCells`) and differs from `segMem j` on at most `#laterCells` cells (`hammingDist_overlayMem_le`), which is at most `d * Σ_{j < k < L} |seg k|` under a uniform step-depth bound `d` (`card_laterCells_le`). The sets `lastCells L j` for `j < L` are pairwise disjoint, so a probe set `P` meets at most `#P` of them (`card_filter_lastCells_le`). A query tree whose probes on the final memory avoid `lastCells L j` answers identically, with the same probe count, on the overlay (`run_overlayMem_eq`). `card_filter_hammingDist_le_le_pow` bounds the number of memories within Hamming distance `r` of a fixed memory by `(S * (2 ^ w - 1) + 1) ^ r`, a special case of the alphabet-generic `Code.card_filter_hammingDist_le_le_pow` in [`Complexity.Foundations.Data.Code.HammingBound`](../../Complexity/Foundations/Data/Code/HammingBound.lean); this is the count of possible overlays in an encoding argument, about `log S + w` bits per recorded cell. The module proves no lower bound by itself; [`Complexity.DataStructure.PrefixSums.CellProbe.LowerBound`](../../Complexity/DataStructure/PrefixSums/CellProbe/LowerBound.lean), described next, uses it. Its [checked client](../../ComplexityTests/CellProbeChronogram.lean) uses an adaptive copy-and-write scheme in which a later read alone removes a cell from `lastCells`. It also shows that the overlay differs from the final memory exactly on a last-touched cell, and that a query probing that cell answers differently, so the disjointness hypothesis of `run_overlayMem_eq` is needed. Run `scripts/build.sh --wfail --iofail ComplexityTests.CellProbeChronogram`.

[`Complexity.DataStructure.PrefixSums.CellProbe.LowerBound`](../../Complexity/DataStructure/PrefixSums/CellProbe/LowerBound.lean) proves the Fredman–Saks chronogram lower bound for dynamic prefix parity: partial sums over `ZMod 2`, where `update i b` sets bit `i` and `query i` returns `A 0 + ⋯ + A i`, as in Pătraşcu–Demaine 2006, §2.1. `AnswersQueries D` says that a deterministic `IndexedScheme (Op n) Result S w` answers every query correctly after every operation sequence. Suppose updates have depth at most `t_u`, `L β ^ L ≤ n`, `β ≥ 4` and `(S 2 ^ w + 1) ^ (8 t_u) ≤ 2 ^ β`. Then the average query over the hard distribution makes at least `L / 64` probes (`card_mul_le_sum_probes`, `exists_le_mul_probes`), and a query-depth bound `t_q` gives `L ≤ 64 t_q` (`le_mul_of_answersQueries`). With `S ≤ 2 ^ w`, choosing `β = max 4 (8 t_u (2 w + 1))` and `L = ⌊log_β n / 2⌋` gives `log_β n ≤ 128 t_q + 1` (`log_le_of_answersQueries`). This is the trade-off `t_q = Ω(lg n / (lg b + lg t_u))` for word size `b` that Pătraşcu–Demaine §3.1 attributes to Fredman–Saks 1989.

The hard instance `hardUpdates hn X` has `L` epochs. Epoch `j` writes the `β ^ (L - j)` bits `X j` at positions `k β ^ j L + j`, and query `q < β ^ L` then answers `Σ_j prefixParity (X j) (q / β ^ j)` (`prefixParity_hardUpdates`). For each epoch the proof counts the *bad* queries, those whose probes meet `lastCells`, and replays the others on the overlay. At most `(S 2 ^ w + 1) ^ (2 t_u β ^ (L - j - 1))` overlays exist, and an overlay determines the prefix-parity vector of epoch `j` up to a Hamming ball of radius `β ^ (L - j) / 16`. Hence at most half of the values of epoch `j` leave fewer than `β ^ L / 32` bad queries. Finally, the bad queries of distinct epochs are charged to distinct probed cells.

The scope is deterministic schemes with worst-case update depth, and the constants are not optimized. Amortized updates, Las Vegas randomization and the stronger Pătraşcu–Demaine trade-offs remain open in [#3207](https://github.com/cslib-community/complexitylib/issues/3207). The [checked client](../../ComplexityTests/CellProbeFredmanSaks.lean) does three things:

- It checks the hard-instance layout and answer formula for `β = L = 2`.
- It proves correct the one-cell-per-bit scheme (update depth `1`, query depth `n`). That scheme meets all hypotheses of the hard-instance form with one epoch (`n = 64`, `w = 1`, `β = 64`) and with two (`n = 131072`, `w = 1`, `β = 256`), and of the logarithmic form (`n ≤ 2 ^ w`).
- It shows that a probe-free scheme answering `0` meets every hypothesis except `AnswersQueries`, which the theorem then refutes.

Run `scripts/build.sh --wfail --iofail ComplexityTests.CellProbeFredmanSaks`.

## Deterministic communication and its variants

[Protocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Protocol.lean#L92) is a two-party binary protocol tree. At an Alice node the next bit is any function of Alice's input; similarly for Bob. Leaves carry the output, so the transcript determines an answer known to both players. The principal cost is maximum transmitted bits. Rectangle partitions, fooling sets and matrix-rank methods support lower bounds. Deterministic equality costs n+1 bits for n at least one under this both-player-output convention.

The relation-solving predicate is defined on explicit input domains, and extended-natural complexity can be infinite if the relation has no valid answer on some pair. Local computations are uncharged. These choices make a communication lower bound precise without asserting anything about participants' running time.

| Variant | Representation and cost |
|---|---|
| [DagProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/DagProtocol.lean#L76) | Acyclic graph of local tree protocols; cost is graph size plus maximum local protocol depth, not total bits along a graph path. |
| [RoundProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/RoundProtocol.lean#L75) | At most a bounded number of messages from a chosen alphabet; message bits require an additional alphabet-size analysis. |
| [PublicCoin](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Randomized.lean#L84) | PMF over deterministic protocols; worst supported depth in extended naturals; countable support is allowed. |
| [PrivateCoin](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Randomized.lean#L221) | Deterministic protocol on inputs augmented by independent finite uniform private tapes. |
| [IsCover](../../Complexity/Computability/Communication/Nondeterministic/Basic.lean) | Cover by valid monochromatic rectangles, indexed by any type; k certificate bits provide at most `2^k` rectangles (`HasCover`), and [coverNumber](../../Complexity/Computability/Communication/Nondeterministic/CoverNumber.lean) counts rectangles directly. |
| [PrivateCoin.SolvesUnbounded](../../Complexity/Computability/Communication/UnboundedError.lean) | Private-coin protocol whose error is strictly below `1/2` on every input; cost is depth, with any finite number of private random bits. |

Two building blocks bound concrete protocols. In `Protocol.ecomplexityFun_le_clog_card_finset_succ`, Alice sends a value from a known finite set and Bob answers, at a cost of `⌈log₂ |s|⌉ + 1` bits. [Binary search](../../Complexity/Computability/Communication/BinarySearch.lean) (`Protocol.exists_search_lt`) finds an index at which Bob's integer weight is below Alice's, given that Bob's total over a list is below hers. It needs `⌈log₂ |l|⌉` comparisons of partial sums, each of cost at most `c`. Krajíček's cutting-planes interpolation uses both.

The nondeterministic cover convention does not charge a final output announcement. Its relationship to a tree in which both parties know the answer therefore has an explicit small overhead. Public-coin PMFs and finite-support randomized query trees are different probability representations; neither should be silently substituted for the other.

## Major communication bridges and bounds

The Karchmer–Wigderson relation asks parties holding opposite outputs of a Boolean function to find a differing coordinate. The monotone version asks for the ordered 1-versus-0 coordinate. Circuit/formula modules prove correspondences with De Morgan or monotone formula depth and leaf count. This bridge turns lower bounds on communication into formula lower bounds, preserving the relevant cost convention. See [Boolean KW](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/KarchmerWigderson.lean) and [monotone KW](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Monotone/KarchmerWigderson.lean).

The communication development includes public-coin equality protocols and linear lower bounds for disjointness and inner product at bounded error, using corruption and discrepancy methods. Its Newman theorem replaces public randomness by a finite seed selection at an additive communication/error cost; the finite statement keeps the input-domain cardinalities and error increment visible. See [communication abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CommunicationAbstract.lean) for the precise finite statements and their hypotheses.

[Information cost](../../Complexity/Computability/Communication/Information.lean) measures what a protocol's transcript reveals, not how many bits it sends. It uses the mutual and conditional mutual information of [MutualInformation](../../Complexity/Probability/MutualInformation.lean). Both costs are stated for a joint law of `(X, Y, T)`, with `T` the leaf reached, so they apply to any protocol model with a transcript law. `internalInfoCost` is `I(T; Y | X) + I(T; X | Y)`, what each player learns about the other's input. `externalInfoCost` is `I(T; XY)`, what an observer learns. `Protocol.transcriptLaw` and `PrivateCoin.transcriptLaw` build the law from inputs drawn from `μ`; private coins are uniform and independent of the inputs. A public-coin protocol's cost is the average over its coins of the cost of the deterministic protocol they select, following Braverman and Rao (Lemma 3.13). For all three models, internal cost is at most external cost, which is at most the depth. This strengthens Braverman–Rao's Lemma 3.14 (information at most communication) by going through the external cost; their proof bounds each transmitted bit's two terms by `1` using the same per-bit independence. The proof is an induction on the tree. It keeps the invariant that, conditioned on the transcript so far, the players' views have law of product form `w(x, y) α(u) β(v)`. With independent inputs the two costs agree, by the information identity `externalInfoCost_sub_internalInfoCost`. Public-coin costs are valued in `ℝ≥0∞`, like public-coin depth, and the deterministic and private-coin costs are real, so the two meet through `ENNReal.ofReal`. `PublicCoin.infoComplexity` is the least internal cost under `μ` of a public-coin protocol solving the relation with error at most `ε` on every input pair in `A × B`. It is at most `ecomplexity` (`infoComplexity_le_ecomplexity`), and `le_infoComplexity_iff` is the interface for lower bounds. The error requirement is worst-case on the input domain, not Braverman–Rao's distributional error under `μ`, and the infimum ranges over public-coin protocols without private coins. So, for `μ` supported on `A × B`, `infoComplexity` is an upper bound on their information complexity. Without that hypothesis it is not, because inputs outside `A × B` carry no correctness requirement. For example, for `A = B = ∅` it is `0`. Distributional information complexity, additivity, the direct-sum theorem and the BJKS disjointness bound are not formalized. The [checked examples](../../ComplexityTests/InformationComplexity.lean) show the gap can be strict. When Alice announces her bit on perfectly correlated inputs, the internal cost is `0` and the external cost is `1`, so computing her bit has information complexity `0`, although every deterministic protocol computing it sends at least one bit.

Unbounded-error communication is characterized by sign-rank. `SignRepresents A f` says that every entry of the real matrix `A` is nonzero with the sign of the `±1` sign matrix, `-1` where `f` is true. [`signRank f`](../../Complexity/Computability/Communication/SignRank.lean) is the least rank of such a matrix. It is at most the rank of any sign-representation (`signRank_le_rank`) and does not increase on submatrices (`signRank_comap_le`). In the [unbounded-error model](../../Complexity/Computability/Communication/UnboundedError.lean), a private-coin protocol solves `f` when its error is below `1 / 2` on every input (`PrivateCoin.SolvesUnbounded`), and `PrivateCoin.uppComplexityFun f` is the least depth of such a protocol. For a Boolean function on finite sets, [the Paturi–Simon theorem](../../Complexity/Computability/Communication/PaturiSimon.lean) `PrivateCoin.clog_signRank_le_uppComplexityFun_le` gives `⌈log₂ r⌉ ≤ UPP ≤ ⌊log₂ r⌋ + 2` with `r = signRank f`. The lower bound holds for protocols with any finite number of random bits. The upper bound (`PrivateCoin.exists_solvesUnbounded_depth_le`) builds a protocol in which Alice sends an index of `⌈log₂ (r + 1)⌉` bits and Bob answers with one biased bit. Equality has sign-rank at most three (`signRank_equality_le_three`), so it costs at most three bits with unbounded error (`PrivateCoin.uppComplexityFun_equality_le_three`), against `⌈log₂ |X|⌉ + 1` deterministically for `|X| ≥ 2`. The coins must be private: on finite inputs, public coins would give every function unbounded-error cost at most two. Lower bounds on sign-rank remain open work, including Forster's bound for Hadamard matrices and `signRank(EQ) = 3` on four or more inputs ([#3262](https://github.com/cslib-community/complexitylib/issues/3262)).

The deterministic lifting theorem composes a Boolean function with an index gadget. For the theorem's parameters m and tau, a protocol of cost c yields a decision tree of depth d with `(m/tau)^d <= 4^c`, assuming `4 <= tau`, `tau^2 <= m` and `320 n^2 (log2 m+1) <= tau`. Choosing tau around the square root of m gives a gadget on the order of `n^4 log^2 n`, rather than the smaller gadgets of more recent sharp lifting theorems. This is a documented quantitative scope choice. The source is [the lifting simulation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Communication/Lifting/Simulation.lean).

[CoverNumber](../../Complexity/Computability/Communication/Nondeterministic/CoverNumber.lean) counts rectangles instead of guessed bits. `coverNumber z R A B : ℕ∞` is the least size of a `z`-cover. On all of `X × Y` it is Kushilevitz and Nisan's `C^z(f)`, and for `z = true` the rectangle covering bound. `ecomplexity_le_iff_coverNumber_le` and `ecomplexity_eq_clog_coverNumber` show that `ecomplexity` is `⌈log₂ coverNumber⌉`. `card_le_coverNumberFun_of_isFoolingSet` is the fooling-set bound on the count itself. [ExtensionComplexity](../../Complexity/Computability/Communication/Nondeterministic/ExtensionComplexity.lean) proves Yannakakis's rectangle covering bound [yannakakis91][yannakakis91], [fmptw15][fmptw15] (Theorem 4). The support of a matrix `M` over an ordered semiring has a `1`-cover by `rank₊ M` rectangles (`coverNumberFun_ne_zero_le_nonnegRank`), so `N¹` of the support is at most `⌈log₂ rank₊ M⌉`. Through the factorization theorem in [extended formulations](../algorithms-and-memory/algorithm-endpoints.md#extended-formulations-and-yannakakiss-factorization-theorem), the same bounds hold for the slack matrix of a nontrivial polytope with `xc P` in place of `rank₊ M`. `card_le_extensionComplexity_of_isFoolingSet` turns a fooling set of the slack matrix's support into a lower bound on extension complexity. The rectangle covering bound can be far from the nonnegative rank, and these modules prove no exponential lower bound for an explicit polytope.

## Number-on-forehead multiparty communication

Import `Complexity.Computability.Communication.NOF.TwoParty`, which brings in the model, discrepancy and the two-player bridge, or one of the modules below it. For the cube bound and the generalized inner product, import `Complexity.Computability.Communication.NOF.GeneralizedInnerProduct` (below). [ComplexityTests/CommunicationNOF.lean](../../ComplexityTests/CommunicationNOF.lean) is a worked example: it has small protocols, cylinder intersections, and the inner-product bound through the two-player bridge. The model is due to Chandra, Furst and Lipton [ChandraFurstLipton1983]. In the number-on-forehead model, players indexed by a type `ι` share an input `x : ∀ i, X i`. Player `i` sees every part except its own, `NOF.view i x`. A [NOF.Protocol](../../Complexity/Computability/Communication/NOF/Protocol.lean) is a tree whose nodes are owned by players, and each written bit is a function of the owner's view. Cost is tree depth, as in the two-party model. Each player still computes for free, and every leaf announces the output to all players. [NOF.PublicCoin](../../Complexity/Computability/Communication/NOF/Randomized.lean) is a PMF over such trees, with the same error and worst-supported-depth conventions as the two-party `PublicCoin`.

A cylinder intersection is presented as the set `cylinderIntersection φ` of inputs on which every player's test `φ i (view i x)` succeeds. `isCylinderIntersection_iff` matches this with the textbook definition: an intersection of sets, each closed under changing one coordinate. [NOF discrepancy](../../Complexity/Computability/Communication/NOF/Discrepancy.lean) is the largest `ν`-signed imbalance of `f` on a cylinder intersection. The discrepancy bound `2 γ ≤ 2 ^ c disc_ν(f)` holds for deterministic protocols with distributional error `1/2 - γ` and for public-coin protocols with worst-case error `1/2 - γ`. With players `Fin 2`, cylinder intersections are rectangles. [The two-player bridge](../../Complexity/Computability/Communication/NOF/TwoParty.lean) proves that the NOF discrepancy then equals the two-party `discrepancy`, transported along `piFinTwoEquiv`. It also runs two-party protocols as NOF protocols of the same depth.

For lower bounds against explicit functions, import `Complexity.Computability.Communication.NOF.GeneralizedInnerProduct`. [ComplexityTests/CommunicationNOFGIP.lean](../../ComplexityTests/CommunicationNOFGIP.lean) has worked instances. Two inputs `a` and `b` span a cube whose `2 ^ k` corners `S.piecewise b a` take `b` on the players in `S` and `a` elsewhere. The cube expectation `cubeExpectation f` averages the product of the signs `(-1) ^ f` over the corners. [The cube bound](../../Complexity/Computability/Communication/NOF/Cube.lean) `discrepancy_uniformOfFintype_pow_le` states `disc(f) ^ (2 ^ k) ≤ E(f)` under the uniform distribution, for `k ≥ 1` players. It is proved by one Cauchy–Schwarz step per player. This is the BNS–Chung criterion of Babai, Nisan and Szegedy [BabaiNisanSzegedy1992] and Chung [Chung1990], in the proof of Raz [Raz2000]. [The generalized inner product](../../Complexity/Computability/Communication/NOF/GeneralizedInnerProduct.lean) `gip` of `k` strings of `n` bits is the parity of the number of positions where all of them are `1`. Its cube expectation equals its bias `(1 - 2 / 2 ^ k) ^ n`. Hence a public-coin protocol of cost `c` with error `1/3` satisfies `2 n < 4 ^ k (c + 2)`, and an exact deterministic protocol of cost `c` satisfies `2 n ≤ 4 ^ k c`. This is the Babai–Nisan–Szegedy `Ω(n / 4 ^ k)` bound, as presented in [Jukna2012], Section 5.6. The sharper `Ω(n / 2 ^ k)` form is not formalized.

For Ramsey-type lower bounds, import `Complexity.Computability.Communication.NOF.ExactlyN`. [ComplexityTests/CommunicationNOFExactlyN.lean](../../ComplexityTests/CommunicationNOFExactlyN.lean) has worked instances. [Leaves](../../Complexity/Computability/Communication/NOF/Transcript.lean) are numbered from left to right, `NOF.Protocol.leaf p x : Fin p.leafCount`. There are at most `2 ^ depth` of them, and the output is a function of the leaf. The star lemma `leaf_eq_of_view_eq` says: if each player `i` has a witness `y i` that it cannot tell apart from `q`, and all the witnesses reach the same leaf, then `q` reaches that leaf too. Equivalently, every leaf is a cylinder intersection (`isCylinderIntersection_leaf`). In [Exactly-N](../../Complexity/Computability/Communication/NOF/ExactlyN.lean), three players hold numbers in `Fin (N + 1)` and `exactlyN N` asks whether they sum to `N`. At each leaf of a protocol computing it, the points `(a, b)` whose yes-input `(a, b, N - a - b)` reaches the leaf form a corner-free set (`ExactlyN.isCornerFree_leaf`). With Mathlib's `corners_theorem_nat`, `ExactlyN.lt_ecomplexityFun` gives `c < D(exactlyN N)` whenever `cornersTheoremBound (2 ^ (-c) / 9) ≤ N / 2 + 1`. `ExactlyN.tendsto_ecomplexityFun` then says that the complexity tends to infinity. This is the Chandra–Furst–Lipton lower bound [ChandraFurstLipton1983], argued through corners as in [RaoYehudayoff2020], Chapter 4. The bound inherits the tower-type growth of Mathlib's `cornersTheoremBound`. Not formalized: the converse (protocols from corner-free colorings), quantitative corners bounds, and the `k`-player version.

## Distributed rounds in the LOCAL model

Import `Complexity.Computability.Distributed.OrientedCycle.RoundComplexity`,
`Complexity.Computability.Distributed.OrientedCycle.MIS` or
`Complexity.Computability.Distributed.OrientedCycle.LCL.Classification` (or one of the modules below
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
use `Nat.logStar_le_iff` rather than unfolding, and `decide` for small values. The companion
iterated floor logarithm `Nat.iterLog` and floor stopping count `Nat.floorLogStar`
(`Nat.floorLogStar_le_iff`) live in `Complexity.Foundations.Data.Nat.IterLog`. `Nat.twoTower` is a
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

[LCL/Basic.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Basic.lean),
[LCL/Flexible.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Flexible.lean),
[LCL/Linear.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Linear.lean) and
[LCL/Classification.lean](../../Complexity/Computability/Distributed/OrientedCycle/LCL/Classification.lean)
cover the classification of LCL problems without inputs on directed cycles by Chang,
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
unfolding `Algorithm.run`.
In `Linear.lean`, `Algorithm.SolvesLCL.le_of_forall_not_isFlexible` is the `Ω(n)` lower bound
(their Thm 6.5 via Lemma 6.3): if no state is flexible, every `t`-round algorithm has
`n ≤ (|L| + 1) (2t + 1)`. The proof takes two nodes with equal outputs and disjoint windows, then
moves one node so that one of the windows shifts by one. This gives closed walks of the consecutive
lengths `d` and `d + 1`, and `IsFlexible.of_consecutive` (Mathlib's `frobeniusNumber_pair`) then
makes that state flexible. The source instead moves nodes repeatedly; the single move is a
difference in proof route, not a new result. `IsSolution.exists_solvesLCL` is the matching upper
bound: on a cycle where `R` is solvable, `gatherRule` sees the whole cycle in `⌊n / 2⌋` rounds and
outputs a rotation of a fixed solution. It finds the node with identifier `0`, so it relies on the
`{0, …, n - 1}` identifier convention. Theorem 6.5 also assumes a repeatable state, which only
makes `R` solvable on infinitely many cycles; the Lean bounds are stated for each solvable `n`
instead. `LCL.trichotomy` in `Classification.lean` assembles the three rows for finite `L`: a loop
and `0` rounds, no loop but a flexible state and `Θ(log* n)`, or no flexible state and `Θ(n)`. The
bounds hold for each `n`, and the algorithms of the last two rows may depend on `n`. The last row
also contains the problems solvable on no cycle (no repeatable state), which the source lists
separately as unsolvable; for them its clauses are vacuous. The lower-bound clauses quantify over
state types of any universe, so destructuring `trichotomy` needs explicit universes, as in
`trichotomy.{0, 0, 0} R`.

[Checked examples](../../ComplexityTests/Computability/Distributed/OrientedCycle.lean) run the
algorithms on a 5-cycle and on the infinite path. They also show that the one-node cycle has no
proper colouring and no MIS, and that two rounds of 3-colouring fail on the cycle of length
`2 ↑↑ 6 + 1`. The 5-cycle examples include the greedy MIS steps and the full `misAlgorithm 2` run.
[LCL examples](../../ComplexityTests/Computability/Distributed/LCL.lean) check that 3-colouring
and MIS are flexible without a loop, and the anchors and filling on a 6-cycle. For 2-colouring,
which has no flexible state, they check that no `1`-round algorithm solves the 10-cycle, that
gathering solves it in `5` rounds, and that the trichotomy puts it in the `Θ(n)` row.

Only oriented cycles are covered in the LOCAL model. General graphs with port numbering, Linial's
`O(Δ²)` colouring, `(Δ + 1)`-colouring and MIS on bounded-degree graphs, the CONGEST message-size
bound, randomized LOCAL algorithms, and LCLs with inputs or on paths and undirected cycles remain
open; see `ROADMAP.md`. A centralized simulation of the phases of Luby's randomized MIS
algorithm on general finite graphs, without messages, is described in
[Luby's randomized maximal independent set](../algorithms-and-memory/algorithm-endpoints.md#lubys-randomized-maximal-independent-set).

## Byzantine agreement

Import `Complexity.Computability.Distributed.Byzantine.NodeBound` for the impossibility theorems,
or `Complexity.Computability.Distributed.Byzantine.OralMessages` for these together with the
single-fault protocol. Both build on
[Byzantine/Basic.lean](../../Complexity/Computability/Distributed/Byzantine/Basic.lean), the model
of deterministic synchronous message passing on the complete graph of a process type `P`. A
`Protocol P State Msg` gives every process an initial state from its input bit (`init`), a message
to every process (itself included) in each round (`send r i s j`), a state update from the messages
received (`update r i s m`, where `m j` came from `j`), and a Boolean decision (`output`). All four
take the process as an argument, so processes may run different code. Messages and local
computation are unbounded and the round number is common knowledge.

Faults are Byzantine and static. `Protocol.state π F adv x r i` is the state of `i` after `r` rounds
on inputs `x : P → Bool` when the processes in `F : Finset P` are faulty. In round `r + 1` a faulty
`j` sends `adv r j i` to `i`, arbitrarily and possibly differently to different recipients.
`Protocol.decision π F adv x R i` is the decision after `R` rounds. Runs are deterministic, so a
fixed table `adv` is as strong as an adaptive or rushing adversary: the messages such an adversary
sends on a given input form a table. `Protocol.adaptiveState_eq_state` checks this for a rushing
adversary `strat r σ j i` that sees the global state `σ` after `r` rounds, and
`SolvesByzantineAgreement.adaptive` transfers agreement and validity to such adversaries.
`SolvesByzantineAgreement t R` requires, for every `F` with at most `t` processes, every `adv` and
every `x`, *agreement* (all correct processes decide alike) and *validity* (if every correct
process has input `v`, every correct process decides `v`). Decisions are read after exactly `R`
rounds, which is how termination is expressed; a protocol that decides earlier keeps its state.
Protocols whose decision round depends on the run are not covered. For finite `P` and `Msg` this
loses nothing, since by König's lemma they decide within a bound uniform over all runs, but for
infinite `Msg` a fixed `R` is strictly narrower than eventual decision. To prove that a protocol
solves the problem, unfold `Protocol.decision` and `Protocol.state` round by round, as
`om1_heard` and `om1_report` in
[OralMessages.lean](../../Complexity/Computability/Distributed/Byzantine/OralMessages.lean) do.

Impossibility proofs use the covering lemma `Protocol.state_eq_coverState`. A covering network is
given by a node type `N`, a process `label a` whose code node `a` runs, an input `input a`, and the
node `nbr a j` that sends to `a` in the role of process `j`; `Protocol.coverState` is its run. If
the correct processes embed into the network by `e`, keeping their code, inputs and mutual wiring,
and every faulty process sends to a correct `i` what the network shows `e i`, then every correct
`i` is in the state of `e i` after every round. This lemma packages the Locality and Fault axioms of
Fischer, Lynch and Merritt (PODC 1985, §2) for this model. To use it, supply the network and check
the four hypotheses: `hlabel`, `hinput` and `hadv` are usually `rfl`, and `hnbr` is the
combinatorial content.

[Byzantine/NodeBound.lean](../../Complexity/Computability/Distributed/Byzantine/NodeBound.lean)
proves their Theorem 1 (§3.1): `Protocol.not_solvesByzantineAgreement` says that no protocol on
`n` processes with `2 ≤ n ≤ 3t` solves Byzantine agreement against `t` faults, for any fixed
decision round `R`. `Protocol.not_solvesByzantineAgreement_three` is the hexagon case `n = 3`,
`t = 1`. Both follow from `Protocol.not_solvesByzantineAgreement_of_partition`, which needs a
map `g : P → Fin 3` whose fibres have at most `t` elements, with `g a = 0` and `g c = 2` for some
`a`, `c`. The proof glues two copies of the network, with inputs `0` and `1`, crossing the edges
between the groups `0` and `2`. Unlike the paper, the middle group may be empty, so `n = 2` is
included. For `n ≤ 1` agreement is trivial: `Protocol.solvesByzantineAgreement_ownInput` (in
`Byzantine/Basic.lean`) decides the own input.

[Byzantine/OralMessages.lean](../../Complexity/Computability/Distributed/Byzantine/OralMessages.lean)
gives the matching upper bound for one fault. `om1` sends inputs in round 1 and relays them in
round 2. A process estimates the input of each `k` by the strict majority of the relays from the
processes `j ≠ k`, and decides the strict majority of these estimates, ties going to `false`.
`solvesByzantineAgreement_om1` proves that it tolerates one fault among `n ≥ 4` processes in any
`R ≥ 2` rounds. This is the single-fault procedure of Pease, Shostak and Lamport (JACM 1980, §2;
there for `n = 4`), generalized to `n ≥ 4` and followed by a majority vote, as in `OM(1)` of
Lamport, Shostak and Pease (TOPLAS 1982, Theorem 1).
`exists_solvesByzantineAgreement_one_iff` combines the bounds: for `R ≥ 2`, `n` processes can
tolerate one fault exactly when `n ≤ 1` or `n ≥ 4`. The statement quantifies over `S M : Type`.

[Checked examples](../../ComplexityTests/Computability/Distributed/Byzantine.lean) show a leader
protocol that solves the fault-free problem and fails against a faulty leader that tells different
processes different things. They also run `om1` on four processes against an equivocating process,
with mixed and with unanimous inputs, and against a rushing process, and instantiate the node bound
at `n = 2` and `n = 6`.

Only static faults on the complete graph with Boolean inputs are covered. The connectivity bound
`κ ≥ 2t + 1` (Fischer, Lynch and Merritt, §3.2), the general upper bound for `n > 3t` (`OM(t)` or
exponential information gathering), the `t + 1` round lower bound, authenticated agreement and
randomized agreement remain open; see `ROADMAP.md`. The asynchronous impossibility of Fischer,
Lynch and Paterson is upstream in CSLib (`Cslib/Computability/Distributed/FLP`), in a separate
asynchronous crash-fault model.

## Locally decodable codes

[LocallyDecodable/Basic](../../Complexity/Computability/LocallyDecodable/Basic.lean) is the local-decoding model. A code is `C : (ι → Bool) → P → Γ`. A decoder for the bit `i` is a `ProbOracleComp (fun _ : P => Γ) Bool`: it draws private uniform coins and queries positions of a received word `y : P → Γ`, possibly adaptively. `decodeLaw program y` is its output law with the queries answered by `y`. The query budget is the worst-case `ProbOracleComp.IsQueryBounded`, which counts queries on every path and not private samples. `IsLocalDecoder C q δ ε A` asks for at most `q` queries and success probability at least `1/2 + ε` from every word within Hamming distance `δ |P|` of a codeword. `IsSmoothDecoder C q c ε A` asks only for success on codewords, and for each position to be read at most `c / |P|` times in expectation. `expectedReads` is an `OracleComp.expectedCost` from [QueryCount/Expected](../../Complexity/Languages/Probabilistic/QueryCount/Expected.lean). This expected-reads notion bounds the probability of reading a position, so it implies the read-probability bound of Katz–Trevisan smoothness (Kerenidis–de Wolf, Definition 3 in arXiv:quant-ph/0208062v2). It does not imply the non-adaptivity that the source definitions require, because the decoders here may be adaptive. For `δ < 0` the local-decoding condition is vacuous, so the results assume `0 < δ` where it matters. `nonadaptive coins Q output` builds a non-adaptive decoder, and its reads do not depend on the received word (`hasObliviousReads_nonadaptive`).

The [Hadamard decoder](../../Complexity/Computability/LocallyDecodable/Hadamard.lean) reads `y r` and `y (eᵢ + r)` for a uniform `r`. It is a `(2, δ, 1/2 − 2δ)` local decoder for every `δ` and a `(2, 2, 1/2)` smooth decoder. [Smoothing](../../Complexity/Computability/LocallyDecodable/Smoothing.lean) proves Katz–Trevisan smoothing (Katz–Trevisan, Theorem 1, restated as Kerenidis–de Wolf, Theorem 9 for non-adaptive decoders): `isSmoothDecoder_mask_heavyPositions` turns a `(q, δ, ε)` local decoder with oblivious reads into a `(q, q/δ, ε)` smooth decoder. It does so by answering queries to the heavy positions from a fixed word. Every non-adaptive decoder and every one-query decoder has oblivious reads. Smoothing adaptive decoders that make several queries is not covered. [OneQuery](../../Complexity/Computability/LocallyDecodable/OneQuery.lean) proves an original explicit one-query bound by a degree-one Fourier argument. Katz and Trevisan proved that one-query locally decodable codes have bounded message length. The inequality here is a different one, polynomial in `|Γ| − 1`, and we did not find it in the literature. `IsSmoothDecoder.four_mul_card_mul_sq_le` proves `4 |ι| ε² ≤ c² (|Γ| − 1)` for `(1, c, ε)` smooth decoders with `0 ≤ ε`. `IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le` proves `4 δ² |ι| ε² ≤ |Γ| − 1` for `(1, δ, ε)` local decoders, whatever the length `|P|`. The proof uses `BitString.sq_sum_sum_abs_fourierCoeff_fiber_le` from [FiberWeight](../../Complexity/Foundations/BooleanAnalysis/FiberWeight.lean), a bound on the degree-one weight of the fibers of a map from the cube. The [checked examples](../../ComplexityTests/LocallyDecodable.lean) include the Hadamard and smoothed Hadamard decoders, and a repetition code. The repetition code is a `(1, 1/3, 1/6)` locally decodable code, its Katz–Trevisan smoothing is `(1, 3, 1/6)`, and it attains the one-query bound. They also show that no two-bit binary code is `(1, 1, 1/2)` smooth. The general Katz–Trevisan bound `n ≥ Ω(k^{q/(q−1)})` and the two-query exponential bounds remain open; see `ROADMAP.md`. A non-adaptive decoder whose reads are uniform and which decodes codewords exactly gives a private information retrieval scheme with one server per read (`PIR.hasScheme_ofDecoder`, [PIR/SmoothCode](../../Complexity/Crypto/Protocols/PIR/SmoothCode.lean)); see the private information retrieval section of the protocols chapter.

## Expander codes and flip decoding

The coding-theory API (minimum distance, the Hamming, Singleton and Johnson bounds, Reed–Solomon and list decoding, Justesen codes) lives in `Complexity/Foundations/Data/Code` and has no chapter of its own yet. Expander codes sit here next to locally decodable codes because their decoder is also local: each flip reads only the checks around one variable. [Expander/Bipartite](../../Complexity/Foundations/Combinatorics/Expander/Bipartite.lean) treats a bipartite graph as a decidable relation `G : ι → κ → Prop` between variables and checks. `neighbors G S` and `uniqueNeighbors G S` are the neighbours and unique neighbours of a set of variables. `IsVertexExpander G k α` asks every set of at most `k` variables to have at least `α |S|` neighbours; this is the `(n, m, c, γ, α)` expander of Guruswami–Rudra–Sudan (Definition 11.2.2 in the August 2025 draft) with `k = γ n`. Left degrees are only bounded by `c` (`IsLeftBounded`), not required to equal `c`. The unique-neighbour lemma `IsVertexExpander.le_card_uniqueNeighbors` gives `(2 α − c) |S| ≤ |U(S)|`. [Code/ExpanderCode](../../Complexity/Foundations/Data/Code/ExpanderCode.lean) defines the Sipser–Spielman code `ExpanderCode.code G`, the kernel of the incidence matrix over `Bool`, as a `Submodule Bool (ι → Bool)`. It proves the rate bounds `2 ^ (n − m) ≤ |C|` and `log₂ |C| / n ≥ 1 − c / d` for `(c, d)`-biregular graphs. For distance, if `c < 2 α` then codewords differ in more than `k` positions (`lt_hammingDist`, `lt_minDist`), and in fact `2 α k ≤ c · d` (`two_mul_mul_le_hammingDist`, GRS Theorem 11.3.8). [Code/FlipDecoding](../../Complexity/Foundations/Data/Code/FlipDecoding.lean) proves correctness of the flip decoder for `3 c < 4 α` (Guruswami–Sharma notes, Lemmas 5 and 6). Each flip lowers the number of violated checks, so a run of `t` flips from `x` has `t ≤ #unsat(x) ≤ c · d(x, w)`. `decode_eq` shows that the bounded decoder `decode pick n` returns `w` for any pivot rule satisfying `IsFlipRule` whenever `c · d(x, w) < (2 α − c) k` and `n ≥ #unsat(x)`. `decode_eq_of_two_mul_le` specializes this to error weight at most `k / 2`. Rounds are counted abstractly; no RAM implementation of the linear-time decoder is given. The [checked examples](../../ComplexityTests/Code/ExpanderCode.lean) use the Fano plane, a `(3, 3)`-biregular graph that expands pairs of points by `5/2`. On it, the distance bound `d ≥ 4` is tight and the decoder corrects every single error. The examples also show that expansion fails for a collinear triple and that two errors can be ambiguous. Lossless expanders themselves (probabilistic existence, Capalbo–Reingold–Vadhan–Wigderson), Spielman's linear-time encodable codes and Zémor's decoding of Tanner codes (whose distance on small-bias Cayley graphs is in [Expander/TannerCode](../../Complexity/Foundations/Combinatorics/Expander/TannerCode.lean)) remain open; see `ROADMAP.md`.

## Channel coding on the binary symmetric channel

[BinarySymmetricChannel](../../Complexity/Probability/BitString/BinarySymmetricChannel.lean) models the binary symmetric channel `BSC_p` (Guruswami–Rudra–Sudan, *Essential Coding Theory*, draft of 26 August 2025, §6.2). `bsc p x` is a `PMF` on received words `ι → Bool`: the translate by `x` of `bscNoise p`, a `Probability.PMF.pi` product of coins `flipBit p`. Its mass at `y` is `p ^ d (1 − p) ^ (n − d)` with `d` the Hamming distance (`bsc_apply_toReal`), and the noise has the law of a `bernoulliAverage` mask of rate `p` (`bscNoise_apply_toReal`). A code is an encoder `E : M → (ι → Bool)` with a decoder `D`. `decodingError p E D m` is the probability that `D` misdecodes the channel output on `E m`, and `IsNearestDecoder E D` is nearest codeword decoding. Nearest codeword decoders exist (`exists_isNearestDecoder`), and they are maximum-likelihood decoders for `p ≤ 1/2` (`bsc_apply_toReal_le_of_isNearestDecoder`). The number of flipped bits is binomial with a Hoeffding tail (`bscNoise_toOuterMeasure_lt_weight_toReal_le`).

[Achievability](../../Complexity/Probability/BitString/BinarySymmetricChannel/Achievability.lean) proves the positive half of Shannon's noisy-channel coding theorem for `BSC_p`: Shannon 1948, Theorem 11, specialized to `BSC_p`, in the form of Guruswami–Rudra–Sudan Theorem 6.3.1(1). The proof follows their §6.3.2. `expect_expect_decodingError_le` is the random-coding bound. Averaged over uniform codebooks and messages, the error of a nearest codeword decoder is at most `T + (|M| − 1) |B(n, r)| / 2^n`, where `T` is the probability that more than `r` bits flip. `exists_code_decodingError_le` expurgates half of a good codebook of size `2K`, as in their Claim 6.3.3. The result is `K` codewords of any length whose *maximal* error is at most `2 (T + (2K − 1) |B(n, r)| / 2^n)` under every nearest codeword decoder. With `r = ⌊ρ n⌋`, Hoeffding's inequality and the entropy volume bound give `exists_pos_forall_exists_code_decodingError_le_exp`. For `0 ≤ p < 1/2` and `R < 1 − h₂(p)`, where `h₂(p) = Real.binEntropy p / Real.log 2` is in bits, some `δ > 0` works for every `n`: there is a code with `2^⌈R n⌉₊` codewords whose maximal error is at most `10 exp (−δ n)`. `exists_pos_forall_exists_isNearestDecoder_decodingError_le_exp` restates this in the source's form, with an encoder and a nearest codeword decoder. `eventually_exists_code_decodingError_le` is the ε–eventually form.

[Converse](../../Complexity/Probability/BitString/BinarySymmetricChannel/Converse.lean) proves the weak converse for `BSC_p`, in the form of Cover–Thomas Theorem 7.9.1 specialized to `BSC_p` [Cover–Thomas][coverthomas06]. It uses Fano's inequality, which [Entropy/Fano](../../Complexity/Probability/Entropy/Fano.lean) proves for finite `PMF`s, in bits, with the library's convention that `conditionalEntropy` of a joint law of `(Y, X)` is `H(X | Y)`. `conditionalEntropy_le_binEntropy_add_mul_logb` states `H(X | Y) ≤ h₂(Pe) + Pe log₂ (|𝒳| − 1)` for every estimator `g` of `X` from `Y`, with `Pe` the probability that `g Y ≠ X`. `conditionalEntropy_map_le_binEntropy_add_mul_logb` restates it for random variables on a common outcome space, and `conditionalEntropy_le_one_add_mul_logb` is the weak form `1 + Pe log₂ |𝒳|`. The proof is a pointwise bound for each observation, combined by concavity of the binary entropy, rather than the textbook's chain rule for an error indicator. [Entropy/Pi](../../Complexity/Probability/Entropy/Pi.lean) adds `entropy_pi`: the entropy of a product of independent laws is the sum of their entropies. For the channel, a message `W` with law `ν` is encoded by `E` and sent through `BSC_p`; let `Y` be the received word. `mutualInfo_bind_bsc_le` shows `I(W; Y) ≤ n (1 − h₂(p))` for every input law, because `H(Y) ≤ n` and every output law `bsc p x` is a translate of the noise, of entropy `n h₂(p)` (`entropy_bsc`). Uniform inputs attain the bound (`mutualInfo_uniformOfFintype_bind_bsc`), so `1 − h₂(p)` is the capacity per use (Cover–Thomas §7.1). This additive-noise argument replaces the chain rule for `n` uses of a memoryless channel (their Lemma 7.9.2). With a uniform message and average error `Pe = 𝔼 m, decodingError p E D m`, `logb_card_le_add_fano` gives `log₂ |M| ≤ n (1 − h₂(p)) + h₂(Pe) + Pe log₂ (|M| − 1)`. `one_sub_expect_decodingError_mul_logb_card_le` is the weak converse `(1 − Pe) log₂ |M| ≤ n (1 − h₂(p)) + 1`, the source's `R ≤ Pe R + 1/n + C`. At a rate `R > 1 − h₂(p)`, `le_expect_decodingError_of_lt_rate` and `eventually_le_expect_decodingError` bound the average error below by `(R − (1 − h₂(p))) / (2 R)` once `n ≥ 2 / (R − (1 − h₂(p)))`, for every decoder and every `p ∈ [0, 1]`. The maximal error is at least the average. Together with achievability, `1 − h₂(p)` is the capacity of `BSC_p` for `p < 1/2`.

The volume bound is [Nat/Choose/Entropy](../../Complexity/Foundations/Data/Nat/Choose/Entropy.lean): `∑_{j ≤ r} C(n, j) (q − 1)^j ≤ exp (n H_q(α))` for `q ≥ 2`, `r ≤ α n` and `α ≤ 1 − 1/q`, with `Real.qaryEntropy` (GRS Proposition 3.3.3). [Code/BallVolume](../../Complexity/Foundations/Data/Code/BallVolume.lean) restates it for Hamming balls. Achievability is formalized only for nearest codeword decoders, and the codes are not explicit. The converse is the weak one, for deterministic decoders and average error. The strong converse (the error tends to `1` above capacity, GRS Theorem 6.3.1(2)), general discrete memoryless channels, channels with feedback and efficient capacity-achieving codes remain open; see `ROADMAP.md`. The [checked examples](../../ComplexityTests/BinarySymmetricChannel.lean) cover:

- a channel mass;
- the noiseless channel `BSC_0`, on which nearest decoding of an injective code is exact;
- the length-three repetition code, whose nearest decoders all have error exactly `3p²(1 − p) + p³`, while a constant decoder is not nearest;
- an explicit two-word code of length seven with maximal error below `1/2` on `BSC_{1/100}`;
- small entropy-bound instances;
- nonvacuity of the asymptotic theorem.

The [converse examples](../../ComplexityTests/BinarySymmetricChannelConverse.lean) cover:

- Fano's inequality, tight for the uniform law on three symbols, and forcing `H(X | Y) = 0` when the estimate is always right;
- the noise entropy of `BSC_{1/2}` and the mutual information of uniform inputs across `BSC_{1/2}` (zero) and `BSC_0` (`n` bits);
- small codes: four messages over one use of `BSC_0` always err, and over three uses of `BSC_{1/2}` they err with average probability at least `1/2`;
- nonvacuity of the asymptotic converse, including a maximal-error form.

Run `scripts/build.sh --wfail --iofail ComplexityTests.BinarySymmetricChannel ComplexityTests.BinarySymmetricChannelConverse`.

## Known Limitations

The surveyed lower bounds concern total Boolean functions or explicitly stated relation/promise domains. When applying a bound, identify whether it assumes both-party output, finite distributions, a bounded-round alphabet, or a gadget-size regime. No query/communication bound here supplies a native runtime without a separate compilation/resource theorem.

[complexitylib]: ../sources.md#complexitylib
[coverthomas06]: ../sources.md#coverthomas06
[fmptw15]: ../sources.md#fmptw15
[yannakakis91]: ../sources.md#yannakakis91
