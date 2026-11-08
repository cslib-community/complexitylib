# Online and streaming models

## Deterministic online strategies

[Complexity/DataStructure/Online/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Online/Basic.lean) gives a `Problem` with state, requests, admissible initial states/transitions and a common step cost. `DetStrategy` has hidden memory and responds to the current request; it cannot inspect future requests through its interface. Competitive predicates compare its accumulated cost against every admissible offline schedule, either from the same initial state or arbitrary valid initial states. The basic coefficients are natural multiplicative/additive bounds; paging also has explicit rational-ratio impossibility theorems [complexitylib][complexitylib].

`adaptiveRequests` constructs a request list by observing the deterministic strategy. Replaying that list produces the same deterministic behavior. This is suitable for deterministic lower bounds; it is not a randomized online-adversary interface identifying adaptive and oblivious adversaries in expectation.

## Demand paging

[Complexity/DataStructure/Paging/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Paging/Basic.lean) instantiates an online problem with a cache of capacity `k`, a page request, and unit charge for a fault. [Complexity/DataStructure/Paging/LRU.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Paging/LRU.lean) implements LRU with a duplicate-free recency list and proves a potential inequality. `lruStrategy_isCompetitive` gives factor `k` with no additive charge from a common initial cache. `lruStrategy_isCompetitiveAnyInit` gives additive `k` for arbitrary valid initial caches.

[Complexity/DataStructure/Paging/LowerBound.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Paging/LowerBound.lean) constructs an adaptive missing-page sequence on `k+1` pages. The online strategy faults each time; a computable offline lookahead schedule separates its faults by `k` requests after warmup. `exists_ratio_violation_of_lt` rules out every rational ratio below `k`, regardless of additive constant, even from the empty cache. These specialize the equal-capacity part of Sleator–Tarjan's paging theorems. The source's unequal-capacity resource-augmentation factor is not yet the local endpoint [sleatortarjan85][sleatortarjan85].

The metric is number of page faults. The recency-list Lean implementation is not claimed to take constant RAM time per request. This is competitive resource analysis over a state-transition model.

## Count-Min: a stored streaming sketch

[Complexity/DataStructure/CountMin/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/CountMin/Basic.lean) models a weighted insertion stream `List (X × Nat)`. Each update increments one bucket in each row of a vector-of-vectors counter table; a query takes the minimum row counter. The exact bucket invariant proves no underestimation, each counter's bound by total mass, and entrywise merge agreement with stream concatenation.

[Complexity/DataStructure/CountMin/Probability.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/CountMin/Probability.lean) analyzes independently sampled two-universal rows for a stream and query fixed before the hash seeds. `dens_estimate_error_le_inv_two_pow` gives failure at most `2^-d` when `2 ≤ width*ε`. This is the one-sided additive-error form of the fixed-query Count-Min guarantee; it makes no adaptive-query or adaptive-update claim [cormode05][cormode05].

[Complexity/DataStructure/CountMin/Program.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/CountMin/Program.lean) supplies `sampleSketch` and `sampleQuery` as `ProbComp` algorithms, retaining seeds with the materialized table. `eval_sampleSketch` and `eval_sampleQuery` identify their laws with the deterministic uniform-seed analysis; `sampleQuery_error_le_inv_two_pow` transfers the accuracy bound. The supplied sampler/hash operation and the Lean array work do not receive machine-time or heap-consumption bounds here.

This is a stream algorithm model and an exact probability theorem, distinct from a general complexity class of one-pass bounded-space machines. It also does not imply differential privacy.

## One-pass streaming algorithms and the AMS sketch

[Complexity/Computability/Streaming/Basic.lean](../../Complexity/Computability/Streaming/Basic.lean) defines a deterministic one-pass `Streaming.Algorithm σ α β`: an initial memory state, an update reading one item and an output. Updates are arbitrary functions, so the model is non-uniform and charges only the memory surviving between items. `A.SpaceLE m b` says that the states reached on streams of at most `m` items have an injective `b`-bit encoding, so space is `⌈log₂⌉` of the number of reachable states. A `Streaming.Randomized` algorithm is a `PMF` over deterministic algorithms, with randomness drawn before the stream as for public-coin protocols. Its memory bound is checked separately for each algorithm in the support. A drawn algorithm's update may depend on the random choices, so random bits are free; this is the convention under which communication lower bounds transfer. An algorithm that tosses fresh coins at every item fits the model, for example after adding a step counter, which costs `⌈log₂(m+1)⌉` bits, so `Ω(n)` lower bounds still apply to it. `Solves ε R m` bounds the error on every stream of at most `m` items. `Algorithm.reduce` prefixes items, translates items and post-processes answers while keeping memory bounds.

[Complexity/Computability/Streaming/Communication.lean](../../Complexity/Computability/Streaming/Communication.lean) turns an algorithm with `b` bits into a one-way protocol in which Alice sends the encoded state after her part of the stream. `Algorithm.ecomplexityFun_le_of_spaceLE` and `Randomized.ecomplexityFun_le_of_spaceLE` bound deterministic and public-coin communication by `b + 1`. [Complexity/Computability/Streaming/Distinctness.lean](../../Complexity/Computability/Streaming/Distinctness.lean) applies this to the disjointness lower bounds:

- `le_of_solves_nodup` covers distinctness of at most `2n` items of `Fin n` with error `ε ≤ 1/2`. It gives `n ≤ 2^10 r (b+1) + 2^12` whenever `(4ε(1-ε))^r ≤ 1/64`; at error `1/3`, `n ≤ 36864 (b+1) + 2^12`.
- `le_of_solves_maxFreq` is the `F∞` lower bound of Alon–Matias–Szegedy, Proposition 3.1 [alonmatiasszegedy99][alonmatiasszegedy99], for estimates within less than `F∞/3`. A fixed item is prefixed to make the stream nonempty, so the statement uses `Fin (n+1)` and `2n+1` items.
- `Algorithm.le_of_run_eq_decide_nodup` and `Algorithm.le_of_run_eq_maxFreq` show that exact deterministic algorithms need `n ≤ b`.

The [test file](../../ComplexityTests/StreamingAMS.lean) shows that an algorithm storing the items seen and a flag uses `n + 1` bits.

There are two ways to prove a new streaming lower bound. The first starts from a communication lower bound, as `le_of_solves_nodup` does: split the stream into Alice's part `u x` and Bob's part `v y`, then apply `Randomized.ecomplexityFun_le_of_spaceLE`. The second reduces to an existing streaming lower bound, as `le_of_solves_maxFreq` does: use `Algorithm.reduce` with `Randomized.SpaceLE.map_reduce` and `Randomized.errorProb_map_reduce_le` to prefix fixed items, translate items and post-process answers.

[Complexity/Computability/Streaming/AMS.lean](../../Complexity/Computability/Streaming/AMS.lean) implements the AMS `F₂` sketch from Theorem 2.2. It keeps `2r` groups of `k` tug-of-war counters, each adding `sgn (h θ a) = ±1` per item, and answers the median over groups of the mean squared counter. The moment computations `𝔼 Z² = F₂` and `𝔼 (Z² - F₂)² ≤ 2F₂²` for four-wise independent signs are in [KWiseIndependent/TugOfWar.lean](../../Complexity/Probability/KWiseIndependent/TugOfWar.lean); the first is an instance of additivity of second moments under pairwise independence, in [KWiseIndependent/SecondMoment.lean](../../Complexity/Probability/KWiseIndependent/SecondMoment.lean). The median-of-means amplification is in [MedianOfMeans.lean](../../Complexity/Probability/MedianOfMeans.lean), built on the lower median of [Finset/Median.lean](../../Complexity/Foundations/Data/Finset/Median.lean). The frequency moments `freqMoment` and the largest frequency `maxFreq` are in [Streaming/Frequency.lean](../../Complexity/Computability/Streaming/Frequency.lean). `dens_amsSketch_error_le` and `solves_ams` give error `(8/9)^r` for relative accuracy `η` when `6 ≤ kη²`. Under the public-coin convention the seeds are not charged, and `spaceLE_ams` shows that every sketch drawn uses `b` bits once `(2m+1)^(2rk) ≤ 2^b`. Only the initial memory depends on the seeds (`init_amsSketch`, `update_amsSketch`, `output_amsSketch`). So `exists_injOn_iUnion_reachable_amsSketch` gives one `b`-bit encoding for the states reachable from all seeds, with the seeds stored, once `(|ι|(2m+1))^(2rk) ≤ 2^b`. This seed-inclusive count matches the `O(η⁻² log δ⁻¹ (log n + log m))` bound of Theorem 2.2. The test file instantiates the hypotheses with the four-wise independent trinomial hash family. It also shows that with a constant sign the sketch reports `F₁²` instead of `F₂`.

## Heavy hitters: Misra–Gries and the Count-Sketch

[Complexity/Computability/Streaming/MisraGries.lean](../../Complexity/Computability/Streaming/MisraGries.lean) implements the deterministic Misra–Gries summary `misraGries k` [misragries82][misragries82]. It stores its at most `k` counters as a multiset whose multiplicities are the counters. Reading an item increments its counter if it has one or if fewer than `k` counters are in use, and otherwise decrements every counter. Each decrement discards `k + 1` distinct stream items, which gives the following statements:

- `MisraGries.run_le_count` and `MisraGries.mul_count_sub_run_add_card_le` give `f̂_a ≤ f_a` and `(k + 1)(f_a − f̂_a) + m̂ ≤ m`, where `m̂` is the sum of the counters. This is Theorem 1.3.1 with the sharpening of Exercise 1-1 of [chakrabarti25][chakrabarti25].
- `MisraGries.count_sub_div_le_run` is the real form `f_a − m/(k+1) ≤ f̂_a`.
- `MisraGries.mem_state_of_length_lt_mul_count` says every item with `f_a > m/(k+1)` keeps a counter. This is the deterministic heavy-hitters guarantee.
- `MisraGries.toFinset_state_one_eq` is the one-counter majority case.
- `MisraGries.spaceLE_misraGries` bounds the memory: `(n(m+1)+1)^k ≤ 2^b` reachable states suffice on streams of at most `m` items over a universe of `n` items.

Chakrabarti's parameter `k` allows `k − 1` counters, so `misraGries k` is his algorithm with parameter `k + 1`.

[Complexity/Probability/KWiseIndependent/CountSketch.lean](../../Complexity/Probability/KWiseIndependent/CountSketch.lean) analyzes one row of the Count-Sketch [charikar04][charikar04] for arbitrary real weights. The bucket family `h` must be two-universal, and the sign family `ε ∘ g` must be independent of it, pairwise independent and of mean zero. Under these hypotheses:

- the estimate is unbiased (`CountSketch.expect_sum_ite_mul_sign_mul_sign`);
- the collision noise has second moment at most `∑_{b≠a} f_b²/w` (`CountSketch.expect_sq_sum_ite_mul_sign_le`);
- by Chebyshev, a row misses by more than `t` with probability at most `1/3` once `3∑_{b≠a} f_b² ≤ wt²` (`CountSketch.dens_abs_sum_ite_mul_sign_gt_le`).

These are equations (5.1)–(5.6) of [chakrabarti25][chakrabarti25]. Only an upper bound on collision probabilities is assumed.

The amplification step is the median trick `dens_abs_median_sub_gt_le`, added to [MedianOfMeans.lean](../../Complexity/Probability/MedianOfMeans.lean): if a single estimate misses with probability at most `1/3`, the median of `2r` independent estimates misses with probability at most `(8/9)^r`. `dens_abs_medianOfMeans_sub_gt_le` is now derived from it.

[Complexity/Computability/Streaming/CountSketch.lean](../../Complexity/Computability/Streaming/CountSketch.lean) assembles `2r` rows into the streaming algorithm `countSketch`, and `countSketchRandom` draws its seeds uniformly. Its results:

- `dens_countSketch_error_gt_le` and `solves_countSketchRandom` answer every fixed point query `a` within `ε‖f_{−a}‖₂` with error `δ`, once `3 ≤ wε²` and `(8/9)^r ≤ δ`.
- `solves_countSketchRandom_freqMoment` gives the same with the bound `ε√F₂`.
- `spaceLE_countSketchRandom` charges `(2m+1)^(2rw) ≤ 2^b` under the public-coin convention.
- `exists_injOn_iUnion_reachable_countSketch` gives the bound with the seeds stored, `(|ι||κ|)^(2r)(2m+1)^(2rw) ≤ 2^b`.

The [test file](../../ComplexityTests/StreamingHeavyHitters.lean) checks concrete Misra–Gries runs, including one where the error `m/(k+1)` is attained. It also instantiates the Count-Sketch hypotheses with the trinomial hash families, and shows that one bucket with a constant sign reports the stream length instead of the frequency.

## Native streaming folds

[Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean) gives actual machine-backed scans of raw bit strings through Christian Reitwiessner's streaming backend. A round holds an encoded accumulator and one input bit instead of copying the remaining input list. Time sums the round computation, old/new state encoding sizes and control; workspace takes a peak bound and charges retained accumulators. Read-only input and write-only output are excluded from work-tape space.

`foldl_bits_stream_sum` and `_spec` give cumulative costs and invariants. `foldl_bits_pair_stream_sum` includes a runtime initial accumulator. `iterate_unary_stream_sum` gives repeated state updates emitting output without workspace proportional to the iteration count. `foldl_bits_finite` specializes to linear time and constant workspace for a fixed finite state, and `map_bits` gives linear time with zero work space. The encoding and combinator source markers record the upstream/vendored backend origin.

These are compositional native resource theorems on the [machine model](../machines-and-classes/index.md), not a separate RAM primitive. Their current declarations still expose tidy backend predicates in this source module; broader plain-computability migration policy does not change what this pinned file actually states.

## Optimal stopping

[OptimalStopping/Basic](../../Complexity/Probability/OptimalStopping/Basic.lean) models stopping on independent observations with discrete laws. `jointLaw` is the product `PMF` of a list of laws. A deterministic stopping rule sees the history so far, most recent observation first, and decides whether to stop. `payoff` evaluates a rule, paying `0` if it never stops. `tsum_payoff_le_valueFrom` is the backward-induction bound: no rule beats the dynamic-programming value `valueFrom`. `tsum_payoff_optimalRule` shows that `optimalRule` attains it; that rule stops exactly when stopping is at least as good as continuing. `valueFrom_eq_iSup` combines the two: the value is the optimum over all rules. Randomized rules are mixtures of deterministic ones and are not modelled separately.

[OptimalStopping/Secretary](../../Complexity/Probability/OptimalStopping/Secretary.lean) treats the classical secretary problem. `n` candidates arrive in the order of a uniform `Equiv.Perm (Fin n)`, and a `Rule` sees only relative ranks. `uniform_map_relRanks` shows that the relative ranks are independent and uniform, which reduces the problem to the stopping model. `successProb_cutoffRule` proves that rejecting `r - 1 ≥ 1` candidates and then hiring the first best-so-far wins with probability `(r-1)/n · ∑_{i=r}^{n} 1/(i-1)`. `successProb_le_successProb_optimalCutoff` proves the Lindley–Dynkin optimality theorem: no rank-based rule beats the cutoff `optimalCutoff n`, the least `r ≥ 1` with `∑_{i=r}^{n-1} 1/i ≤ 1`. The quantitative forms are `successProb_le_exp_neg_one_add` (every rule is at most `1/e + 1/n`), `exp_neg_one_sub_le_successProb_floor` (cutoff `⌊n/e⌋ + 1` achieves at least `1/e - 1/n`) and `tendsto_successProb_optimalCutoff` (limit `1/e`). The full-information variant, where values are observed, is not covered.

[OptimalStopping/Prophet](../../Complexity/Probability/OptimalStopping/Prophet.lean) proves the prophet inequality of Krengel–Sucheston for independent `ℝ≥0`-valued `PMF` laws. `expectedMax_le_two_mul_expectedReward` is a single threshold statement. Let a rule accept every value above `t` and only values of at least `t`. Let `R` be its probability of accepting nothing. If `t` and `R` lie on opposite sides of `E[max]/2` and `1/2`, that is, `2t ≤ E[max]` and `1 ≤ 2R`, or `E[max] ≤ 2t` and `2R ≤ 1`, the rule earns at least `E[max]/2`. This needs no integrability hypothesis. The corollaries are Kleinberg–Weinberg's threshold `t = E[max]/2` (`expectedMax_le_two_mul_expectedReward_half`, assuming `E[max] < ∞`) and Samuel-Cahn's median threshold (`expectedMax_le_two_mul_expectedReward_median`). For a median `m`, accepting values `≥ m` works when `m ≥ E[max]/2`, and accepting values `> m` works when `m ≤ E[max]/2`. The median of the maximum is a hypothesis; its existence is not proved. Unlike Samuel-Cahn's rules, which take the last value when nothing was accepted, these rules receive `0`, so the bounds imply hers. `exists_tightLaws_lt` shows that `½` is optimal for all stopping rules, using the two values `1` and `k+1` with probability `1/(k+1)`.

[Checked instances](../../ComplexityTests/OptimalStopping.lean) evaluate the three-candidate case (success `1/2`, optimal cutoff `2`), confirm that the never-stop rule has probability `0`, compute the tight prophet instance's backward-induction value `1` through `valueFrom_eq_iSup`, and exercise the median and tightness statements.

## Known Limitations

The four meanings of “streaming” here should not be conflated: an input-list fold, an accurate stored probabilistic sketch, the abstract one-pass memory model with communication lower bounds, and a native machine scan with measured workspace. The abstract model counts reachable memory states and imposes no uniformity or time bound on updates. Its randomized lower bounds are for error at most `1/2` with public randomness that is not charged to the memory, and the AMS sketch has no `ProbComp` sampler or machine realization. Multi-pass algorithms, turnstile updates as stream items, `F_k` for `k > 2` and the deterministic-approximation and randomized-exact `F_k` lower bounds (Alon–Matias–Szegedy, Propositions 3.7–3.8) are not formalized. The Count-Sketch guarantees are for a query fixed before the seeds, not for adaptively chosen queries. Neither heavy-hitter algorithm has a `ProbComp` sampler or machine realization. Recovery of all heavy hitters over the universe, merging of Misra–Gries summaries and heavy-hitter space lower bounds are not formalized. No automatic native realization of the Count-Min sketch was identified in its four source modules. The online interface surveyed is deterministic; randomized competitive analysis would need additional adversary/expectation definitions. The optimal-stopping modules are semantic probability statements over deterministic rules: they do not charge the rules' computation and are not phrased through the online `Problem` interface.

[alonmatiasszegedy99]: ../sources.md#alonmatiasszegedy99
[chakrabarti25]: ../sources.md#chakrabarti25
[charikar04]: ../sources.md#charikar04
[complexitylib]: ../sources.md#complexitylib
[cormode05]: ../sources.md#cormode05
[misragries82]: ../sources.md#misragries82
[sleatortarjan85]: ../sources.md#sleatortarjan85
