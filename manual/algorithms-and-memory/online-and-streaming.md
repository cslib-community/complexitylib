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

## Native streaming folds

[Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Streaming.lean) gives actual machine-backed scans of raw bit strings through Christian Reitwiessner's streaming backend. A round holds an encoded accumulator and one input bit instead of copying the remaining input list. Time sums the round computation, old/new state encoding sizes and control; workspace takes a peak bound and charges retained accumulators. Read-only input and write-only output are excluded from work-tape space.

`foldl_bits_stream_sum` and `_spec` give cumulative costs and invariants. `foldl_bits_pair_stream_sum` includes a runtime initial accumulator. `iterate_unary_stream_sum` gives repeated state updates emitting output without workspace proportional to the iteration count. `foldl_bits_finite` specializes to linear time and constant workspace for a fixed finite state, and `map_bits` gives linear time with zero work space. The encoding and combinator source markers record the upstream/vendored backend origin.

These are compositional native resource theorems on the [machine model](../machines-and-classes/index.md), not a separate RAM primitive. Their current declarations still expose tidy backend predicates in this source module; broader plain-computability migration policy does not change what this pinned file actually states.

## Known Limitations

The three meanings of “streaming” here should not be conflated: an input-list fold, an accurate stored probabilistic sketch, and a native machine scan with measured workspace. No automatic native realization of the Count-Min sketch was identified in its four source modules. The online interface surveyed is deterministic; randomized competitive analysis would need additional adversary/expectation definitions.

[complexitylib]: ../sources.md#complexitylib
[cormode05]: ../sources.md#cormode05
[sleatortarjan85]: ../sources.md#sleatortarjan85
