# Representative algorithm endpoints and their models

These results are clients of the RAM and specification models, not additional execution models. The selected formal abstracts are useful when applying these results because they restate the actual model, encoding, quantifiers and bounds with checked bridges. This survey inspected their source statements; it did not rerun their audits or render their PDFs [complexitylib][complexitylib].

## Sorting and selection

[abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean) gives one fixed 16-register program for in-place randomized quicksort and one for quickselect, in the exact Word-RAM basis with unit-cost finite-interval `rand`.

| Algorithm | Fitting-width condition | Worst-case executed steps | Expected steps | Other guarantee |
|---|---|---|---|---|
| Quicksort | `w ≥ 3*(floorlog₂(n)+1)` and input fit | `20*n² + 8*n + 32` | `≤ 120*n*(floorlog₂(n)+1)+32` | At most `n-1` draws, sorted permutation, linear scratch frame |
| Quickselect, `k<n` | `w ≥ 2*(floorlog₂(n)+1)` and input fit | `10*n²+15` | `≤80*n+15` | At most `n-1` draws, kth sorted value and partition, no auxiliary memory |

Quickselect receives the index followed by the array; an invalid index has an explicit eight-step, no-write, no-randomness behavior returning zero. The expected costs are machine instruction counts. They do not price the `rand` instruction as an exact strict-PPT finite-coin sampler.

## Shortest paths and priority queues

[abstracts/ComplexityAbstracts/DijkstraAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/DijkstraAbstract.lean) represents directed weighted multigraphs by adjacency lists with natural weights; parallel edges and self-loops are allowed. Output distance is an extended natural, encoded as zero for infinity and `d+1` for a finite distance. The word condition is `8*(n+m+2)*(W+2) < 2^w`.

`dijkstra_logLinear` has `O((m+1)*(floorlog₂(n)+1))` instructions; `dijkstra_fibonacci` has `O(m+n*(floorlog₂(n)+1))`. The graph is already installed in the machine's initial memory. The first bound can omit a standalone scan over isolated vertices because untouched zero memory represents infinity. Treating graph construction or a mandatory full output traversal as charged work would be a different end-to-end contract.

[abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean) specifies bounded-capacity handles, bounded key/value ranges, fresh-handle insertion and arbitrary minimum ties. Initializer/operation code is chosen before capacity/key/value/base/width parameters. The amortized total is constant per ordinary operation plus a sum of logarithms of current size for extract-min. Fresh zeroed memory permits constant-time initialization; the reusable-memory version explicitly clears the region and costs linear time. The abstract's fixed operation list is demonic over all allowed results; the shared data-structure layer separately supports fully adaptive clients.

## Hash families and dictionaries

[abstracts/ComplexityAbstracts/HashTablesAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/HashTablesAbstract.lean) selects four expected-amortized dictionary implementations: multiply-shift chained hashing, five-wise linear probing, odd-stride uniform probing and cuckoo hashing. Each supports `get` and `insert` with overwrite, up to bounded distinct-key capacity. **Deletion is not included.** The operation list is fixed before initialization randomness; these are oblivious-sequence guarantees.

The initializer and operation programs are independent of runtime word width and base address, but their dependence on capacity/universe differs by theorem. The abstract does not bound static program-list length. Executed steps exclude caller argument preparation/dispatch. Universe restrictions include the chosen exponent-four polynomial regime; load-factor assumptions and exact initialization costs are visible. These distinctions prohibit a blanket claim of fully dynamic adaptive constant-time dictionaries.

[abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean) gives high-independence hashing with an explicit regime switch at capacity `2^320000`. Below it, finite-field polynomial hashing supplies exact k-wise independence; above it, fixed-parameter double tabulation has a high-probability transcript coupling, with an explicit condition under which the error bound becomes nontrivial. Queries per resampling epoch are restricted to at most `k` distinct keys. Programs may depend on `(k, capacity, universe, outputWidth)`; static code size is not bounded.

Across capacities the stated space is at most `(k+9232)*(capacity+1)` words, evaluation at most `111230*k+6862` instructions, and resampling at most `(5*k+46096)*(capacity+1)`. These constants are theorem bounds, not measured runtime or a practical implementation recommendation. The large-regime construction adapts Thorup's double-tabulation work; its fixed-k error statement is explicitly different from the source's original growing-independence asymptotic formulation [thorup13][thorup13].

## Global minimum cut

[abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean) treats weighted undirected multigraphs, `n≥2`, fitted total doubled edge weight and word widths sufficient for workspace/trial counters. A single contraction trial is one fixed 16-register program: `42*n²+12*n+21` worst-case instructions and at most `n-2` random calls, always returning a genuine nontrivial cut value. When minimum cut is positive, it succeeds with probability at least `2/(n*(n-1))`.

The Karger–Stein endpoint uses one fixed 24-register program, `O(n² log n)` worst-case steps and `O(n²)` matrix scratch per tree, with success at least `1/(floorlog₂(n)+15)`. Repetition gives minimum-cut **value** with failure at most `1/(2n)` in `O(n² log³ n)`. It does not enumerate all minimum cuts or attain the source's sparse-space formulation. The threshold is an integer inequality rather than a literal square-root expression; the abstract labels the implementation and proof adaptations.

## Other clients and classification

The source tree also contains native integer arithmetic, multiword circuit evaluation, matrix multiplication, primality/counting, predecessor structures, 3SUM/exact-triangle routines and randomized SAT algorithms. These broaden coverage of the machine library; they should be catalogued through the complete module census without counting each as a new model. In particular, a bounded frontend or a conditional transfer theorem should not be presented as completion of an unresolved fine-grained endpoint. The current `ROADMAP.md` and selected abstracts are better evidence of endpoint disposition than a directory name.

## Tree Evaluation

The [Cook–Mertz endpoint](catalytic-and-tree-evaluation.md) computes the root of an explicitly table-encoded perfect binary tree in native independent workspace `O(log n · log log n)` for positive value length and height. The output is not charged to workspace, and the theorem leaves time existential. The same page distinguishes borrowed-register restoration and fan-in/packed procedure variants.

## Known Limitations

The numeric values above are transcriptions of checked source statements, not results of new execution benchmarks. The source-reference audit checks locations and digests; it does not rerun Lean or prove asymptotic summaries. The full Haskell/Lean runtime behavior, allocator, operating system and hardware are outside these idealized RAM models.

[complexitylib]: ../sources.md#complexitylib
[thorup13]: ../sources.md#thorup13
