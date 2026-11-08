# Representative algorithm endpoints and their models

These results are clients of the RAM and specification models, not additional execution models. The selected formal abstracts are useful when applying these results because they restate the actual model, encoding, quantifiers and bounds with checked bridges. This survey inspected their source statements; it did not rerun their audits or render their PDFs [complexitylib][complexitylib].

## Sorting and selection

[abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean) gives one fixed 16-register program for in-place randomized quicksort and one for quickselect, in the exact Word-RAM basis with unit-cost finite-interval `rand`.

| Algorithm | Fitting-width condition | Worst-case executed steps | Expected steps | Other guarantee |
|---|---|---|---|---|
| Quicksort | `w ≥ 3*(floorlog₂(n)+1)` and input fit | `20*n² + 8*n + 32` | `≤ 120*n*(floorlog₂(n)+1)+32` | At most `n-1` draws, sorted permutation, linear scratch frame |
| Quickselect, `k<n` | `w ≥ 2*(floorlog₂(n)+1)` and input fit | `10*n²+15` | `≤80*n+15` | At most `n-1` draws, kth sorted value and partition, no auxiliary memory |

Quickselect receives the index followed by the array; an invalid index has an explicit eight-step, no-write, no-randomness behavior returning zero. The expected costs are machine instruction counts. They do not price the `rand` instruction as an exact strict-PPT finite-coin sampler.

### Deterministic selection in the comparison model

Import `Complexity.Algorithms.Lean.Query.Select.Correctness` and `Complexity.Algorithms.Lean.Query.Select.Cost`. [Defs.lean](../../Complexity/Algorithms/Lean/Query/Select/Defs.lean) defines `Cslib.Query.select k xs`, the groups-of-five median-of-medians algorithm in cslib's comparison-query model `FreeM (LEQuery α)`, the model of `Cslib.Query.mergeSort`. Every comparison `a ≤ b` is an oracle query and list manipulation is free. The program sorts lists of at most `selectCutoff = 730` elements with `mergeSort`. For a longer list it takes the lower median of each group of five, selects the median of these medians recursively as the pivot, partitions three ways (below, equivalent to and above the pivot) and recurses into the part holding rank `k` [BFPRT 1973][bfprt73], [CLRS 9.3][clrs09]. The three-way partition makes the algorithm correct for total preorders with ties. Before recursing into a side, the program checks without comparisons that the side has at most `selectSideBound n` elements, and returns `none` otherwise. Under an oracle implementing a total preorder the check always passes. It makes the recursion well founded and lets the comparison bound hold for every oracle.

| Declaration | Statement |
|---|---|
| `select_isOrderStatistic`, `eval_select_eq_none` | under an oracle implementing a total preorder `r`, `select k xs` returns an element of rank `k` when `k < xs.length`, and `none` otherwise. No antisymmetry is assumed |
| `eval_select_eq_getElem?_mergeSort` | in a linear order, `select k xs` returns `xs.mergeSort[k]?` |
| `length_filter_lt_le_selectSideBound`, `length_filter_gt_le_selectSideBound` | the median-of-medians counting bound: if the pivot has rank `⌊(g−1)/2⌋` among the `g = ⌈n/5⌉` group medians, at most `n − 3⌊(g−1)/2⌋ − 1` elements lie strictly on either side of it |
| `select_countQueries_le`, `select_upperBound` | `select k` makes at most `37 n` comparisons under every oracle, as `UpperBound (select k) List.length (37 * ·)` |

The cost proof solves `T(n) ≤ 8n/5 + T(⌈n/5⌉) + 2n + T(selectSideBound n)` by strong induction. Sorting the groups costs `8n/5` (`medians_countQueries_le`), the partition costs `2n` (`partition3_countQueries_le`), and the base case costs `n⌈log₂ n⌉ ≤ 10n`. The group cost uses [CountBound.lean](../../Complexity/Algorithms/Lean/Query/Sort/Merge/CountBound.lean), which sharpens cslib's merge bound: a merge makes at most `|xs| + |ys| − 1` comparisons (`merge_countQueries_le_sub_one`), so `mergeSort` sorts five elements with at most `8` (`mergeSortCountBound_five`). Ranks are stated with `List.IsOrderStatistic` in [OrderStatistic.lean](../../Complexity/Foundations/Data/List/OrderStatistic.lean): at most `k` elements lie strictly below `y` and more than `k` lie at or below it. `List.isOrderStatistic_iff_mergeSort` identifies the rank-`k` element of a linear order with `xs.mergeSort[k]`. The [tests](../../ComplexityTests/QuerySelect.lean) run lists longer than the cutoff, duplicates, out-of-range ranks, a preorder with ties and a dishonest oracle.

The constant `37` comes from this simple accounting. Blum, Floyd, Pratt, Rivest and Tarjan refine the algorithm (`PICK`) to at most `5.4305 n` comparisons [BFPRT 1973][bfprt73]; that constant is not formalized. Group sizes other than five, the comparison lower bounds (`n − 1` for the minimum, `⌈3n/2⌉ − 2` for the minimum and maximum together, and the selection lower bounds) and a word-RAM implementation also remain open; see `ROADMAP.md`.

## Shortest paths and priority queues

[abstracts/ComplexityAbstracts/DijkstraAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/DijkstraAbstract.lean) represents directed weighted multigraphs by adjacency lists with natural weights; parallel edges and self-loops are allowed. Output distance is an extended natural, encoded as zero for infinity and `d+1` for a finite distance. The word condition is `8*(n+m+2)*(W+2) < 2^w`.

`dijkstra_logLinear` has `O((m+1)*(floorlog₂(n)+1))` instructions; `dijkstra_fibonacci` has `O(m+n*(floorlog₂(n)+1))`. The graph is already installed in the machine's initial memory. The first bound can omit a standalone scan over isolated vertices because untouched zero memory represents infinity. Treating graph construction or a mandatory full output traversal as charged work would be a different end-to-end contract.

[abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean](../../abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean) specifies bounded-capacity handles, bounded key/value ranges, fresh-handle insertion and arbitrary minimum ties. Initializer/operation code is chosen before capacity/key/value/base/width parameters. The amortized total is constant per ordinary operation plus a sum of logarithms of current size for extract-min; no per-call worst-case bound is stated, even for queries. The operation set has no non-removing find-min: extract-min is the only operation that locates a minimum entry, and it removes that entry. Fresh zeroed memory permits constant-time initialization; the reusable-memory version explicitly clears the region and costs linear time. Both theorems execute demonically admissible adaptive clients (`Client`, whose continuations observe returned handles and extracted entries); external argument preparation, result decoding and pure host continuation choices between `p_op` calls are uncharged.


### Native binary heap and Dijkstra

Choose the API by the cost contract you need. For standalone operation calls, import
`Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Certificate` and use the
`Cslib.DataStructure.PriorityQueue.BinaryHeap.Native` namespace. `dynamicProgram`, `certificate`,
`instruction_bound` and `run_client_bound` provide one fixed program, its representation and
halt-inclusive bounds for admissible calls and adaptive clients. The
[complete priority-queue client](../../ComplexityTests/WordRAMPriorityQueue.lean) supplies the
imports, argument-register setup, representation and valid-history proofs. The
[raw implementation client](../../ComplexityTests/WordRAMBinaryHeapImplementation.lean) also
checks zero capacity, narrow widths, noncanonical tags and retained outside memory.

Keep initialization separate from those call bounds. Here `n` is capacity, `K` the key bound
and `base` the owned base; `Fits w a` means `a < 2^w`. The linked clients supply bounded-state,
argument-matching and representation premises at the points where they are required:

| Route | Storage and prerequisite | Charged initialization |
|---|---|---|
| Fresh compact raw heap | `3*n+1` words, `Fits w (base+3*n+1)`, `Fits w K` and an explicitly zero owned block | The native fresh initializer; no clearing is needed under this premise |
| Dirty compact raw heap | The same `3*n+1`-word region with arbitrary bounded contents | Shared `initClear`: `initTime + 4*space + 6` body instructions, with any final halt separate |
| Allocated memory-program heap | Original `Memory.allocLayout`, with `Fits w (frontier+3*n+2)` and `3*n+2` reserved words | Two dirty memory queries preserve old contents; heap-invariant construction uses `ZeroAbove` |

The [complete initialization client](../../ComplexityTests/WordRAMBinaryHeapInitialize.lean)
checks these distinct layouts and width boundaries. The native certificates are in
[Native/Initialize.lean](../../Complexity/DataStructure/PriorityQueue/BinaryHeap/Native/Initialize.lean).
The two-query count uses `Memory.charge`; its native realization also pays staging and copying.
Dirty allocation does not itself make memory zero, and local zero for one raw initialization is
not a reusable global allocator precondition. If fresh-zero premises are unavailable, retain the
linear dirty-clear allowance instead of applying the fresh theorem.

Standalone calls leave external argument delivery, result decoding and host continuation work
uncharged. For the fully compiled binary-heap Dijkstra client, import
`Complexity.Algorithms.Lean.Dijkstra.Native.Binary`. In its
`Cslib.Algorithms.Lean.Dijkstra.Native.Binary` namespace, `realizes_run` certifies the original
allocated `Memory.run`; `exists_program_state` exports one program/register layout/factor before
all graphs and widths, with full final memory/frontier and the actual prefix, control and halt
charged. Use the [complete native client](../../ComplexityTests/DijkstraNativeBinary.lean) and
[headline client](../../ComplexityTests/WordRAMDijkstra.lean) for their imports, fitting hypotheses
and actual-run conclusions. The encoded graph is still supplied freely in the initial
`Data.init` memory with its zero tail: graph construction and installing those raw input words
are not included. The original word condition and `LogLinearStatement`/`dijkstra_logLinear`
headline are unchanged.

The old `PriorityQueue.WordRAM.BinaryHeap` execution modules and their `Program`/`Sift` imports
are retired. Pure Model/Order declarations now live under `PriorityQueue.BinaryHeap`; use the
native route above for execution. Old fixed register/clock constants and the implementation
helpers with coefficients `200`/`230` are not replacement API guarantees. PQCode and the
Fibonacci execution core with live MinPQ consumers remain; these native Dijkstra endpoints do
not complete generic whole-client realization or the remaining heap migration.

### Native Fibonacci heap and Dijkstra

For the full shortest-path client, import
`Complexity.Algorithms.Lean.Dijkstra.Native.Fibonacci` and use
`Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci.realizes_run` or `exists_program_state`.
The [checked client](../../ComplexityTests/WordRAMDijkstraFibonacci.lean) applies one native
program to the parallel-edge/multi-hop sample, unreachable vertices and sparse edgeless graphs;
it retains the whole source memory and exact allocated frontier. The stable
`fibonacciSpecStatement` and `fibonacciStatement` reader routes in
`Complexity.Algorithms.WordRAM.Dijkstra.Fibonacci` keep their original types. The sharper clock
is `C*(m+min(n,m+1)*(floorlog₂(n)+1))`, and the same program also meets the textbook bound.

One program, register layout and factor precede all runtime graphs and widths. The original
`Fits w (8*(n+m+2)*(W+2))` condition is unchanged. The initialized graph's zero tail permits
dirty reservations of the distance table and original `9*n+5` heap layout without linear
clearing; this is not an arbitrary-dirty-memory initialization theorem. The existing disjoint
framed product composes the heap, mutable distance table and immutable graph; original valid
remaining histories and key bounds establish reached native-method domains. Its nonzero Fibonacci potential telescopes
through the existing amortized refinement; a decrease or extraction is not assigned a
worst-case constant native clock.

The method-level Backend's external argument installation and observation are uncharged. The
full Dijkstra theorem instead charges actual argument staging, arithmetic, copies, early-exit
control, initialized register/frontier prefix and halt. Raw graph placement in `Data.init`
remains free, as in the original specification. The old `fibDijkstra` and its program-specific
`fibDijkstra_spec`, `fibonacciSpec` and `fibonacciLinearSpec` coefficient-640 helpers are
superseded, without claiming that the new uniform factor is 640. The unused GenericPQ Dijkstra
executor is removed, while Model/Trees/Forest, PQCode and the execution core still used by
MinPQ/FibonacciHeapBridge remain. F2, its abstract-space decision and general whole-client
transfer remain open; the selected abstract statements are unchanged.

### All-pairs shortest paths and the (min,+) product

Import `Complexity.Algorithms.Lean.Query.ShortestPaths.MinPlus` for the two reductions and `Complexity.Algorithms.Lean.Query.Arith.FloydWarshall` for Floyd–Warshall; both import the pure walk and matrix-power theory in `Complexity.Algorithms.ShortestPaths`.

These results use the query model `FreeM`, not the word RAM. A weighted digraph on `Fin n` is a matrix over `MinTropical R`, where `R` is any `LinearOrderedAddCommMonoidWithTop`, for example `WithTop ℤ` with negative weights. The tropical `0 = ⊤` means no edge, `*` adds weights and `+` takes minima, so the matrix product is the (min,+) product. [Walk.lean](../../Complexity/Algorithms/ShortestPaths/Walk.lean) defines `walkWeight`, `NoNegCycle` (every closed walk has weight at least `0`) and `IsShortestDistances W D` (each `D i j` is the greatest lower bound of the weights of the walks from `i` to `j`). [Power.lean](../../Complexity/Algorithms/ShortestPaths/Power.lean) proves `isShortestDistances_one_add_pow`: `(1 + W) ^ k` is the distance matrix for every `k ≥ n - 1` when there are no negative cycles. It also proves the negative-cycle test `noNegCycle_iff_one_le_one_add_pow_diag`, which makes `NoNegCycle` decidable [CLRS 25.1][clrs09].

The programs are generic in the entry type, so they combine weights only through `ArithQuery` queries: `.mul` adds weights and `.add` compares them. Correctness theorems assume an oracle that answers `.add` and `.mul` honestly. Cost theorems hold under every oracle. Indexing, `withOneDiag` and building the tripartite matrix are pure code, which `FreeM` does not charge.

| Declaration | Statement |
|---|---|
| `Cslib.Query.floydWarshall`, `cost_floydWarshall`, `isShortestDistances_floydWarshall` | Floyd–Warshall with pivots `0, …, n−1` makes exactly `n³` additions and `n³` multiplications and returns the distance matrix [Floyd 1962][floyd62], [CLRS 25.2][clrs09]. The pure lemma `Cslib.Algorithms.ShortestPaths.isShortestDistances_foldl_fwStep` proves the relaxation correct for every pivot list that contains each vertex, in any order |
| `Cslib.Query.schoolbookMatMul`, `cost_schoolbookMatMul` | the (min,+) product with `n²·(n·cMul + (n−1)·cAdd)` cost |
| `Cslib.Query.apspBySquaring`, `isShortestDistances_apspBySquaring`, `cost_apspBySquaring_le` | APSP from any product subroutine `mp` with `⌈log₂(n−1)⌉` calls, so cost `⌈log₂(n−1)⌉·t` when each call costs at most `t` |
| `Cslib.Query.minPlusViaAPSP`, `eval_minPlusViaAPSP`, `cost_minPlusViaAPSP` | the (min,+) product from one call of any APSP subroutine that is correct on `3n`-vertex graphs without negative cycles, at exactly the cost of that call |

The two reductions are in [MinPlus.lean](../../Complexity/Algorithms/Lean/Query/ShortestPaths/MinPlus.lean), and the [tests](../../ComplexityTests/ShortestPaths.lean) run all programs on a graph with a negative edge. Together they show that a cost-`T(n)` algorithm for either problem gives one for the other with cost `⌈log₂(n−1)⌉·T(n)` or `T(3n)`. This is the starting point of the APSP class of [Vassilevska Williams and Williams][vww18]. The negative-triangle equivalence and the other problems in that class are not formalized. Neither is a word-RAM realization with bit-length costs, so no statement here concerns subcubic running time.

## Depth-first search, topological sort and Bellman–Ford

These are pure Lean functions on adjacency lists, with `TimeM` cost models (as for Kruskal and Edmonds–Karp), not machine programs.

- **Depth-first search.** Import `Complexity.Algorithms.Lean.DFS.Basic` ([source](../../Complexity/Algorithms/Lean/DFS/Basic.lean)). `dfs adj k roots` on `adj : V → List V` visits the roots in turn, with recursion budget `k`; `Fintype.card V ≤ k` suffices. `mem_dfs_visited_iff` and `mem_dfs_finished_iff` say that it discovers and finishes exactly the vertices reachable from the roots. `dfs_finished_order` says that for an edge `u → v` out of a finished vertex, `u` finishes after `v` unless `v` reaches `u`. This is the finishing-time argument in the proof of [Cormen et al., Theorem 22.12][clrs09], which rests on the no-back-edge lemma (Lemma 22.11 there). `time_dfsM` charges one unit per root and one per adjacency-list entry examined. The membership test, insertion and cons are treated as constant-time steps, not charged separately.
- **Topological sort.** Import `Complexity.Algorithms.Lean.DFS.TopologicalSort` ([source](../../Complexity/Algorithms/Lean/DFS/TopologicalSort.lean)). `topologicalSort adj vs` lists the vertices in reverse finishing order. When `vs` lists every vertex, `isTopologicalOrder_topologicalSort_iff` says that the output is a topological order exactly when `Relation.Acyclic (Edge adj)` holds [Cormen et al., Theorem 22.12][clrs09]. `time_topologicalSortM` gives the exact cost `|vs| + ∑ v, |adj v|`.
- **Bellman–Ford.** Import `Complexity.Algorithms.Lean.BellmanFord.Basic` ([source](../../Complexity/Algorithms/Lean/BellmanFord/Basic.lean)). Weights may be negative: they lie in a linearly ordered cancellative additive commutative monoid such as `ℤ`. Walks are `Quiver.Path`s, as for Dijkstra's `Instance.dist`. For a list `vs` of all the vertices, `bellmanFord_eq_none_iff` says that the algorithm returns `none` exactly when a negative cycle is reachable from the source. Otherwise `isShortestDist_of_bellmanFord_eq_some` says that each returned value is the least walk weight, or `⊤` with no walk. Together these are [Cormen et al., Theorem 24.4][clrs09] without the predecessor tree. `time_bellmanFordM` gives the exact cost `n + n (n + m)` for `n = |vs|` and `m` adjacency-list entries.

The [DFS examples](../../ComplexityTests/DFS.lean) include a triangle and a self-loop, on which topological sort is not a topological order. The [Bellman–Ford examples](../../ComplexityTests/BellmanFord.lean) include a negative edge, a reachable negative cycle and an unreachable one, with exact tick counts. Strongly connected components and linear-time 2-SAT are tracked in [#3053](https://github.com/cslib-community/complexitylib/issues/3053).

## Context-free membership and CYK

Like Bellman–Ford, this is a pure Lean function with a `TimeM` cost model, not a machine program.

- **Grammars in Chomsky normal form.** Import `Complexity.Computability.Languages.ChomskyNormalForm` ([source](../../Complexity/Computability/Languages/ChomskyNormalForm.lean)). A `ChomskyNormalFormGrammar` has a list of rules `A → a` (`leaf`) and `A → B C` (`node`), and a flag `nilRule` for the rule `S → ε`. Sipser's definition [Sipser, Definition 2.8][sipser13] forbids the start symbol on every right-hand side; the bundled invariant forbids it only when `nilRule` is set, so Hopcroft, Motwani and Ullman's `ε`-free form, with the start symbol allowed on right-hand sides, is covered too. `toCFG` reads the grammar as a Mathlib `ContextFreeGrammar`, and every statement is about Mathlib's `Derives` and `language` for it. `derives_iff_of_ne_nil` describes the derivations of a nonempty word by a first rule and a split. It rests on `ContextFreeGrammar.derives_append_iff` in [Foundations/Computability/ContextFreeGrammar.lean](../../Complexity/Foundations/Computability/ContextFreeGrammar.lean), which splits a derivation from `u ++ v` into derivations from `u` and from `v`.
- **CYK.** Import `Complexity.Algorithms.Lean.CYK.Basic` ([source](../../Complexity/Algorithms/Lean/CYK/Basic.lean)). `cyk G w` fills the table of nonterminals deriving each subword, level by level, following [Kasami][kasami65], [Younger][younger67] and [Hopcroft, Motwani and Ullman, Section 7.4.4][hmu06]. `mem_table_iff` says that each cell lists exactly the nonterminals deriving its subword. `cyk_eq_true_iff` says that `cyk G w = true` iff `w ∈ G.toCFG.language`, and `decidableMemLanguage` makes membership decidable. `time_cykM` gives the exact cost `(|R| + 1) (n + C(n + 1, 3))` for `|R|` rules and a word of length `n`, and `time_cykM_le` bounds it by `(|R| + 1) (n + 1)³`. One unit is charged per rule examined in each scan, and per split point (or letter) read. Table reads and writes, cell membership tests and insertions are constant-time steps, as on a RAM holding an array of nonterminal sets. Insertion skips nonterminals already present, and `nodup_table_and_length_le` shows that every cell is a list without repetitions of at most `|R|` nonterminals. The pure `cyk` is a specification for proofs and `decide`, not a fast executable (its table is a chain of function updates); the cost statements concern `cykM`.

The [CYK examples](../../ComplexityTests/Algorithms/Lean/CYK.lean) decide accepted and rejected words, including the empty word, for `{aⁿbⁿ}` and for balanced parentheses with `S → ε`, using `decide`, and check exact tick counts. This is the algorithm of [Sipser, Theorem 7.16][sipser13] (every context-free language is in P) **only for grammars already in Chomsky normal form**. Conversion of arbitrary grammars, a machine-level `ComputableInPolyTime` decider, Valiant's subcubic parsing, the pumping lemma, and CFG emptiness and universality are not formalized ([ROADMAP](../../ROADMAP.md#structure-time-and-space), [#3303](https://github.com/cslib-community/complexitylib/issues/3303)).

## Hash families and dictionaries

[abstracts/ComplexityAbstracts/HashTablesAbstract.lean](../../abstracts/ComplexityAbstracts/HashTablesAbstract.lean) selects four expected-amortized dictionary implementations: multiply-shift chained hashing, five-wise linear probing, odd-stride uniform probing and cuckoo hashing. Each supports `query` and `insert` with overwrite, up to bounded distinct-key capacity. **Deletion is not included.** The operation list is fixed before initialization randomness; these are oblivious-sequence guarantees.

The initializer and operation programs are independent of runtime word width and base address, but their dependence on capacity/universe differs by theorem. The abstract does not bound static program-list length. Executed steps exclude caller argument preparation/dispatch. Universe restrictions include the chosen exponent-four polynomial regime; load-factor assumptions and exact initialization costs are visible. These distinctions prohibit a blanket claim of fully dynamic adaptive constant-time dictionaries. The uniform-probing and cuckoo per-operation constants are derived from the capacity threshold `2^320000`: below it they only cap quantities that grow with capacity (the deterministic probe count for uniform probing, the polynomial-hash degree for cuckoo hashing). Their constant bounds are therefore asymptotic statements met trivially at realizable sizes: a linear scan of the stored keys meets the uniform-probing charge at every capacity below `2^320000` and the cuckoo charges (over `8*10^11` instructions per operation) up to about `10^10` keys. For uniform probing the abstract also states the threshold-free bound: at capacity `2^320000` or more, at most three expected probes give at most `13778` expected instructions per operation (`upLargeOpCharge`). No threshold-free charge is stated for cuckoo hashing.

[abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean](../../abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean) gives high-independence hashing with an explicit regime switch at capacity `2^320000`. Below it, finite-field polynomial hashing supplies exact k-wise independence; above it, fixed-parameter double tabulation has a high-probability transcript coupling, with an explicit condition under which the error bound becomes nontrivial. Queries per resampling epoch are restricted to at most `k` distinct keys. Programs may depend on `(k, capacity, universe, outputWidth)`; static code size is not bounded. The all-capacity evaluation bound grows linearly in `k`. At capacity `2^320000` or more, the abstract also bounds every evaluation by `6862` instructions whatever `k` is (`doubleTabEvalTime`, the double-tabulation evaluation cost plus dispatch).

Across capacities the stated space is at most `(k+9232)*(capacity+1)` words, evaluation at most `111230*k+6862` instructions, and resampling at most `(5*k+46096)*(capacity+1)`. These constants are theorem bounds, not measured runtime or a practical implementation recommendation. The large-regime construction adapts Thorup's double-tabulation work; its fixed-k error statement is explicitly different from the source's original growing-independence asymptotic formulation [thorup13][thorup13].

### Fixed-capacity succinct dynamic dictionary

[Complexity/DataStructure/Dictionary/WordRAM/Succinct.lean](../../Complexity/DataStructure/Dictionary/WordRAM/Succinct.lean) provides `Succinct.impl` (over the exact-instruction basis `Basis.exact`) and `Succinct.implStandard` (over the standard basis `Basis.standard`). [ComplexityTests/WordRAMSuccinctDictionary.lean](../../ComplexityTests/WordRAMSuccinctDictionary.lean) gives a checked client. [abstracts/ComplexityAbstracts/SuccinctDictionaryAbstract.lean](../../abstracts/ComplexityAbstracts/SuccinctDictionaryAbstract.lean) states the self-contained formal abstract.

The specification `Dynamic.spec U V n_max` ([Complexity/DataStructure/Dictionary/Dynamic/Spec.lean](../../Complexity/DataStructure/Dictionary/Dynamic/Spec.lean)) supports `query u`, `insert u v` (for key `u : Fin U` and value `v < V`), and `delete u` while the active key set `Dictionary.dom s` has size `#(Dictionary.dom s) ≤ n_max`. For `n_max ≤ U`, initialization draws one hash seed, and every operation keeps that seed unchanged. The seed marginal stays exact (`seedSlack = 1`) against the uniform seed distribution. No persistent flag is kept to latch hash or overflow failures across operations. Each bucket's item count and expected extra collision or overflow probes (`probeExcess`) per operation depend only on the current active key set. The physical chain order and the division of a bucket's items between fixed-size full slabs and the shared tail pool under lazy promotion and demotion thresholds depend on operation history. The single memory block `[base, base + Succinct.space U V w n_max)` uses at most `Dynamic.succinctWords 81 213 U V w n_max` words (the information-theoretic baseline `OPT(U, V, n_max)` plus `81 * n_max * ⌈log₂ ⌈log₂ (max n_max 4)⌉⌉` bits, packed into `w`-bit words, plus `213` words) without requiring a polynomial bound on `U`. Initialization runs in `initTime ≤ Succinct.initSteps U n_max + 1 ≤ 31 * n_max + 1092` expected body instructions (`Succinct.initTime_impl_le`), where body instructions count executed instructions inside the subroutine excluding caller argument setup and the final `halt`. At the `Memory.Prog` level ([Complexity/DataStructure/Dictionary/WordRAM/SuccinctHash.lean](../../Complexity/DataStructure/Dictionary/WordRAM/SuccinctHash.lean)), `queryWithHashProg_dict_spec`, `insertWithHashProg_dict_spec`, and `deleteWithHashProg_dict_spec` bound per-seed amortized `memoryCost` (the `Memory.Prog` instruction count) by `26 + 8 * probeExcess`, `184 + 8 * probeExcess`, and `270 + 8 * probeExcess` with potential `66 * slotPotential`, where `slotPotential` sums the per-bucket slab-hysteresis potentials. In turn, `tsum_uniform_probeExcess_reducedPolyHash_le_five` bounds expected `probeExcess` by `5`. At the compiled Word-RAM level ([Complexity/DataStructure/Dictionary/WordRAM/SuccinctDispatch.lean](../../Complexity/DataStructure/Dictionary/WordRAM/SuccinctDispatch.lean)), the five generic `Memory.Prog` subroutines (`extractQuotGenProg`, `queryWithHashGenProg`, `insertWithHashGenProg`, `deletePrepWithHashGenProg`, `deleteFinishWithHashGenProg`) do not depend on `(U, V, w, n_max)`. The full program `subroutineCode U V w n_max` depends on `(U, V, w, n_max)` only through the `space` constant in `allocSpan` (the bump-allocator step that advances the frontier register by `space`), the 36-instruction parameter-loading prefix `loadParamsCode`, and the hash code. It does not depend on `base`. Consequently, both the register budget `Succinct.rSuccinct` (`≥ 292`) and the per-operation charge `Succinct.chargeVal = 313 * Succinct.opFactor + 284725` (where `Succinct.opFactor` is the maximum of `1` and the five parameter-free subroutines' `Realizes.factor` instruction-per-memory-step constants) are universal `O(1)` constants independent of `(U, V, w, n_max)`, `base`, and `ops.length`. Theorem `Succinct.seq_expected_amortized` bounds expected total body instructions across any valid oblivious sequence `ops` (fixed before initialization) by `initTime + ops.length * Succinct.chargeVal`. No theorem bounds static code size. The hash (`ReducedKWise`) and bit-packed accessors (`BitPackedArray`) are hand-written `WordRAM.Code` primitives. The deterministic bucket, slab, tail, chain, and Feistel bit-extraction subroutines ([Complexity/DataStructure/Dictionary/WordRAM/SuccinctProg.lean](../../Complexity/DataStructure/Dictionary/WordRAM/SuccinctProg.lean) to [Complexity/DataStructure/Dictionary/WordRAM/SuccinctHash.lean](../../Complexity/DataStructure/Dictionary/WordRAM/SuccinctHash.lean)) are `Memory.Prog` programs lowered by `realize`. Because `ReducedKWise` has no `Realizes` certificate, the top-level dispatcher ([Complexity/DataStructure/Dictionary/WordRAM/SuccinctDispatch.lean](../../Complexity/DataStructure/Dictionary/WordRAM/SuccinctDispatch.lean)) is hand-written `WordRAM.Code`. Before calling `Succinct.seq_expected_amortized`, verify `0 < w`, `n_max ≤ U`, `Fits w U` (`U < 2 ^ w`), `Fits w V` (`V < 2 ^ w`), `Fits w (base + Succinct.space U V w n_max)`, word-bounded initial machine state `x.Bounded w` (all initial registers and memory cells hold `< 2 ^ w`), `x.regs Succinct.frontierReg = base`, zeroed initial memory on `[base, base + Succinct.space U V w n_max)`, and `(Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops` for an oblivious sequence `ops` fixed before initialization.

### FKS two-level perfect hashing (static, abstract cost model)

Import `Complexity.DataStructure.Dictionary.PerfectHashing.Construction` ([Construction.lean](../../Complexity/DataStructure/Dictionary/PerfectHashing/Construction.lean)), which re-exports the table layer. [ComplexityTests/PerfectHashing.lean](../../ComplexityTests/PerfectHashing.lean) is a complete checked client: it instantiates a family, builds and checks a concrete table, and applies the construction theorems.

[Complexity/DataStructure/Dictionary/PerfectHashing/Table.lean](../../Complexity/DataStructure/Dictionary/PerfectHashing/Table.lean) and [Construction.lean](../../Complexity/DataStructure/Dictionary/PerfectHashing/Construction.lean) formalize the static dictionary of Fredman, Komlós and Szemerédi [fks84][fks84] in the form of CLRS 3rd ed., Section 11.5 [clrs09][clrs09]. That account uses an arbitrary universal family; FKS's own `k x mod p mod s` family and their `n + o(n)` refinement are not formalized. A `PerfectHashing.Family X` gives, for each range `r`, a seed law `seed r` and functions `hash r s : X → Fin (r + 1)`. Every theorem about the construction assumes `∀ r, IsTwoUniversal (F.seed r) (F.hash r)` and a duplicate-free key list (`keys.Nodup`). The `Valid` conditions are: `n` top buckets (top range `n - 1`), `∑ b_j² ≤ 4n`, a block of exactly `b_j²` cells for each nonempty bucket, and secondary hashes injective on their buckets.

- **Correctness and probes.** `PerfectHashing.lookup F x` is an `OracleComp` that reads memory cells and depends only on the family and the key. `runLookup_memory` proves it answers `decide (x ∈ keys)` on the laid-out `memory D keys` whenever the secondary hashes are injective. `isQueryBounded_lookup` bounds every lookup by `3` reads on any memory (hash evaluation is not charged).
- **Space.** The table is counted in **typed cells**, not words or bits: a cell holds one key, one seed, or one block address with one seed. The cell bound is an `O(n)`-word bound only for families whose seeds fit in `O(1)` words. No such family is formalized yet; a seed of the uniform-function family in the tests is a whole function table. A valid table occupies exactly `n + 1 + ∑ b_j²` cells for `n ≥ 1` (`size_eq`), at most `5n + 2` (`size_le`), and every later cell is empty (`memory_of_size_le`).
- **Construction.** `PerfectHashing.build F fuel keys` is an `OracleComp` over `buildSpec F`. Its calls are `draw r` (a fresh seed) and `eval r s x` (one hash value). Every table in the support of the honest run is `Valid` (`valid_of_mem_support_build`), so it answers correctly and fits in `5n + 2` cells. The cost model is **abstract**: `expectedCost` with `drawCost` or `evalCost` counts seed draws or hash evaluations. Bucketing, success tests and layout are free local computation, and no word-RAM time is claimed. Each level retries at most `fuel` times (`OracleComp.retry`) and the run returns `none` when a level runs out. For `n ≥ 1` keys, failure has probability at most `(n + 1)·2^{-fuel}` (`evalWith_build_none_le`, stated with `keys.length - 1 + 2`). The construction makes at most `2(n + 1)` expected draws (`expectedCost_build_draw_le`) and at most `4n` expected evaluations (`expectedCost_build_eval_le`), uniformly in `fuel`. There is no unbounded Las Vegas form.

The probability core is in [Complexity/Probability/HashFamily/Collisions.lean](../../Complexity/Probability/HashFamily/Collisions.lean):

- `sum_card_filter_sq`: the identity `∑_j b_j² = n + #ordered collisions`;
- `IsUniversalHash.tsum_orderedCollisionCount_le`: at most `n(n - 1)ε` expected ordered colliding pairs, which is `2·C(n,2)ε`;
- `IsTwoUniversal.toOuterMeasure_not_injOn_le`: `Pr[not injective] ≤ 1/2` when `n² ≤ m`;
- `IsTwoUniversal.toOuterMeasure_four_mul_lt_sum_card_filter_sq_le`: `Pr[4n < ∑_j b_j²] ≤ 1/2` when `n ≤ m`.

CLRS states the last two for `m = n²` and `m = n` with strict bounds (`< 1/2`, and `≥ 4n`). The non-strict forms here are the ones the construction's tests use. Markov's inequality for a `PMF` is `Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum` in [Complexity/Probability/PMF/Markov.lean](../../Complexity/Probability/PMF/Markov.lean).

The generic retry combinator, with its geometric failure and cost bounds, is in [Complexity/Languages/Probabilistic/Retry.lean](../../Complexity/Languages/Probabilistic/Retry.lean). That file also has the product-of-programs lemmas (`expectedCost_pi`, union bound `toOuterMeasure_evalWith_pi_exists_le`). The [checked examples](../../ComplexityTests/PerfectHashing.lean) cover:

- the uniform-function family (`isDeltaUniversalHash_uniformOfFintype`);
- a three-key table in `Fin 8` with every lookup and its size checked by `decide`;
- a broken table whose lookup fails;
- a top seed that fails the `4n` test;
- a successful construction run.

Remaining work ([#3276](https://github.com/cslib-community/complexitylib/issues/3276)) includes:

- dynamic perfect hashing;
- a word-RAM realization and a bridge to `w`-bit cell probes;
- the FKS family itself, and the deterministic construction;
- the Fredman–Komlós lower bound on description size.

## Approximate membership filters

Import `Complexity.DataStructure.ApproximateMembership.WordRAM.QuotientFilter` ([Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter.lean](../../Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter.lean)) and construct `QuotientFilter.implOfEps` (for target error `ε ≠ 0` via `epsLog ε`) or `QuotientFilter.impl` (for dyadic error `(1 / 2) ^ k`); see [ComplexityTests/WordRAMQuotientFilter.lean](../../ComplexityTests/WordRAMQuotientFilter.lean) for a complete checked client and [abstracts/ComplexityAbstracts/ApproximateMembershipAbstract.lean](../../abstracts/ComplexityAbstracts/ApproximateMembershipAbstract.lean) for the self-contained formal abstract.

The specification `ApproximateMembership.spec U n ε` enforces strict set validity on active set `S` (`insert u` requires `u ∉ S ∧ #S < n`; `delete u` requires `u ∈ S`; `query u` is always valid) and guarantees zero false negatives on every random branch together with per-absent-query false-positive probability at most `ε` across any fixed valid operation sequence. The constructors require key bit-width `0 < w₀`, word width `2 * w₀ ≤ w` (needed to bit-pack remainders and derive `quotBits w₀ n < w`), universe bound `U ≤ 2 ^ w₀`, memory fit `base + QuotientFilter.space w w₀ n (epsLog ε) < 2 ^ w`, and zeroed owned memory `[base, base + QuotientFilter.space w w₀ n (epsLog ε))` with `qfReg 240 = base`. The single allocated block uses `QuotientFilter.space w w₀ n (epsLog ε) ≤ 640 * ((n * epsLog ε + w - 1) / w + 1)` words, and initialization takes `QuotientFilter.setupSteps w₀ n` expected body instructions. The randomized hash (`ReducedKWise`) and pure bit-packed layout accessors (`SlotArray`) are implemented as low-level primitives. The deterministic cluster navigation, scan, and shift phases in [Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter/Cluster.lean](../../Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter/Cluster.lean) are authored as `QuotientFilter.clusterOpProg : ClusterInput → Memory.Prog ℕ` and lowered via the `realize` tactic (`realizes_clusterOp.code`). Each operation charges at most `QuotientFilter.charge = opStepBound 290 = O(1)` expected executed body instructions, excluding the final `halt` step and caller argument delivery in `qfReg 1` and `qfReg 247`. Compiled programs `p_init` and `p_op` depend on `(w, w₀, n, ε)` with no static code-size bound.

## Global minimum cut

[abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean) treats weighted undirected multigraphs, `n≥2`, fitted total doubled edge weight and word widths sufficient for workspace/trial counters. A single contraction trial is one fixed 16-register program: `42*n²+12*n+21` worst-case instructions and at most `n-2` random calls, always returning a genuine nontrivial cut value. When minimum cut is positive, it succeeds with probability at least `2/(n*(n-1))`.

The Karger–Stein endpoint uses one fixed 24-register program, `O(n² log n)` worst-case steps and `O(n²)` matrix scratch per tree, with success at least `1/(floorlog₂(n)+15)`. Repetition gives minimum-cut **value** with failure at most `1/(2n)` in `O(n² log³ n)`. It does not enumerate all minimum cuts or attain the source's sparse-space formulation. The threshold is an integer inequality rather than a literal square-root expression; the abstract labels the implementation and proof adaptations.

### Deterministic minimum cut: Stoer–Wagner

Import `Complexity.Algorithms.Lean.StoerWagner.Basic` ([Basic.lean](../../Complexity/Algorithms/Lean/StoerWagner/Basic.lean)). It uses the weighted multigraphs of `Cslib.WeightedCut` (`W : Fin n → Fin n → ℕ`, symmetric with zero diagonal) and Karger's contraction (`contractMatrix`, `contractPart`). The algorithm follows [Stoer and Wagner][stoerwagner97].

- **MA orderings:** [MAOrdering.lean](../../Complexity/Foundations/Combinatorics/WeightedCut/MAOrdering.lean) defines `attachWeight W A x = ∑ a ∈ A, W a x`, maximum adjacency orderings (`IsMAOrdering`, decidable) and maximum adjacency search `maSearch`, with ties broken by list order. `cutWeight_singleton_le_of_isMAOrdering` is the MA-ordering lemma ([Nagamochi and Ibaraki][nagamochiibaraki92]; the cut-of-the-phase lemma of [Stoer and Wagner][stoerwagner97]). If an MA ordering ends with `s, t`, then `{t}` weighs at most every vertex set containing exactly one of `s` and `t`. The proof is an induction over the prefixes of the ordering. `cutWeight_singleton_eq_minCutBetween_of_isMAOrdering` restates it as `cutWeight W {t} = minCutBetween W s t`, using the minimum `s`–`t` cut weight shared with the Gomory–Hu development. `maSearch_spec` shows that the search produces an MA ordering.
- **Phase recursion:** `cutWeight_contractCut` shows that merging `t` into `s` preserves the cuts that do not separate them. `minCut_eq_min_contractMatrix` says that `minCut W` is the minimum of the weight of a minimum `s`–`t` cut and the `minCut` after the merge. `minCut_eq_min_minCutBetween` states it as `minCut W = min (minCutBetween W s t) (minCut (contractMatrix W s t))`. `minCut_eq_min_of_isMAOrdering` applies this to one phase.
- **Algorithm:** `stoerWagner W` returns a `CutResult` with one side of a cut and its weight. It is structurally recursive (`run`, with fuel in `maSearch`), so `decide` evaluates it. `stoerWagner_spec`: for `2 ≤ n` and `IsMultigraph W`, the side is a non-trivial cut whose weight is the answered weight, which equals `minCut W`.
- **Cost:** `stoerWagnerM` adds `TimeM.tick` charges to the same program, and `ret_stoerWagnerM` shows that it returns the same result. `time_stoerWagnerM_le` bounds the time by `n ^ 3 + 4 n ^ 2`, and the tests pin the charged time `509` on the 8-vertex example. The unit-cost model is an array implementation; for a phase on `m` supervertices of a graph on `n` vertices:
  - initializing the keys costs `m`;
  - a search step over `r` candidates costs `2 r − 1`;
  - recording a cut of the phase costs `m + n`;
  - a merge costs `4 m + n + 1`: merging row and column `t` into `s`, moving row and column `m − 1` into the freed slot, relabelling the original vertices, and one comparison.

  The charges are annotations; they are not derived from the Lean evaluation, which uses closures.

The [checked examples](../../ComplexityTests/StoerWagner.lean) test three graphs against brute force over all vertex sets. The first is a weighted 4-cycle. The second is the 8-vertex example graph of [Stoer and Wagner][stoerwagner97], with edge weights from a secondary reproduction (Wikipedia's article). It has minimum cut `4`, and search from its vertex `2` gives the ordering `2, 3, 4, 7, 8, 6, 5, 1` of the worked example's first phase, with cut of the phase `5`. The third is the Boost Graph Library example, which asserts minimum cut weight `7`. The examples also show that an ordering without the MA property can end in a pair whose last-vertex cut is not minimal. They cover a disconnected graph and `n = 0, 1, 2`. Not formalized:
- the `O(n m + n² log n)` priority-queue version;
- real weights (rational weights need scaling);
- enumeration of all minimum cuts;
- Nagamochi–Ibaraki sparse certificates;
- Karger's near-linear algorithm;
- Queyranne's symmetric submodular minimization ([#3369](https://github.com/cslib-community/complexitylib/issues/3369)).

The contraction API comes from the randomized Karger module, so this deterministic module imports its probability dependencies; [#3403](https://github.com/cslib-community/complexitylib/issues/3403) tracks moving it into `WeightedCut`.

## Gomory–Hu trees

Import `Complexity.Algorithms.Lean.GomoryHu.WeightedCut` ([source](../../Complexity/Algorithms/Lean/GomoryHu/WeightedCut.lean)). The declarations live in `Cslib.Algorithms.Lean.GomoryHu` and `Cslib.WeightedCut`. This is a theorem-level development: there is no algorithm and no running time. For a weighted multigraph `W : V → V → ℕ` with `IsMultigraph W`, `minCutBetween W s t` is the minimum `s`–`t` cut weight `λ(s, t)` ([source](../../Complexity/Foundations/Combinatorics/WeightedCut/MinCutBetween.lean)). `Network.Flow.IsMaxFlow.value_eq_minCutBetween` identifies it with the value of a maximum `s`–`t` flow in the network with capacities `W`, using the existing max-flow min-cut theorem. [MinCutBetween.lean](../../Complexity/Foundations/Combinatorics/WeightedCut/MinCutBetween.lean) also proves:

- the triangle inequality `min_le_minCutBetween`: `min (λ(u, v)) (λ(v, w)) ≤ λ(u, w)` for `u ≠ w`;
- its consequence `minCutBetween_eq_of_lt`;
- submodularity of `cutWeight W` (`cutWeight_union_add_cutWeight_inter_le`);
- posimodularity of `cutWeight W` (`cutWeight_sdiff_add_cutWeight_sdiff_le`).

The general theory, in [Basic.lean](../../Complexity/Algorithms/Lean/GomoryHu/Basic.lean) and [Existence.lean](../../Complexity/Algorithms/Lean/GomoryHu/Existence.lean), works for any set function `f : Finset V → β` with values in a linearly ordered cancellative commutative monoid. Three definitions carry it:

- `IsMinCutBetween f s t X`: `X` contains `s`, misses `t` and minimizes `f`.
- `edgeSide T u v`: the vertices reachable from `u` in `T` once the edge `uv` is deleted.
- `IsGomoryHuTree f T`: `T` is a spanning tree and, for every tree edge `uv`, `edgeSide T u v` is a minimum `u`–`v` cut. This is the cut-equivalent tree of [Gomory and Hu][gomoryhu61] ([Schrijver 2003][schrijver03], Section 15.4).

`exists_isGomoryHuTree` proves existence for every symmetric (`f Xᶜ = f X`) submodular `f` on a nonempty finite `V`, and `exists_isGomoryHuTree_cutWeight` is the graph case. Gomory and Hu treat graphs only; the symmetric submodular form is the standard abstraction of their proof, which uses only these two properties. The proof follows Gomory and Hu's recursion without contracting vertices. It splits the terminals along a minimum cut, uses `IsMinCutBetween.inter` to uncross the minimum cuts on each side into that side, and joins the two partial trees built recursively with one edge. Three consequences follow:

- `IsGomoryHuTree.exists_isMinCutBetween_of_isPath`: some edge on the `s`–`t` tree path has a side that is a minimum `s`–`t` cut.
- `IsGomoryHuTree.isLeast_minCutBetween`: flow-equivalence. `λ(s, t)` is the least `λ(u, v)` over the edges `uv` of the tree path.
- `card_image_minCutBetween_le`: there are at most `Fintype.card V - 1` distinct values `λ(s, t)` with `s ≠ t`.

To check a candidate tree, first compute its edge sides with `edgeSide_eq_of_forall_adj`: if `S` contains `u`, misses `v` and no other tree edge crosses `S`, then `edgeSide T u v = S`. Then decide the minimum-cut conditions. The [tests](../../ComplexityTests/GomoryHu.lean) do this for the path `0 - 1 - 2 - 3` on a five-edge graph. They also refute a star, and a path for another graph, as Gomory–Hu trees.

Limitations:

- Weights are natural numbers.
- The construction with `n - 1` maximum-flow calls is not formalized, whether in Gomory and Hu's form or in [Gusfield][gusfield90]'s variant without contraction; neither is its running time.
- Minimum cuts are not enumerated.

[#3320](https://github.com/cslib-community/complexitylib/issues/3320) tracks the remaining work.

## Maximum flow: generic push–relabel

Import `Complexity.Algorithms.Lean.MaxFlow.Preflow` ([Complexity/Algorithms/Lean/MaxFlow/Preflow.lean](../../Complexity/Algorithms/Lean/MaxFlow/Preflow.lean)) for the objects of the push–relabel method of [Goldberg and Tarjan][goldbergtarjan88], following [CLRS, Section 26.4][clrs09], on the integral networks of `MaxFlow.Basic`. Antiparallel arcs are allowed. `Network.Preflow` bounds arc flows by the capacities and requires inflow at least outflow at every vertex other than `s`. `Preflow.IsValidLabeling f h` says `h s = |V|`, `h t = 0` and `h u ≤ h v + 1` on every residual arc. `Preflow.push` and `Preflow.relabel` have the preconditions `CanPush` and `CanRelabel`. `IsValidLabeling.push` and `.relabel` keep labelings valid (Lemma 26.16). `exists_canPush_or_canRelabel` shows that an active vertex admits one of the two operations (Lemma 26.14). `not_resReachable` rules out a residual `s`–`t` path (Lemma 26.17). `resReachable_source_of_excess_pos` gives every vertex with positive excess a residual path back to `s` (Lemma 26.19), and `le_of_excess_pos` bounds its height by `2|V| - 1` (Lemma 26.20). With no active vertex, `isMaxFlow_toFlow` shows the preflow is a maximum flow (Theorem 26.18). `isMinCut_gapCut` shows that the vertices above the least empty height level form a minimum cut of the same value. This gap cut is read off from the heights alone.

`Complexity.Algorithms.Lean.MaxFlow.PushRelabel` ([Complexity/Algorithms/Lean/MaxFlow/PushRelabel.lean](../../Complexity/Algorithms/Lean/MaxFlow/PushRelabel.lean)) states the operation bounds for every run of the generic algorithm. A run is a list of operations, each admissible in the state it is applied to (`PushRelabel.State.IsRun`), so the bounds hold for every selection rule. For `s ≠ t`, a run from `PushRelabel.init N` has:

- at most `(|V| - 2)(2|V| - 1) < 2|V|²` relabels (`numRelabels_le`, `numRelabels_lt`; Corollary 26.21);
- at most `|V|` saturating pushes per arc pair of `N.symArcs`, so at most `2|V||E|` (`numSatPushes_le`, `numSatPushes_le_posArcs`; Lemma 26.22, where `E = N.posArcs`);
- fewer than `4|V|²(|V| + |E|)` nonsaturating pushes (`numNonsatPushes_le`, `numNonsatPushes_lt_posArcs`; Lemma 26.23), by the potential `Σ_{v active} h v`;
- at most `maxOps N = O(|V|² |E|)` operations in total (`length_le`; the operation count of Theorem 26.24).

`pushRelabelWith N vs norm` scans the vertex list `vs` for the first active vertex and pushes along its first admissible arc, or relabels it. `pushRelabelWith_correct` shows that it performs a run of at most `maxOps N` operations and returns a maximum flow and a minimum cut of equal value. `pushRelabel` on `Fin n` tabulates the state after every operation, so the kernel can evaluate it. The [checked client](../../ComplexityTests/PushRelabel.lean) runs it with `decide +kernel` on the CLRS six-vertex network (value `23`, `29` operations) and on edge cases: antiparallel arcs, an unreachable sink, a single arc `s → t`, and `s = t`.

Limitations: the bounds count operations and do not charge the selection of an operation, so there is no `TimeM` running-time bound. The FIFO, relabel-to-front and highest-label rules, the gap and global-relabelling heuristics and dynamic trees are not formalized ([#3373](https://github.com/cslib-community/complexitylib/issues/3373)).

## Bipartite matching and Hopcroft–Karp

Import `Complexity.Algorithms.Lean.MaxFlow.HopcroftKarp` ([Complexity/Algorithms/Lean/MaxFlow/HopcroftKarp.lean](../../Complexity/Algorithms/Lean/MaxFlow/HopcroftKarp.lean)). It is a native `TimeM ℕ` program, not a RAM-model program. It takes `G : Fin m × Fin r → Bool` and candidate neighbour lists `adj` with `BipAdjValid G adj` (every edge of `G` occurs in `adj`; extra candidates only cost time). `hopcroftKarpM_correct` gives a maximum matching (`IsMaxMatching`), a minimum König cover (`IsMinVertexCover`), equal sizes, and at most `2 * Nat.sqrt ν` augmenting phases, where `ν` is the maximum matching size. `hopcroftKarpM_time_le` bounds the charged steps by `(2 * Nat.sqrt ν + 1) * (7 * m + 3 * r + 1 + 4 * bipAdjSteps adj) + m + 3 * r`. Ticks are charged per entry of each allocated table (mate, matched-left, layer and visited tables), per mate entry scanned to mark matched left vertices, per left vertex examined when seeding BFS layer `0`, per expanded BFS layer, per frontier left vertex and candidate edge inspected by the BFS, per DFS root and candidate edge scanned by the DFS, per rematched right vertex, and per step of the final matching and cover extraction. Vector reads and writes, list cons, `Finset` insertion, `ℕ`/`Option` comparisons and edge queries `G (u, v)` are free primitives inside those charged steps, as in the Edmonds–Karp solver (the module docstring's "Cost model and limitations" gives the per-phase breakdown). Converting the input into `adj` is not charged. `hopcroftKarpDenseM` uses every pair as a candidate, giving `O(m r √(min m r))`. The [checked client](../../ComplexityTests/HopcroftKarp.lean) builds `adj` for small graphs, discharges `BipAdjValid` by `decide`, evaluates complete runs, and applies `hopcroftKarpM_correct` and `hopcroftKarpDenseM_time_le`.

Outputs use the same `IsMatching`/`VertexCover` vocabulary as the Edmonds–Karp reduction `bipartiteMatchingM`. `card_hopcroftKarpM_matching` shows the two solvers return matchings of the same size, so a client can switch solvers without changing its statements. `decidePerfectMatchingHKM_eq_true_iff` gives the same characterisation of `HasPerfectMatching` as `decidePerfectMatchingM`.

The combinatorial layer is [Complexity/Algorithms/Lean/MaxFlow/AugmentingPath.lean](../../Complexity/Algorithms/Lean/MaxFlow/AugmentingPath.lean). It contains Berge's theorem (`isMaxMatching_iff_forall_not_isAugmentingPath`), the phase lemma (`IsMaximalLayeredAugmentation.noShortAug_augment`) and the phase bound (`IsPhaseRun.le_two_mul_sqrt`). These proofs use a layered counting lemma, `card_mul_le_of_noShortAug`, instead of decomposing `M ⊕ M*` into disjoint augmenting paths; that decomposition is not formalized.

## Chain covers: Dilworth's and Mirsky's theorems

Both theorems are stated for finite posets. Chains and antichains are Mathlib's `IsChain (· ≤ ·)` and `IsAntichain (· ≤ ·)`, and a covering by `k` chains (or antichains) is a colouring `α → Fin k` whose fibres are chains (or antichains). [Complexity/Foundations/Order/Mirsky.lean](../../Complexity/Foundations/Order/Mirsky.lean) proves weak duality in both directions: a chain meets each antichain fibre at most once, and an antichain meets each chain fibre at most once. It also proves Mirsky's theorem, following [Schrijver's lecture notes][schrijver17], Theorem 7.5. Colouring by `Order.height` gives a chain `C` and a covering by `|C|` antichains (`exists_isChain_and_antichain_coloring`). In min–max form, `α` is covered by `k` antichains if and only if every chain has at most `k` elements (`exists_antichain_coloring_iff`). [Mirsky's paper][mirsky1971] was not consulted.

[Complexity/Algorithms/Lean/MaxFlow/Dilworth.lean](../../Complexity/Algorithms/Lean/MaxFlow/Dilworth.lean) proves Dilworth's theorem ([Schrijver][schrijver17], Theorem 7.6; [Dilworth][dilworth1950]) by the bipartite-matching reduction usually credited to [Fulkerson][fulkerson1956], instead of Schrijver's induction. Its graph `ltGraph` joins the left copy of `x` to the right copy of `y` when `x < y`. Folding `mergeLabel` over a matching appends chains along matching edges. `exists_chain_coloring_of_isMatching` turns a matching `M` into `|α| - |M|` chains. `isAntichain_uncovered` and `card_sub_size_le_card_uncovered` show that the elements a vertex cover `C` misses on both sides form an antichain of at least `|α| - |C|` elements. König's theorem (`exists_maxMatching_eq_minVertexCover`) then gives `exists_isAntichain_and_chain_coloring` (an antichain `A` and a covering by `|A|` chains) and the min–max form `exists_chain_coloring_iff`. The Dilworth and Fulkerson papers were not consulted, so the attribution of the reduction to Fulkerson is secondary.

`minChainCoverM e` in [Complexity/Algorithms/Lean/MaxFlow/ChainCover.lean](../../Complexity/Algorithms/Lean/MaxFlow/ChainCover.lean) is the executable version. It is a native `TimeM ℕ` program, not a RAM-model program, on a poset enumerated by `e : Fin n ≃ α` with decidable `<`. It runs `hopcroftKarpDenseM` on `enumLtGraph e`, merges label-table chains along the matching, and reads the antichain off the König cover. `minChainCoverM_correct` shows four things: the label fibres are chains, the returned indices form an antichain, the number of labels (`numChains`) equals the antichain's size, and that size plus the matching's size is `n`. The two optimality statements follow from this. `card_le_card_antichain_of_isAntichain` bounds every antichain by the output's size. `card_antichain_le_of_isChain_fibre` bounds the output's size by the number of chains in any chain cover. `minChainCoverM_time_le` bounds the charged steps by `(2 * Nat.sqrt n + 1) * (10 * n + 1 + 4 * n²) + 2 * n² + 6 * n`, that is `O(n^{5/2})`. Ticks are charged for Hopcroft–Karp, one per label entry allocated or rewritten by a merge, one per scanned pair of indices, and one per index when collecting the antichain. `Finset` membership, `Vector` reads, `Fin n` comparisons and order queries `e i < e j` are free primitives inside those steps; computing `e` is not charged.

[Complexity/Foundations/Combinatorics/ErdosSzekeres.lean](../../Complexity/Foundations/Combinatorics/ErdosSzekeres.lean) derives the Erdős–Szekeres monotone subsequence theorem from Mirsky's theorem ([Erdős–Szekeres][erdosszekeres1935], pp. 467–468). `exists_monotoneOn_or_strictAntiOn_of_mul_lt` gives, for any sequence of more than `r * s` terms in a linear order, a monotone subsequence of `r + 1` terms or a strictly decreasing subsequence of `s + 1` terms. `exists_strictMonoOn_or_strictAntiOn_of_mul_lt` is the injective case. The [checked client](../../ComplexityTests/Dilworth.lean) covers four instances: width `6` and height `4` for divisibility on `{1, …, 12}`, width `3` and height `4` for the Boolean lattice `Finset (Fin 3)`, complete solver runs on divisibility on `{1, …, 6}` and on the rank-`3` Boolean lattice as bitmasks, and the tight sequence `2, 1, 4, 3`.

## Assignment problem and the Hungarian method

Import `Complexity.Algorithms.Lean.MaxFlow.Hungarian` ([Complexity/Algorithms/Lean/MaxFlow/Hungarian.lean](../../Complexity/Algorithms/Lean/MaxFlow/Hungarian.lean)). It is a native `TimeM ℕ` program, not a RAM-model program. `hungarianM c` takes integer costs `c : Fin n × Fin n → ℤ` on the complete bipartite graph and minimizes. `hungarianM_correct` shows three things: the output matching is a minimum-cost perfect matching (`IsMinCostPerfectMatching`), the output potentials `y`, `z` are feasible (`IsFeasiblePotential`), and the cost equals `∑ y + ∑ z`. `hungarianM_time_le` bounds the charged steps by `6 * n ^ 3 + 6 * n ^ 2 + 3 * n`. Ticks are charged per column scanned for a row minimum, per entry of each allocated or rebuilt table (potentials, mate, tree, slack and path tables), per column scanned by the argmin, per tree extension, and per rematched column. Vector reads and writes, list cons, `ℤ` arithmetic and comparisons, and cost queries `c (u, v)` are free primitives inside those charged steps, as in the Edmonds–Karp and Hopcroft–Karp solvers. The module docstring's "Cost model and limitations" gives the per-round breakdown. Rectangular instances and forbidden edges have to be padded or given large costs. For maximum weight, negate the costs.

Egerváry's theorem is available without running the algorithm. `exists_isMinCostPerfectMatching_potential_eq` gives the integral form. `isMinCostPerfectMatching_iff_exists_potential` gives the min–max form, and `exists_perm_assignment` the permutation form. The weak-duality and complementary-slackness lemmas in [Complexity/Algorithms/Lean/MaxFlow/WeightedMatching.lean](../../Complexity/Algorithms/Lean/MaxFlow/WeightedMatching.lean) are stated for arbitrary graphs and arbitrary matchings, for reuse by minimum-cost flow. The [checked client](../../ComplexityTests/Hungarian.lean) evaluates complete runs, including an instance where greedy fails and one that needs dual adjustments. It checks the optimum against all permutations of a `3 × 3` instance, verifies the dual certificates independently, and applies `hungarianM_correct` and `hungarianM_time_le`.

## General matching: Berge's lemma and the Tutte–Berge formula

These results are about matchings in arbitrary finite graphs, not necessarily bipartite. They are stated on Mathlib's `SimpleGraph` and `SimpleGraph.Subgraph.IsMatching`, not on the bipartite `L × R → Bool` model above, and there is no executable algorithm yet.

[Complexity/Foundations/Combinatorics/SimpleGraph/Berge.lean](../../Complexity/Foundations/Combinatorics/SimpleGraph/Berge.lean) defines:
- `Subgraph.IsAugmentingPath M p`: a path between distinct uncovered vertices that alternates in Mathlib's `IsAlternating` sense;
- `Subgraph.augment M p`: `M ∆ E(p)`;
- `Subgraph.IsMaximumMatching`: a matching with at least as many edges, counted by `Set.encard`, as every matching.

`IsAugmentingPath.isMatching_augment` and `ncard_verts_augment` show that augmenting gives a matching covering two more vertices. `IsMatching.isMaximumMatching_iff_forall_not_isAugmentingPath` is Berge's lemma for finite graphs ([Berge 1957][berge57], Theorem 1; [Schrijver's lecture notes][schrijver17], Theorem 3.2). It is proved from `IsMatching.exists_isAugmentingPath_of_ncard_lt`, using the odd-degree vertices of a component of `M ∆ M'`. `exists_isMaximumMatching` gives a maximum matching of a finite graph, and `IsPerfectMatching.isMaximumMatching` shows that perfect matchings are maximum. The bipartite Berge theorem in `MaxFlow/AugmentingPath` is a separate statement in its own model; neither is derived from the other.

[Complexity/Foundations/Combinatorics/SimpleGraph/TutteBerge.lean](../../Complexity/Foundations/Combinatorics/SimpleGraph/TutteBerge.lean) proves the Tutte–Berge formula ([Berge 1958][berge58]; [Schrijver's lecture notes][schrijver17], Theorem 5.1) with vertex counts, writing `o(G - U)` as `((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard`:
- `IsMatching.ncard_verts_add_ncard_oddComponents_le` (weak duality): `|V(M)| + o(G - U) ≤ |V| + |U|`.
- `exists_isMatching_ncard_verts_add_ncard_oddComponents_eq` (strong duality) is derived from Mathlib's `SimpleGraph.tutte` by adjoining `d` universal vertices, where `d` is the maximum deficiency.
- `IsMatching.isMaximumMatching_iff_exists_ncard_verts_add_ncard_oddComponents_eq`: a single `U` certifies that a matching is maximum.
- `IsMaximumMatching.isLeast_two_mul_ncard_edgeSet`: `2ν(G)` is the least value of `|V| + |U| - o(G - U)`.

The [checked instances](../../ComplexityTests/GeneralMatching.lean) cover three graphs:
- On the path `0 - 1 - 2 - 3`, an explicit walk is an augmenting path for `{12}`.
- On the `5`-cycle, `U = ∅` certifies the matching `{01, 23}`.
- On the star `K_{1,3}`, `U = {0}` certifies the matching `{01}`.

Still open ([#3337](https://github.com/cslib-community/complexitylib/issues/3337)):
- Edmonds' blossom-contraction lemma ([Schrijver's lecture notes][schrijver17], Theorem 5.2);
- an executable blossom algorithm with its `O(|V|²|E|)` bound;
- weighted general matching;
- the Gallai–Edmonds decomposition.

## Matroid intersection

Import `Complexity.Algorithms.Lean.Matroid.Intersection` ([Complexity/Algorithms/Lean/Matroid/Intersection.lean](../../Complexity/Algorithms/Lean/Matroid/Intersection.lean)). It proves Edmonds' matroid intersection theorem for Mathlib matroids `M₁ M₂ : Matroid α` relative to a finite candidate set `E : Finset α`, following the augmenting-path proof of [Schrijver's lecture notes][schrijver17], Section 10.5. The matroids' ground sets need not equal `E`: elements outside `Mᵢ.E` behave as loops. `iSup_card_eq_iInf_eRk_add_eRk` states that the maximum of `I.card` over common independent `I ⊆ E` equals the minimum of `M₁.eRk U + M₂.eRk (E \ U)` over `U ⊆ E`. `iSup_encard_eq_iInf_eRk_add_eRk` gives the same equality for a finite `X : Set α`. Taking `X` to be the common ground set gives the source's Theorem 10.9. `exists_commonIndep_card_eq_eRk_add_eRk` and its `ℕ`-valued companion give a maximum common independent set together with an optimal `U`. Weak duality (`encard_le_eRk_add_eRk`) needs no finiteness.

The algorithmic layer is stated on explicit objects. `IsExchSource`, `IsExchSink` and `IsExchArc` are the source set, sink set and arcs of the exchange digraph `H(M₁, M₂, I)`, displays (23)–(24) of the notes. A walk is a `List α` (`IsExchWalk`, `IsExchAugWalk`), and `IsShortestExchAugWalk` asks for the minimum number of vertices. `IsShortestExchAugWalk.augment` (Theorem 10.6) shows that `I ∆ p.toFinset` is a common independent subset of `E` of size `I.card + 1`; it relies on `indep_exchange_chain`, the chordless-exchange step of Lemma 10.2. `exists_separator_of_not_exists_exchAugWalk` (Theorem 10.7) shows that when no augmenting walk exists, the set of vertices unreachable from the sources attains the bound. The [tests](../../ComplexityTests/MatroidIntersection.lean) include a walk that is augmenting but not shortest, along which the exchange breaks `M₁`-independence, so the shortest-walk hypothesis cannot be dropped.

`Complexity.Algorithms.Lean.Matroid.Intersection.Konig` ([Complexity/Algorithms/Lean/Matroid/Intersection/Konig.lean](../../Complexity/Algorithms/Lean/Matroid/Intersection/Konig.lean)) connects this to the bipartite matching vocabulary above. `unitPartitionMatroid f` is the free matroid pulled back along `f`, in which a set is independent when `f` is injective on it. `isMatching_iff_isCommonIndep` identifies matchings of `G : L × R → Bool` with common independent subsets of `bipartiteEdges G` for the `Prod.fst` and `Prod.snd` partition matroids (Example 10.5a). `exists_maxMatching_separatorCover` derives König's theorem from Edmonds' theorem (Exercise 10.22). The cover is read off from the separator, and its minimality uses the existing matching/cover weak duality. The flow-based König theorem `exists_maxMatching_eq_minVertexCover` remains the primary statement; the tests recover its form from the matroid route.

The executable solver is in `Complexity.Algorithms.Lean.Matroid.Intersection.Solver` ([Complexity/Algorithms/Lean/Matroid/Intersection/Solver.lean](../../Complexity/Algorithms/Lean/Matroid/Intersection/Solver.lean)). Its independence tests are effectful, `Finset α → m Bool` for a monad `m`. One phase (`exchTablesM`) computes the sources, sinks and arcs of the exchange digraph of the current `I` by tests. It then runs a multi-source breadth-first search, `Cslib.Reachability.findWalk` ([Complexity/Algorithms/Reachability/ShortestWalk.lean](../../Complexity/Algorithms/Reachability/ShortestWalk.lean)). The search returns either a shortest source-to-sink walk (`isShortestSrcTgtWalk_of_findWalk_eq_inl`) or the reachable vertices, which form a separator (`isSrcTgtSeparator_of_findWalk_eq_inr`). `maxCommonIndepM` runs at most `n + 1` phases from `∅` on the `n` distinct candidates and returns `(I, U)`, where `U` is the set of unreachable candidates. `maxCommonIndep` is the same program with Boolean tests (`maxCommonIndepM_pure`). For tests that decide `M₁` and `M₂`, `maxCommonIndep_spec` (Theorem 10.8) shows that `I` is a maximum common independent subset of `es.toFinset` and that `U ⊆ es.toFinset` satisfies `I.card = M₁.eRk U + M₂.eRk (es.toFinset \ U)`, so `U` is a checkable optimality certificate. Breadth-first search and list bookkeeping are pure host computation. The tests are issued with core `List.filterM`. The general facts about it are `List.filterM_pure` and `Cslib.IsMonadHom.map_filterM` in [Complexity/Foundations/Control/Monad/FilterM.lean](../../Complexity/Foundations/Control/Monad/FilterM.lean), and `Cslib.FreeM.countQueries_filterM` in [Complexity/Algorithms/Lean/Query/FreeM/FilterM.lean](../../Complexity/Algorithms/Lean/Query/FreeM/FilterM.lean).

`Complexity.Algorithms.Lean.Query.Matroid.Intersection` ([Complexity/Algorithms/Lean/Query/Matroid/Intersection.lean](../../Complexity/Algorithms/Lean/Query/Matroid/Intersection.lean)) runs the solver in `FreeM (IndepPairQuery α)`. Here `IndepPairQuery α = IndepQuery α ⊕ IndepQuery α`, one independence oracle per matroid, and `IndepPairQuery.left`/`right`/`pair` split and join oracles. Only the independence tests are counted. `eval_matroidIntersection_spec` is the correctness theorem for oracles with `ImplementsMatroid (left oracle) M₁` and `ImplementsMatroid (right oracle) M₂`. On `n` distinct candidates a phase from `I` makes exactly `2(n - |I|)(1 + |I|)` queries (`countQueries_exchTablesM_of_nodup`). For every oracle, even one that implements no matroid, `matroidIntersection_upperBound` gives a `Cslib.Query.UpperBound` of `2n(n + 1)²` in the list length. For oracles implementing matroids, `countQueries_matroidIntersection` gives the exact count `∑_{r=0}^{ν} 2(n - r)(1 + r)`, where `ν` is the size of the output, and `countQueries_matroidIntersection_le` bounds it by `2n(ν + 1)²`. These counts describe this implementation, which rebuilds the exchange digraph in every phase. The source states only polynomial running time. The [solver tests](../../ComplexityTests/MatroidIntersectionSolver.lean) check:
- shortest-walk and separator outcomes of the search;
- a bipartite matching run that needs a three-vertex augmenting walk, with 20 queries;
- a colourful-forest run (a graphic matroid against a colour partition matroid) that exchanges an edge, with 40 queries;
- the correctness theorem at `Type 1`.

`TimeM` costs for the host computation (the search, the list filters and the symmetric difference) are not charged yet; that remaining work is tracked in [#2018](https://github.com/cslib-community/complexitylib/issues/2018). Weighted matroid intersection and infinite ground sets are not treated.

## Stable matching

Import `Complexity.Algorithms.Lean.StableMatching.Incentives` (which also brings in `Basic`, `DeferredAcceptance` and `Blocking`) and `Complexity.Algorithms.Lean.StableMatching.Lattice`; the declarations live in the namespace `Cslib.Algorithms.Lean.StableMatching`. This is a pure Lean development, not a RAM client. An `Instance n` has `n` proposers and `n` receivers with strict complete preference lists (`Fin n → Equiv.Perm (Fin n)`, rank `0` most preferred); a `Matching n` is a permutation, and `IsStable` means no blocking pair. `Instance.deferredAcceptance` is a total, `decide`-evaluable implementation of proposer-proposing deferred acceptance whose state is the vector of rejection counts. The modules prove stability of the output, the bound `proposals_le : I.proposals ≤ n ^ 2 - n + 1`, proposer-optimality and receiver-pessimality, the distributive lattice `Instance.Stable I` with deferred acceptance as `⊤` and its receiver-proposing dual as `⊥`, the blocking lemma `exists_isBlockingPair_of_lt`, weak Pareto optimality, and coalitional strategy-proofness for proposers (`not_forall_mem_propRank_lt_of_isStable`). Roth's impossibility theorem `MatchingMechanism.not_isStable_and_strategyProof` is proved for three agents on each side (`MatchingMechanism 3`), with the checked witness `MatchingMechanism.rothInstance`. That suffices for the existential impossibility; the statement for every `n ≥ 3` is not formalized.

The cost measure is the number of proposals, a property of the algorithm's trace rather than of a machine model; no Word-RAM or Turing implementation is certified. Incomplete lists, ties, unequal sides and many-to-one markets are not modeled; [#2990](https://github.com/cslib-community/complexitylib/issues/2990) tracks these directions. [ComplexityTests/StableMatching.lean](../../ComplexityTests/StableMatching.lean) contains the checked instances.

## Assignment problem: Bertsekas's auction algorithm

Import `Complexity.Algorithms.Lean.Assignment.Auction` ([Complexity/Algorithms/Lean/Assignment/Auction.lean](../../Complexity/Algorithms/Lean/Assignment/Auction.lean)); the declarations live in the namespace `Cslib.Algorithms.Lean.Assignment`. This is a pure Lean development, not a RAM client. The input is an integer cost matrix `c : Fin n × Fin n → ℤ` on the complete bipartite graph, and an assignment is a permutation `σ : Equiv.Perm (Fin n)` of cost `∑ i, c (i, σ i)`, to be minimized. `auction c ε` is the Gauss–Seidel auction of [Bertsekas][bertsekas88] in the cost form of [Bertsekas][bertsekas98], §7.1.1: an unassigned person bids for an object of least reduced cost `c (i, j) + p j`, raising its price by the gap to the second least reduced cost plus `ε`, and evicts the previous owner. Unassigned persons are kept on a stack. Fuel `bidBound n (costSpread c) ε` is computed from the data, so the function is total and `decide`-evaluable.

- **Invariant:** `AuctionInv.bidStep` is Prop. 7.1: each bid preserves `ε`-complementary slackness for the partial assignment (the `AuctionInv.epsCS` field, stated for assigned pairs). The complete-assignment form `IsEpsCompSlack` is recovered for the output by `isEpsCompSlack_auctionPerm`.
- **Termination:** `auction_free` gives termination with every person assigned. `bids_auction_le` bounds the number of bids by `bidBound n C ε = n (C + ε) / ε + 1` whenever every row cost range `c (i, k) - c (i, j)` is at most `C`. The proof uses the explicit measure `n (C + ε) - ∑ j, p j` (`sum_price_bidStep`, `AuctionInv.price_le`) in place of the book's argument by contradiction for Prop. 7.2.
- **Quality:** `auctionPerm c hε` is the output. `sum_auctionPerm_le` shows that it is within `n * ε` of every permutation (Props. 1.4 and 7.2). `sum_auctionPerm_le_rowPotential` turns the final prices into the feasible dual `(rowPotential c p, -p)` certifying this.
- **Exactness:** `scaledAuction c` runs the auction on `(n + 1) * c` with `ε = 1`, and `scaledAuctionPerm c` is its assignment. `sum_scaledAuctionPerm_le` proves it optimal, and `bids_scaledAuction_le` bounds the bids by `n ((n + 1) C + 1) + 1`.

The general layer [Complexity/Algorithms/Lean/Assignment/Basic.lean](../../Complexity/Algorithms/Lean/Assignment/Basic.lean) states `ε`-complementary slackness, weak duality over permutations and the `n ε` bound for any finite index type and ordered additive group. The cost measure is the number of bids: the `O(n)` scan per bid is not charged and there is no `TimeM` accounting. The bound is pseudo-polynomial, linear in `C / ε`. The `ε`-scaling version with its `O(n A log (n C))` bound (Prop. 7.3), the Jacobi, reverse and asymmetric auctions, rectangular or sparse instances, and a bridge to the potentials of the [Hungarian method](#assignment-problem-and-the-hungarian-method) are open; [#3317](https://github.com/cslib-community/complexitylib/issues/3317) tracks these directions. [ComplexityTests/AuctionAssignment.lean](../../ComplexityTests/AuctionAssignment.lean) contains the checked instances:

- a `3 × 3` optimum checked against all six permutations, with its dual certificate;
- a `2 × 2` instance on which the unscaled auction is suboptimal, showing that the scaling is needed;
- Bertsekas's price war (Figs. 1.12–1.14), whose bid count grows with `C / ε`;
- the cases `n = 0` and `n = 1`.

## Housing markets and top trading cycles

Import `Complexity.Algorithms.Lean.HousingMarket.Incentives` (which also brings in `Basic` and `TopTradingCycles`); the declarations live in the namespace `Cslib.Algorithms.Lean.HousingMarket`. This is the housing market of [Shapley and Scarf][shapleyscarf74]. An `Instance n` gives each of `n` agents a strict complete preference list over the `n` houses, using the stable-matching conventions above (`pref : Fin n → Equiv.Perm (Fin n)`, rank `0` most preferred). Agent `i` owns house `i`, and an `Allocation n` is a permutation. A coalition `S` may only reallocate its own houses, that is, use permutations `ν` with `ν i ∈ S` for `i ∈ S`. There are two notions of blocking. `Blocks` asks for every member strictly better off, and its unblocked allocations are the core (`InCore`). `WeaklyBlocks` asks for all members weakly better off and one strictly better off, and its unblocked allocations are the strict core (`InStrictCore`). [Schummer and Vohra][schummervohra07], §10.3, call the latter "the core". With strict preferences the two notions still differ: the checked tests contain a core allocation outside the strict core. This contradicts the claim of [Schummer and Vohra][schummervohra07], p. 255, that they coincide for strict preferences. Their argument drops weakly blocking members who are not strictly better off as if they kept their own houses, but such a member may keep a house it received in the trade.

`Instance.ttc` is Gale's top trading cycles algorithm as a total, `decide`-evaluable function. In each round every remaining agent points to the owner of its favourite remaining house (`topChoice`). The agents on cycles (`cycleAgents`, the periodic points of the pointer map) receive the houses they point to and leave. All cycles of a round are removed together, as in [Schummer and Vohra][schummervohra07], Definition 10.5, and `n` rounds suffice. The main results:

- `inStrictCore_iff : I.InStrictCore μ ↔ μ = I.ttc`: the strict core is exactly the TTC allocation ([Roth and Postlewaite][rothpostlewaite77]; [Schummer and Vohra][schummervohra07], Theorem 10.6, whose core is defined by weak blocking).
- `inCore_ttc`, `isIndividuallyRational_ttc`, `isParetoEfficient_ttc`: consequences of strict-core membership. `inCore_ttc` is the existence half of [Roughgarden's CS364A][roughgarden13cs364a], Lecture #9, Theorem 3.2. That lecture defines the core by strict blocking, and for that notion the uniqueness half fails (see the second test market below).
- `isCompetitive_ttc`, `IsCompetitive.inStrictCore` and `exists_isCompetitive_iff`: TTC is competitive (every agent can afford its house and prefers it to every house it can afford) at the prices `ttcPrice`, the number of agents present in the round in which the house leaves. Competitive allocations lie in the strict core, so an allocation is competitive at some `ℕ` prices iff it is the TTC allocation.
- `HousingMechanism.isStrategyProof_topTradingCycles`: the TTC mechanism is strategy-proof ([Roth][roth82]; [Schummer and Vohra][schummervohra07], Theorem 10.7; [CS364A][roughgarden13cs364a], Lecture #9, Theorem 3.1). A misreport by agent `i` can only change the pointers of agent `i`. Before agent `i` leaves, the cycles that do not contain `i` are unchanged, and every house that agent `i` can reach is one it could reach under truthful reporting.

Scope: preferences are strict, every agent owns exactly one house, the market size `n` is fixed by `Fin n`, and only individual (not group) strategy-proofness is proved. No running time is charged: `ttc` is a mathematical function, not a `TimeM` or RAM program, so the `O(n²)` bound for TTC is not stated. House allocation with existing tenants (Abdulkadiroğlu–Sönmez), Ma's characterization of TTC, group strategy-proofness and indifferences are directions recorded in [#3286](https://github.com/cslib-community/complexitylib/issues/3286). [ComplexityTests/HousingMarket.lean](../../ComplexityTests/HousingMarket.lean) contains the checked instances: a three-cycle, a two-cycle followed by a fixed point, TTC prices, uniqueness by enumeration, and two small mechanisms: keeping the endowment is strategy-proof but not Pareto efficient, and a two-agent mechanism is manipulable.

## Scheduling bounds

[Complexity/Algorithms/Lean/Scheduling/](../../Complexity/Algorithms/Lean/Scheduling/) contains
classical makespan bounds as mathematical statements about schedules. These are not runtime claims.
`IdenticalMachines.lean` models `P || C_max`: an assignment `σ : Fin n → Fin m` of jobs with
processing times `p : Fin n → α` (an ordered field for the ratio theorems). `IsListSchedule p σ`
is Graham's rule that each job goes to a least-loaded machine over the earlier jobs.
`listSchedule` computes such an assignment. `IsListSchedule.makespan_le_optMakespan` proves
`C ≤ (2 - 1/m) · OPT`, and `IsListSchedule.makespan_grahamTight` shows that the ratio is
attained for every `m`. `LPT.lean` defines `lptSchedule`, which applies `listSchedule` after
sorting by `lptOrder`, and proves `makespan_lptSchedule_le`: `C ≤ (4/3 - 1/(3m)) · OPT`.

`Precedence.lean` models `P | prec | C_max` in discrete time. Start times are `s : J → ℕ`,
processing times are natural numbers and `prec` is any relation; the bounds assume it is
well-founded. `IsFeasible` and `IsGreedy` are predicates on
schedules. `exists_isGreedy` constructs a greedy schedule for well-founded precedences and
positive processing times. `IsGreedy.exists_chain` is Graham's critical chain.
`IsGreedy.mul_makespan_le_of_le` is Graham's 1966 anomaly theorem. `Brent.lean` defines the
critical-path `span` and proves the work and span laws, the greedy bound
`m · T ≤ ∑ p + (m - 1) · span`, and Brent's lemma for unit-time DAGs
(`exists_isFeasible_mul_makespan_le`). Two limitations apply: processing times in the precedence
model are integers, and Graham's anomaly instances are not formalized.
[ComplexityTests/Scheduling.lean](../../ComplexityTests/Scheduling.lean) checks the tight
instances, nonvacuity of `IsGreedy`, a feasible schedule that is not greedy, and a zero-length
self-loop showing that the critical-chain theorem needs well-founded precedences.

## Divide-and-conquer recurrences

[MasterTheorem.lean](../../Complexity/Foundations/Data/Nat/MasterTheorem.lean) solves divide-and-conquer cost recurrences over `ℕ` with explicit constants. `Nat.DivideConquerBound T a b n₀ T₀ f` has two parts:

- The base bound: `T n ≤ T₀` for `n ≤ n₀`.
- The recursive step: for `n > n₀`, every `S` that bounds `T` on `[0, ⌈n/b⌉]` gives `T n ≤ a S + f n`.

So a cost function with floor and ceiling splits, or several subproblems of size at most `⌈n/b⌉`, satisfies it directly. Monotonicity is not required and the recurrence need not be an equality. To prove `step` for a concrete recurrence:

1. Unfold one level with `rw`. If the definition's pattern match does not rewrite cleanly, state the one-level equation first.
2. Instantiate `hS` at each subproblem size, proving each `m ≤ (n + b - 1) / b` with `omega`.
3. Normalize `c * n ^ d` with `simp only`.
4. Close the goal with `omega`.

The clients below follow this recipe.

`DivideConquerBound` itself imposes no condition on `a`, `b` or `n₀`, and without further hypotheses the conclusions below can fail. For example, `T n = n` with `a = b = n₀ = T₀ = 1` and `c = d = 0` satisfies the contract, because `⌈n/1⌉ = n`, yet case 2 would give `T 2 ≤ 1`.

`DivideConquerBound.le_sum` unrolls the recursion for `a ≥ 1` and monotone `f`. For `f n = c n ^ d` the three cases follow. All three statements in the table assume `a ≥ 1`, `b ≥ 2` and `n₀ ≥ 1`:

| Case | Lean statement | Bound |
|---|---|---|
| `a > b ^ d` | `sub_mul_le_pow_clog` | `(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ ⌈log_b n⌉` |
| `a = b ^ d` | `le_mul_pow_mul_clog` | `T n ≤ (b n) ^ d (T₀ + c n₀ ^ d ⌈log_b n⌉)` for `n ≠ 0` |
| `a < b ^ d` | `pow_sub_mul_le_mul_pow` | `(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d` for `n ≠ 0` |

[MasterTheoremAsymptotics.lean](../../Complexity/Foundations/Data/Nat/MasterTheoremAsymptotics.lean) turns these into `O(n ^ log_b a)`, `O(n ^ d log n)` and `O(n ^ d)` as Mathlib `IsBigO` statements (`isBigO_rpow`, `isBigO_pow_mul_log`, `isBigO_pow`). In case 1 it also gives an explicit real-power bound (`le_mul_rpow`). The conversions are the base-`b` lemmas `Nat.pow_clog_le_mul_rpow_logb` and `Nat.clog_le_two_mul_logb` in [LogTwoRpow.lean](../../Complexity/Foundations/Data/Nat/LogTwoRpow.lean), whose base-`2` cases are used by Karatsuba. Mathlib's `Mathlib.Computability.AkraBazzi` proves the more general Akra–Bazzi `Θ` bound, but it needs an equality recurrence over `ℝ` with positive base values. The statements here give upper bounds only. Case 3 is proved for polynomial `f`, not under the general regularity condition. Applied to cslib's merge-sort count, case 2 gives `2 n ⌈log₂ n⌉`, which is weaker by the factor `b` than cslib's own `n ⌈log₂ n⌉`. The halving lemma `Nat.add_mul_two_pow_clog_le_of_halving` ([HalvingRecurrence.lean](../../Complexity/Foundations/Data/Nat/HalvingRecurrence.lean)) remains the sharper tool for `b = 2`. It carries a subtracted lower-order term through the induction, which the Karatsuba addition count needs (`addCount_add_le_pow_clog`).

The checked client [MasterTheorem.lean](../../ComplexityTests/MasterTheorem.lean) applies the theorem to:

- cslib's `timeMergeSortRec`;
- Karatsuba's `mulCount`, recovering `mulCount_le_pow_clog`;
- a Strassen-shaped `7 T(⌈n/2⌉) + n²`, giving `O(n ^ log₂ 7)`;
- a binary-search recurrence;
- a base-`3` case-3 recurrence.

It also refutes the hypothesis for `n²`. Build with

```bash
lake build Complexity.Foundations.Data.Nat.MasterTheoremAsymptotics ComplexityTests.MasterTheorem
```

## Other clients and classification

The source tree also contains native integer arithmetic, multiword circuit evaluation, matrix multiplication, primality/counting, predecessor structures, 3SUM/exact-triangle routines and randomized SAT algorithms. These broaden coverage of the machine library; they should be catalogued through the complete module census without counting each as a new model. In particular, a bounded frontend or a conditional transfer theorem should not be presented as completion of an unresolved fine-grained endpoint. The current `ROADMAP.md` and selected abstracts are better evidence of endpoint disposition than a directory name.

## Canonical 3SUM pipeline and parameter migration

There is one executable pipeline: `DyadicParameters` computes geometry,
`ParameterSelecting` selects the prime and dispatches, and `CallableFixedPrime` calls the
box-backed `StreamingFixedPrime` controller. Both ordinary 3SUM endpoint theorems use that pipeline.
The former `Box`-prefixed module families are retired; import the canonical modules named
below. Existing `RecordBoxProduct` and `BoxTable` names still describe the underlying
mathematics and are not alternate end-to-end solvers.

This migration changes finite parameters, not only import spelling. The canonical family is
`b = floor(log2(n)/2394)`, `m = 63b`, `D = 4^m`, `g = 4^(2b)` and `L = 21m`.
The first fast branch is now at `n = 2^2394`; the old 1296-bit family and its `m=36b`,
`g=4^b`, `L=19m` bounds are removed. Inputs between the old and new branch thresholds now use
the actual exhaustive branch. Recheck finite `timeBound` and geometry/admission premises with
the current declarations rather than reusing the old finite constants.
The [parameter client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMExactTriangleDyadicParameters.lean)
evaluates actual code at zero, just below the new threshold and at the threshold. The headline
1.9992 exponent, distinct-position meaning and native resource guarantees below are unchanged.

## Maintaining the per-record product and witness clients

For a prepared record, use `RecordProduct.exec_of_output` or
`RecordBoxProduct.exec_of_output` with the genuine `Instances.Output`. Both concrete
programs derive their source spans through `RecordProduct.producer_readback` in
`Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback`; that pure module
also exposes the record data and ordered query decoder. It needs no initialized product run.
Use `RecordProduct.NumericBounds` and `RecordWitness.NumericBounds` for numerical width
and word estimates. The actual all-prefix execution theorems remain in `RecordProduct.SourceBounds` and
`RecordWitness.SourceBounds`, each following from its real `runs_input` theorem.

`RecordBoxProduct.program` uses the physical pointer front
[`PointerBoxProduct.exec`](../../Complexity/Algorithms/WordRAM/MatrixMultiplication/Schonhage/CallableBox/Pointer/Exec.lean).
For a separate caller, initialize its five scalar/header words and appended threshold, supply
raw row-major X/Y pointers and the interleaved query pointer, and prove all three source ends
lie below the private base. The front computes its own virtual width and snapshot layout,
then physically gathers the header and external arrays directly into that snapshot. Physical
pointers occupy registers outside the normalized source bank and may exceed the virtual modulus.
Source/source aliases are permitted when their readback agrees. The private low matrix/query
payload and remaining workspace may be dirty.

The [pointer client](../../ComplexityTests/WordRAMSchonhagePointerBox.lean) executes raw binary
matrices, duplicate occurrences, zero queries and dirty reuse with a changed query count at
physical pointers above the virtual modulus. Returned answers are exact physical signed words;
external sources and memory outside the window survive. Original routing, matrix doubling,
restoration and both final normalization loops remain. The snapshot remains live until matrix
adaptation and restoration finish. `RecordBoxProduct.gatherTimeBound_ledger` accounts for the
actual gather and bridge instructions, and `gatherTimeBound_le_timeBound` bounds `gatherTimeBound`
by the conservative `RecordBoxProduct.timeBound` envelope. This compares certified allowances, not
measured execution times; it changes neither the reserved window nor the 1.9992/2.99835 headline
exponents. `RecordProduct` and contiguous-input `CallableBoxProduct` provide their own
initialized/restoring clients.

For a source-level continuation after a real gather, import
`Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec` and use
[`BoxProduct.exec_fromSnapshot`](../../Complexity/Algorithms/WordRAM/MatrixMultiplication/Schonhage/BoxProduct/Exec.lean).
It requires actual computed parameters, threshold, ordinary scalar header and protected-snapshot
readback. Low matrix/query words may be dirty; snapshot word zero is restored exactly.
Both raw unsigned and canonical signed matrix inputs use this same charged suffix:
`QueriedProduct.exec_routingFromSnapshot` routes occurrences,
`BoxProduct.exec_frontFromSnapshot` prepares matrices and bands, and `exec_fromSnapshot`
constructs geometry, evaluates tiles, reconstructs original occurrences and restores input.
The contiguous `BoxProduct.exec` establishes the snapshot by its actual original copy, then
uses the same suffix. The physical gather and native memory-window frames are proved in
`CallableBox.Pointer`; a canonical register view does not establish a memory frame.

When composing another proved record product with the existing verifier, use
`RecordWitness.exec_after_product` from `RecordWitness.AfterProduct`. Supply its actual
execution, actual output offset, exact signed matrix-product answers, outside-window memory
frame and all producer registers below 65, including ordinal register 64. The theorem invokes
`exec_consume` and retains its scan-dependent charge, original-coordinate witness and query
occurrence. The concrete original and box endpoints discharge this premise internally;
their public statements do not acquire a solver assumption. Keep their `19*m` and `21*m`
geometry, threshold instructions and admission proofs separate.

For a reused slot, use `RecordWitness.exec_after_record_product` from
`RecordWitness.AfterRecordProduct`, or the concrete box specialization
`BoxRecordWitness.exec_at_record` from `BoxRecordWitness.Record`. Supply the actual physical
descriptor, query span, matrix pair and protected original arrays. Its physical ordinal is
independent of the logical chunk/piece index; an all-record `Instances.Output` is neither
required nor asserted for that slot. `RecordWitness.exec_after_product` specializes this boundary
for standalone producer outputs.

The [pure readback client](../../ComplexityTests/WordRAMExactTriangleRecordReadback.lean)
checks duplicate occurrence order with dirty unused memory. The
[consumer client](../../ComplexityTests/WordRAMExactTriangleRecordWitness.lean) checks
success, failure, zero answers and repeated failed candidates. The standalone original
product and witness clients remain available alongside the box clients.

## Box-backed fixed-prime Exact Triangle

To decide whether three signed integer matrices contain a zero-weight triangle, import
`Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime` and use
`StreamingFixedPrime.runs_input`. The complete initialized client is
[the streaming test module](../../ComplexityTests/WordRAMExactTriangleStreamingFixedPrime.lean):
it discharges admission, recovers a successful witness, and checks negative exhaustion. The
[general-threshold client](../../ComplexityTests/WordRAMExactTriangleFixedPrimeInput.lean)
checks the same canonical solver at `m=2`, including prime-three false positives. `Instances`
provides an independent all-record producer, standalone record products and witness consumers are
available separately, and `FixedPrime` holds numerical and controller support.

Provide `3*n²` signed weights in row-major AB, BC, AC order, with every absolute value at most
`A`. `PreparationInput.input n (D m) g p values` supplies the scalar headers and canonical
signed encoding; `State.init` stores the input length at address 0, places these raw words at
successive addresses from 1, and zeroes the remaining memory. The
geometric premises are `D m = 4^m >= 16`, `(D m)^18 <= n`, `g >= 1` and
`p` in `Nat.sqrtPrimeWindow (D m)`. The physical width must satisfy
`FixedPrime.admissionWidth n (D m) g p A <= W`. If application fails, check the list length,
weight bound, prime-window inequalities and width against the complete client; the theorem
does not select an admissible prime or geometry for you.

The fixed 416-register streaming program computes the catalogue, then constructs the next
logical chunk/piece in one fixed slot. It runs the complete box product and original-weight
verifier at physical ordinal zero, consumes the answer immediately, and resets the heap by a
charged copy. Logical progress follows the original chunk-major/piece-major order and stops
at the first original witness. Original signed weights, queries and catalogue remain below
the slot; dirty solver scratch may be overwritten without clearing it. The same-state prefix
and charged halt return one exactly for an original zero triangle, with original coordinates.
The executed catalogue, construction, argument copies, guards, solver calls, reset and halt
are charged; original input placement is an initial-state convention.

For at least one logical record, the retained record region is `6+2*n*D` words instead of
`M*(6+2*n*D)`. With no records, the guard performs no construction. The existing solver reserve
was already reused; its size and the coarse admission/word/support bounds remain unchanged.
This is a smaller record region, with no claim of an asymptotic total-space improvement.

For `m=9k`, apply `FixedPrime.timeBound_le` to the derived genuine standalone reference returned by
`runs_input`. `StreamingFixedPrime.streamingCharge_le_timeBound` places every streaming charge,
including halt, within `FixedPrime.timeBound`; that reference is never asserted for a reused slot. Its complete finite bound retains preparation, aggregate box charges,
root/query/controller overhead and **one global** `F(p)+1` original-weight scan reserve.
The product term is `125829120(189k+1)^2(9k+1)D^(-8/125)n³g`; that saving alone is not an
unconditional total exponent. The zero-weight and constant-257 negative clients are checked
symbolic execution witnesses at admitted positive-threshold geometry, not interpreter runs
or benchmarks.

The automatic box-backed host and its ordinary 3SUM 1.9992 composition are described below.
The component theorem above retains its explicit geometry and selected-prime premises.

### Calling the box controller from another native program

Import `Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime`. For an initialized
call, use `CallableFixedPrime.runs_input` with the same `PreparationInput.input` layout and
geometry/prime premises above, and physical width at least
`CallableFixedPrime.inputWidth n (D m) g p values`. The complete
[initialized client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMCallableBoxFixedPrime.lean)
checks successful original-coordinate recovery, a same-execution finite charge and negative
exhaustion. Fourteen executed header/pointer instructions precede the actual caller program;
input placement itself follows the `State.init` convention above.

For an existing caller, `CallableFixedPrime.exec_at` accepts the original raw arguments in
registers 600–607: n, D, g, p, AB, BC, AC and workspace base. Put the canonical signed arrays below
that base; the three original spans may alias. Retain the same original-list, geometry and
prime premises. The physical address/window fit premise is
`Fits W (base + 4 * CallableFixedPrime.windowSize n (D m) g p (CallableFixedPrime.rawTotal n values) + 1024)`.
`exec_at` establishes semantic execution and frames without an initial whole-data bound;
use `exec` with `x.Bounded W`, or the original-admission prefix rules, for physical-word bounds.
Raw verdict, witness and scans return in 632–636.
The fixed 640-register program preserves the low 160 selector bank, all eight original argument
registers and memory outside its stated window. It copies and sums only the original arrays,
computes its own virtual width, and executes the real box controller in reused dirty memory.
The [dirty caller client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMCallableBoxFixedPrimeCaller.lean)
checks aliased spans, nonzero selector registers and dirty words above the virtual modulus.

At `m=9k`, `CallableFixedPrime.timeBound_le` charges the actual copy/setup/return and final
halt plus at most three times the complete box-controller ledger. Retain its preparation,
root/query/controller and global `F(p)+1` scan terms. This bound already includes the caller
halt; add 14 for the initialized header, as the checked client does. For every wider admitted
prefix, `bounded_reachable_input` gives polynomial words and zero support above the shared
original-input envelope. For arbitrary dirty callers, use `bounded_reachable_caller` with the
original raw-word bound: memory above the envelope is preserved and need not be zero.
`CallableFixedPrime.inputWidth_le_log` and `CallableFixedPrime.prefixBound_le_pow` supply the shared numerical
estimates for polynomial original weights and bounded scalar headers. These are symbolic
execution guarantees, not interpreter benchmarks. `ParameterSelecting.callee` computes its
geometry and selected prime and calls this actual controller. Its register names are
`ParameterSelecting.Reg`; parameter fields use `DyadicParameters.Reg`.

## Automatic native Exact Triangle solver

Import `Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting` and open
`Cslib.Algorithms.WordRAM.ExactTriangle`. Use `ParameterSelecting.runs_input_uniform` for a
complete initialized decision. The
[checked client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMParameterSelectingInput.lean)
gives full imports, admitted positive/negative signed cases, empty input, and a symbolic fast
family with the actual selected-prime conclusion. From a checkout containing this endpoint:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.WordRAMParameterSelectingInput
```

Supply `values : List ℤ` of length `3*n²`, in row-major AB, BC, AC order, and prove every
`z.natAbs <= F`. Initialize with `State.init (CountPrime.inputWords n F values)`: address 0
holds the input length, addresses 1 and 2 hold n and F, signed matrix words start at address 3,
and remaining memory is zero. F is an original magnitude bound, not a prime. The theorem
requires `ParameterSelecting.inputWidth n F values <= W`; it computes geometry, pointers,
workspace, the prime and the fast/small dispatch itself. If application fails, check the exact
list length, canonical signed encoding, magnitude bound and width against the linked client.

The fixed 640-register program returns a raw Boolean in `ParameterSelecting.Reg.result`,
exactly one iff the original matrices contain a zero triangle. The initialized prefix and
halt share one final state, original arguments 0–5 are restored, and the stated original-array
and outside-workspace frames are retained. Zero vertices, F=0 and the entire small regime
are included. Input placement is the initial-state convention; the executed 15-instruction
header, parameter computation, actual minimum-count prime selection, solver/control and final
halt are charged. The uniform initialized bound is `ParameterSelecting.callerTime n F`,
already including the header and halt reserve of 16.
Its fast body allowance retains all three component budgets plus 26; the small allowance
uses actual exhaustive code. No supplied solver, run, prime, layout or time law is required.

For an existing ordinary host, `ParameterSelecting.callee` supplies `ThreeSum.Host.Callee 633`:
633 scratch registers give 640 total, arguments 0–5 are restored and Boolean 6 is returned.
Its semantic execution permits arbitrary unused old words. Caller prefix-resource rules
separately require their original raw-word bound; arbitrary old memory is not asserted zero.
For initialized polynomial magnitudes `F <= (n+2)^κ`, `inputWidth_le_log` gives width at most
`(12332*(κ+9)+40)*clog₂(n+2)`, and `bounded_reachable_polynomial` bounds every admitted wider
prefix's words and zero support by `(n+2)^(12332*(κ+9)+41)`.

This canonical automatic solver calls the fixed-prime controller above. Its complete time is
`Oκ(n^(3-33/20000))` at polynomial original magnitudes. It supplies both ordinary 3SUM bounds
below. Time counts standard unit instructions on signed integer matrices; this is not bit-time
or an arbitrary-real theorem. The large-family client is a checked symbolic run, not an
enormous interpreter benchmark.

## Conservative ordinary integer 3SUM

Import `Complexity.Algorithms.WordRAM.ThreeSum.Decision.Subquadratic`. In namespace
`Cslib.Algorithms.WordRAM.ThreeSum.Decision`, apply `exists_subquadratic_runs κ` to the actual
ordinary host with `ParameterSelecting.callee`. The complete
[checked client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMSubquadraticThreeSum.lean)
includes imports, positive repeated-zero inputs, negative all-one/all-minus-one inputs, and
rejection of two zeros because the positions must be distinct. From an endpoint checkout:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.WordRAMSubquadraticThreeSum
```

Fix a natural magnitude exponent `κ`. For `input : List ℤ` of length n, prove each
`|z| <= (n+2)^κ` and supply `Decision.width κ 123357 n <= W`. The starting state is
`State.init (input.map Signed.encode)`: address 0 holds n, signed input words start at 1,
and remaining memory is zero. If application fails, check the signed encoding, original list
length, magnitude bound, width and import against the complete client.

One fixed 848-register standard Word-RAM program per κ returns one exactly for a zero sum at
three distinct original positions; repeated values are allowed. Correctness holds at every
length and every admitted wider width. The actual halt and prehalt prefix share a final state.
For each κ, one positive C and threshold N precede all inputs and physical widths; for n >= N,
charged steps are at most `C*n^(2-1/5184)`. Actual preprocessing, parameters, prime selection,
matrix construction, solver calls, control and halt are included in `Decision.cost`. No solver,
prime, layout, run or time law is supplied. Initial input placement/output extraction follow
the model convention. These clients consume checked run theorems; they are not VM benchmarks.

Every reachable prefix has register/memory words below
`(n+2)^(2*Decision.widthCoefficient κ 123357)` and memory zero at or above that address envelope;
final data also satisfy the physical width bound. Time counts standard unit instructions,
including multiplication, division, bitwise operations and shifts, with overflow faults.
This is polynomially bounded integer Word-RAM time, not bit/Turing time or arbitrary-real
3SUM. This conservative exponent is a weaker bound on the same canonical tuned pipeline used
by the 1.9992 theorem below; there is no separate conservative solver implementation.

## Ordinary integer 3SUM in time n^1.9992

Import `Complexity.Algorithms.WordRAM.ThreeSum.Decision.One9992`. In namespace
`Cslib.Algorithms.WordRAM.ThreeSum.Decision`, apply `uniformDecidableInO_one9992 κ` for the
compact complexity statement in the existing Word-RAM time API. `Admissible κ input W`
bundles the magnitude and width conditions below; `Admissible.inputFits` proves that every
admitted pair meets the API's separate input-fit requirement.
The natural-valued time scale is the ceiling of `n^(2499/1250)`; this ceiling is proof
metadata and is not evaluated by the machine.

For a particular program, `boxProgram κ` is computable structured code and `boxFlatProgram κ`
is its assembled standard Word-RAM program with 848 registers.
`boxFlatProgram_decidesInTime κ` gives its exact `Decision.cost` allowance at every length.
Use `exists_one9992_runs κ` when you also need the final native state, same-state prehalt
prefix or polynomial bounds on every prefix. None of these interfaces asks for a solver,
time law, selected prime or layout certificate. The complete
[checked client](../../ComplexityTests/ThreeSumOne9992.lean)
shows the semantic interfaces, positive and negative inputs, repeated values at distinct
positions, rejection of an inadmissible magnitude, the charged halt and the same-state
prehalt prefix. The [native visitor client](../../ComplexityTests/NativeChanHeVisitor.lean)
checks actual node calls, skipped descriptors and resumption with dirty solver scratch.
From a checkout containing this visitor, run:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.ThreeSumOne9992   ComplexityTests.NativeThreeSumDecision ComplexityTests.NativeChanHeVisitor
```

The native constructor `Decision.program κ solver` accepts only the finite callee code;
`Decision.flatProgram` assembles its halt. The canonical solver argument is
`ParameterSelecting.program`. Correctness and time certificates refer to that same syntax,
so evaluating it does not require evaluating proof-only resource metadata. There is no
separate `Decision.Code` import or duplicate `programOfCode` assembly.

The canonical controller constructs each actual Chan–He node and immediately passes its
packed block to the Convolution host before pushing its children. Calls follow the exact
finite preorder and multiplicity. Boolean accumulation continues after a positive result;
zero-fuel and empty-column descriptors take their actual skip paths without a solver call.
The ordinary path publishes no packed-pointer table and performs no later table readback.

For an independently useful complete catalogue, import
`Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing` for initialized execution,
readback, width and resources. Its `PreprocessingExecute` companion supplies
`Preprocessing.afterFrontend_exec` after the frontend, in namespace
`Cslib.Algorithms.WordRAM.ThreeSum.ChanHe`. This standalone producer remains separate from
the ordinary visitor. Ordinary clients use `Decision.exec_input` or `Decision.runs_input`;
they need no snapshot, cursor or individual-stage contracts. The lower-level
[`Decision.exec_large`](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/Execute.lean)
also requires `x.Bounded W` for its complete starting register file. The initialized endpoint
derives that premise from `Data.init` and its actual saved-header prefix.

Choose a fixed natural magnitude exponent `κ` and an original `input : List ℤ`. Set
`n = input.length`, prove every `|z| <= (n+2)^κ`, and supply physical width
`Decision.width κ 123357 n <= W`. The initial state is
`State.init (input.map Signed.encode)`: address 0 holds the length, canonical signed words
start at address 1, and the remaining memory is zero. If application fails, check this
encoding, list length, magnitude premise, width and imported source revision against the
client. Input placement is the initial-state convention; it does not charge a whole-envelope
clearing pass.

For each `κ`, the theorem chooses one positive constant `C` and threshold `N` before all
inputs and physical widths. Correctness holds at every length: the actual halt returns one
exactly when three distinct input positions sum to zero; equal values at different positions
are allowed. The same execution has a charged natural step count, at most the concrete host
cost, and for `n >= N` at most `C * n^(2499/1250)`, where `2499/1250 = 1.9992`. Every admitted
wider width has the same guarantees. Every reachable prefix has register and memory words
below `(n+2)^(2 * Decision.widthCoefficient κ 123357)` and memory zero at addresses at least
that envelope; the final data also satisfy the physical word bound.

At each reached node, executed argument copies deliver the actual packed pointer, common
length and current allocation endpoint `H` to the Convolution host. Its matrix workspace starts
at that current endpoint, as proved by
[`Visitor.exec_consume`](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/VisitorCall.lean).
The return frame preserves every cell below `H`, including the current packed block, pending
heavy arrays, native stack and frontend descriptors. Arbitrary higher scratch may be dirty
and can be reused. The polynomial value envelope bounds signed values and arithmetic width;
it does not supply a workspace address.

The proof composition keeps the original construction-state emission and the actual call's
register/prefix frames. It transports only the live child and pending-source views needed for
the next iteration. Root initialization is shared with the standalone catalogue producer through
[`Traversal.initializeRoot_exec`](../../Complexity/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalInitialize.lean).

The prefix frame is a return-state guarantee, not a ban on transient callee writes.
After consuming the node, one actual copy sets the committed heap to its packed pointer.
[`VisitorRelease`](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/VisitorRelease.lean)
proves that all heavy children and pending ancestor columns end below that released frontier.
The packed block, residue workspace and histogram tail can be overwritten by later construction;
the copy itself changes no memory cells. Persistent heavy-buffer allocation remains monotone,
and the old table gap stays reserved.

The actual
[`Visitor.live_transition`](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/VisitorTransition.lean)
postcondition gives final committed heap equal to the body's initial heap plus
`3 + len(column0) + len(column1) + len(column2)`; skipped bodies leave it unchanged.
The three count cells and full heavy-buffer capacities remain allocated. The discarded tail
has `len(column0)+len(column1)+len(column2)+4*N+M` words, where `N` is the common group count
and `M` is this node's selected modulus. These are native body storage equalities, not a bound
on arbitrary callee scratch or touched high-water memory. The existing polynomial word/support
envelope remains unchanged; no improved total-space bound is claimed.

The [native fixture source](../../ComplexityTests/NativeChanHeVisitor.lean) includes an initial
heap of 100 with expected final frontiers 106 for one live node and 115 for the two-node
branching case. It also overwrites a released packed cell after the actual child pushes and
checks an empty heavy column whose pointer equals the frontier. The build command above checks
these local cases alongside the endpoint clients; they are not asymptotic-space measurements.

The [actual automatic callee](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ExactTriangle/ParameterSelecting/Callee.lean)
executes parameter computation, prime selection and the real box-backed calls. Its integer
parameters and the reason for their constants are explained below; the parameter `n` there
is the ET dimension, rather than the original 3SUM length.
The [parameter boundary client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMExactTriangleDyadicParameters.lean)
checks the actual VM at zero, below `2^2394` and at `2^2394`;
the [automatic Exact Triangle client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMParameterSelectingInput.lean)
checks symbolic fast-family executions, including the selected-prime conclusion. These huge
matrix clients are proof witnesses, not execution benchmarks. Small ordinary-input VM checks
also reject lengths below three. The complete finite ledger charges preprocessing, selector,
global original-weight scan reserve, matrix preparation, every box call, outer control and
halt. Polynomial logarithmic factors are absorbed before the ordinary reduction is applied.

The intermediate native Exact Triangle bound is `Oκ(n^(3-33/20000)) = Oκ(n^2.99835)`;
this does not claim the source Exact Triangle exponent 2.9983. The final
[ordinary theorem and source mapping](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ThreeSum/Decision/One9992.lean)
adapt the 1.9992 target to this library's standard unsigned Word-RAM with canonical signed
encoding and polynomially bounded integers. Time counts unit native instructions with
logarithmic admitted word width. This is not a bit-time or arbitrary-real 3SUM theorem;
the source's separate signed modular machine and `SolvedInTime` predicate are not imported.

## Following and reusing the runtime bound

The exponent comes from the dimension of each ET call and the number of charged calls.
For original 3SUM length `n`, write `ell = floor(log2(n+2))+1`,
`q = Decision.instanceBound κ n` and `s = Host.sideLength (Decision.instanceLength κ n)`.
The fixed magnitude exponent `κ` may affect constants. The finite account is:

| Quantity | Bound before absorbing logarithms | Checked statement |
|---|---|---|
| Preparation/traversal allowance `Pκ(n)` | `Kκ*(n+2)*(sqrt(n+2)+1)*ell^13` | `Preprocessing.cost_bound` |
| Emitted-node allowance `q` | `128*(κ+2)^2*ell^7` | `Decision.instanceBound_le_numBound` |
| ET side `s` | `Oκ(sqrt(n)*ell^2)` | `ChanHe.packed_side_le` |
| One Convolution-call allowance, including outer control | `2*s*T(s,F)+355*s^3` | `Decision.callerTime_add_twelve_le` |

The [runtime module](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/Runtime.lean)
connects these statements to the actual `Decision.cost`:
`Pκ(n) + 4*E + 32 + q*(Host.callerTime(...)+12)`, where
`E = Decision.envelopeExponent κ`. The fixed reserve includes setup and halt; the caller
term includes matrix construction and every ET invocation. The passed magnitude is
`F = 2*(n+2)^E+1`. `ChanHe.packed_weight_le` bounds it by `(s+2)^(2*E+2)`, so an ET theorem
for polynomial weights applies at the actual side `s`.

The Convolution consumer alone costs `Host.callerTime(...)+7`. The one-copy packed-tail
release makes the traversal's callback-and-release charge `Host.callerTime(...)+8`.
[`Visitor.cost_ledger`](../../Complexity/Algorithms/WordRAM/ThreeSum/Decision/VisitorCost.lean)
proves that the fused initialized budget plus `18+4*emitted` equals the reused budget with
`emitted` call allowances. The finite node-count theorem gives `emitted <= q`, so the visitor
fits the existing `Decision.cost`. Every skipped descriptor is charged as traversal work;
only emitted nodes incur solver charges. This is an identity of proved instruction budgets,
not a measured runtime or a completed execution of the standalone catalogue producer.

The native forest pays these different live/skip costs with an explicit ghost potential:
remaining traversal work plus solver charges for the exact remaining emitted nodes. The
[variable-cost native loop guide](memory-specifications.md#pay-variable-native-loop-work-with-a-ghost-potential)
explains the generic `ExecWithin.loop_potential_state` rule and its complete checked client.

If `T(s,F) = O(s^(3-δ))`, the solver term becomes `O(q*s^(4-δ))`.
Substitution produces the power `n^(2-δ/2)` with a fixed logarithmic factor.
Only then does the proof absorb logarithms: it establishes every
`a > 2-δ/2`, for `0 < δ <= 1`. It does not establish the boundary exponent with those
factors removed. This also explains why the entire preprocessing cost must be retained.

For a different actual certified ET implementation, import
`Complexity.Algorithms.WordRAM.ThreeSum.Decision.Runtime`. In the `Decision` namespace,
`exists_cost_bound` takes a concrete `Host.Callee r`, `0 < δ <= 1`, a target exponent
`a > 2-δ/2`, and its proved uniform polynomial-weight time bound `Oκ(n^(3-δ))`.
It derives the full ordinary `Decision.cost` bound `Oκ(n^a)`, retaining native preprocessing,
actual packed dimensions and emitted-node counts, matrix/callee calls, control and halt. The
constant and threshold precede all original inputs and admitted physical widths.

Import `Complexity.Algorithms.WordRAM.ThreeSum.Decision.Transfer` for
`exists_runs_of_callee_time`, which adds the complete initialized execution, distinct-position
verdict, same-state prefix/halt and every-wide polynomial word/support guarantees. These generic
modules import no particular ET supplier. Their quantitative premise must be proved for actual
code; it is not an execution or time oracle for the final algorithm. For ordinary use of the
canonical implementation, apply `exists_one9992_runs` directly and supply only the original
input magnitude and physical-width premises described above.

The canonical callee uses `δ = 33/20000`. Both `a = 2499/1250` and the older conservative target
`a = 2-1/5184` satisfy the strict inequality, so both endpoint proofs reuse this same transfer
and concrete solver. The [ordinary client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/ThreeSumOne9992.lean)
and [conservative client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMSubquadraticThreeSum.lean)
check the resulting concrete run/resource contracts. From a checkout containing this revision:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.ThreeSumOne9992 ComplexityTests.WordRAMSubquadraticThreeSum
```

The finite reductions and box mathematics retain their Alman–Williams/Anthropic source credit;
the integer parameter tuning, shared native representation and cost composition are original
native adaptations. The generic transfer changes proof reuse, not the computational model or
the 1.9992 theorem's scope.

### Why these integer parameters work

Here `n` denotes the ET dimension. The parameters put all components on the common scale
`n^3/g`. Read the feasibility and balance conditions before the chosen values:

| Condition | What it pays for |
|---|---|
| `D^18 <= n` | Box-backend geometry |
| `D*g^2 <= n` | Preparation `n^2*D*g <= n^3/g` |
| `g^2 <= sqrt(D)` | Query control |
| `g^2 <= D^(8/125)` | Product work `n^3*g*D^(-8/125) <= n^3/g` |

The [parameter family](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/ExactTriangle/ParameterChoice.lean)
chooses `g=4^(2b)`, `m=63b`, `D=4^m`, and the existing box tensor depth `L=21m`.
The product balance is the small integer inequality `4*125 <= 63*8`, or `500 <= 504`;
`63b` also satisfies the box tradeoff's divisibility by nine.
The stronger reserve `D^19 <= n` requires `2394*b <= floor(log2(n))`, because
`2394 = 2*63*19`. This gives `b=floor(log2(n)/2394)`.
The [cost-geometry lemmas](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/ExactTriangle/ParameterChoice/CostGeometry.lean)
prove the conditions and `n^3/g <= 16*n^(3-2/1197)`, retaining integer rounding.

The raw saving `2/1197` is not yet a full runtime exponent. The
[finite coefficient](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ExactTriangle/DyadicCost/Asymptotics.lean)
retains the product factor `(21m+1)^2*(m+1)`, a linear logarithmic parameter term and the
global selected-prime scan term proportional to the weight exponent times `log(n)`.
It is bounded by a constant times `(floor(log2(n))+1)^3`. Absorbing this full coefficient,
and charging callable setup and dispatch, gives the ET saving `δ=33/20000`.
The ordinary transfer then allows any exponent above `2-δ/2`, which is 1.999175;
the target 1.9992 leaves a further gap of `1/40000` for its logarithmic factors.

`ParameterChoice.blocks_pos_iff` proves the exact ET fast cutoff `n >= 2^2394`.
The executable selector chooses exhaustive solving below it. This cutoff follows from
the proved integer family; it is not a measured crossover, an optimized cutoff, or a claim
about practical performance. The asymptotic threshold can be larger still, and the
existential false-positive constant in the proof does not supply a numerical benchmark.

## Greedy weighted set cover

Import `Complexity.Algorithms.Lean.SetCover.Greedy` ([Complexity/Algorithms/Lean/SetCover/Greedy.lean](../../Complexity/Algorithms/Lean/SetCover/Greedy.lean)). Unlike the endpoints above, this is a pure Lean function analyzed for solution quality, not a machine program with a step bound. `greedy S w J U` takes a ground set `U : Finset α`, sets `S : ι → Finset α`, weights `w : ι → 𝕜` in a linearly ordered field and a candidate list `J`. Each round it picks a candidate minimizing `w j / |S j ∩ R|` over the uncovered elements `R`, with ties going to the earliest candidate in `J`. It stops when no candidate meets `R` and returns the chosen candidates in order.

- **Feasibility:** `greedy_covers` needs every element of `U` to lie in some candidate set; `ComplexityTests/SetCoverGreedy.lean` shows the loop stopping with an incomplete cover when that fails. `nodup_greedy` and `length_greedy_le` bound the output by `U.card` distinct candidates.
- **Ratio, stated against any cover:** `sum_greedy_le_harmonic_mul` proves `cost ≤ H d · w(C)` for every cover `C` drawn from `J` whose sets meet `U` in at most `d` elements, given nonnegative candidate weights. Instantiating `C` with an optimal cover gives Chvátal's `H d` ratio. `sum_greedy_le_harmonic_card_mul` takes `d = |U|`, and `sum_greedy_le_one_add_log_mul` gives `(1 + log d) · w(C)` over `ℝ`.
- **Fractional form:** `sum_greedy_le_harmonic_mul_fractional` compares with every nonnegative fractional cover `x` instead. This is Theorem 1.12 of [Williamson and Shmoys][williamsonshmoys11] stated without the linear-programming API: the dual-fitting step and weak duality are merged into one inequality, and the caller supplies the fractional cover. Instantiating it with an LP optimum would go through the [duality theorems below](#linear-programming-duality-over-ordered-fields); no set-cover LP is stated yet.

The [checked examples](../../ComplexityTests/SetCoverGreedy.lean) include an instance where greedy pays `11/6` against an optimum of `11/10`, inside the bound `121/60`. They also show a fractional cover strictly cheaper than every integral cover. Machine-level running time is open ([ROADMAP](../../ROADMAP.md#combinatorial-optimization)).

## Greedy submodular maximization over matroids and `p`-systems

Import `Complexity.Algorithms.Lean.Submodular.MatroidGreedy` ([source](../../Complexity/Algorithms/Lean/Submodular/MatroidGreedy.lean)) for the algorithm and its guarantees, and `Complexity.Algorithms.Lean.Query.Submodular.MatroidGreedy` ([source](../../Complexity/Algorithms/Lean/Query/Submodular/MatroidGreedy.lean)) for the oracle program. Like greedy set cover, this is analyzed for solution quality and query counts, not for machine running time. `submodularMatroidGreedy f indep xs` takes a value function `f : Finset α → β`, an independence test `indep : Finset α → Bool` and a ground list `xs`. Starting from `∅`, each round adds an element `c ∉ S` of `xs` with `indep (insert c S)` that maximizes `f (insert c S)`, with ties going to the earliest element of `xs`. It stops when no element can be added. This is the greedy algorithm of [Fisher, Nemhauser and Wolsey][fnw78], as described in [Călinescu et al.][ccpv11].

- **Constraint families:** `IsPSystem indep p` in [Complexity/Algorithms/Lean/Matroid/PSystem.lean](../../Complexity/Algorithms/Lean/Matroid/PSystem.lean) asks that `∅` is independent, that independence is inherited by subsets, and that any two maximal independent subsets `A, B` of a finite set satisfy `|A| ≤ p * |B|` ([Călinescu et al.][ccpv11], Section 1). `isPSystem_matroid` shows that every Mathlib `Matroid` is a `1`-system on finite sets, and `isPSystem_iInter_matroid` that the intersection of `k ≥ 1` matroids is a `k`-system. The analysis uses the blocking form `IsPSystem.card_le_mul_card_of_blocked`: if every element of an independent `T` outside an independent `S` is blocked by `S`, then `|T| ≤ p * |S|`.
- **Feasibility:** `indep_submodularMatroidGreedy` (the output is independent whenever `∅` is) and `not_indep_insert_submodularMatroidGreedy` (no element of `xs` can be added). Under a matroid oracle, `submodularMatroidGreedy_isBasis'` makes the output a basis of the ground list.
- **Ratio, stated against any independent set:** for monotone submodular `f`, a `p`-system `indep` and any independent `O ⊆ xs.toFinset`, `add_nsmul_le_succ_nsmul_submodularMatroidGreedy` proves `f O + p • f ∅ ≤ (p + 1) • f G` in any linearly ordered additive group. Over an ordered field with `0 ≤ f ∅`, `div_succ_le_submodularMatroidGreedy` gives `f O / (p + 1) ≤ f G`. Specializations: `half_le_submodularMatroidGreedy_of_matroid` (`1/2` for a matroid) and `div_card_succ_le_submodularMatroidGreedy_of_iInter_matroid` (`1/(k+1)` for `k` matroids). Nonnegativity of `f` is not assumed in the group form; it is replaced by the `f ∅` terms. The proof charges each element of `O` to the greedy rounds in which it was still feasible, and the blocking bound limits how many elements of `O` can stop being feasible early. This is a different bookkeeping from the explicit partition of `O` in [Călinescu et al.][ccpv11], Appendix B.
- **Modular objectives:** for nonnegative weights `w`, `sum_le_nsmul_sum_submodularMatroidGreedy` gives `∑ O w ≤ p • ∑ G w`, the `1/p` bound that [Călinescu et al.][ccpv11] attribute to Jenkyns, and `sum_le_sum_submodularMatroidGreedy_of_matroid` gives optimality over a matroid.
- **Tightness:** `exists_tight_submodularMatroidGreedy` gives a coverage objective and a partition matroid on three elements on which the greedy value is exactly half the value of an independent set.
- **Queries:** `submodularMatroidGreedyQuery xs` runs the same algorithm in `FreeM (SumQuery (ValueQuery α β) (IndepQuery α))`. `SumQuery` ([source](../../Complexity/Algorithms/Lean/Query/SumQuery.lean)) charges value queries (`countInl`) and independence queries (`countInr`) separately. These counts describe this implementation, which re-tests every remaining element in each round; they are not claimed optimal. With `n` distinct ground elements and output `G`, `countInr_submodularMatroidGreedyQuery` gives exactly `∑ t ∈ range (|G| + 1), (n - t)` independence queries, and under a matroid oracle `|G|` is the rank of the ground list (`countInr_submodularMatroidGreedyQuery_of_isBasis'`). `countInl_submodularMatroidGreedyQuery` counts one value query per feasible candidate in each round, which is never more than the independence count. Each count is at most `n (n + 1) / 2`, and `submodularMatroidGreedyQuery_upperBound` bounds the total by `m (m + 1)` for ground lists of length at most `m`. `half_le_eval_submodularMatroidGreedyQuery` restates the `1/2` bound for the query program under `IndepQuery.ImplementsMatroid`.

The [checked examples](../../ComplexityTests/SubmodularMatroidGreedy.lean) run the tight instance, where greedy makes `6` independence and `4` value queries, also on a ground list with repeated elements. They also show that matchings of a three-edge path form a `2`-system (as the intersection of two partition matroids) but not a matroid, and that greedy gets exactly half of the maximum modular weight there, so the `1/p` bound is attained at `p = 2`. The continuous greedy with pipage rounding (`1 - 1/e` over a matroid), knapsack constraints and non-monotone objectives remain open ([ROADMAP](../../ROADMAP.md#combinatorial-optimization)).

## Vertex cover and metric TSP 2-approximations

Two more classical approximation algorithms are stated as plain inequalities against the optimum.

- **Vertex cover from a maximal matching.** Import `Complexity.Computability.Complexity.Problems.VertexCover.Approximation` ([source](../../Complexity/Computability/Complexity/Problems/VertexCover/Approximation.lean)); the generic algorithm is in `Complexity/Algorithms/Lean/VertexCover/Matching.lean`. `matchingCover es` scans an edge list once, keeps every edge with distinct endpoints that are both still unmatched, and returns their endpoints. This is `APPROX-VERTEX-COVER` of [Cormen et al., Section 35.1][clrs09] with "an arbitrary remaining edge" read as "the first one in list order". `isVertexCover_matchingCover` proves feasibility, and `length_matchingCover_le_two_mul_vertexCoverNum` bounds the size by twice Mathlib's `vertexCoverNum`. The matching lower bound `length_le_encard_of_isVertexCover` is stated for any vertex cover. On the library's `Graph` encoding, `approxCover G` runs on the edges between declared vertices: `approxCover_mem_VertexCover` and `length_approxCover_le_two_mul_vertexCoverNum` compare it with `VertexCover` and `Graph.vertexCoverNum`, and `computableInPolyTime_approxCover` is a plain `ComputableInPolyTime` certificate from `encGraph`.
- **Metric TSP through a minimum spanning tree.** Import `Complexity.Computability.Complexity.Problems.TSP.Approximation` ([source](../../Complexity/Computability/Complexity/Problems/TSP/Approximation.lean)); the generic algorithm is in `Complexity/Algorithms/Lean/TSP/MSTTour.lean`. `mstTour δ` computes Kruskal's minimum spanning tree of the complete graph on `Fin n` and grows a tour from vertex `0`: while some tree edge has exactly one endpoint on the tour, it inserts the other endpoint right after that one. `totalWeight_kruskalEdges_le_cycleCost` is Lemma 2.10 of [Williamson and Shmoys][williamsonshmoys11] (the tree costs at most any tour). `cycleCost_insertAfter_le` is the insertion step of their Theorem 2.11, which they prove for the nearest-addition algorithm on Prim's tree; here it is applied to Kruskal's tree. Together they give `cycleCost_mstTour_le_two_mul`. On `TSP` instances, `TSP.approxTour D` visits every city exactly once (`approxTour_perm`), and when `TSP.IsMetric D` holds, `tourLength_approxTour_le_two_mul` bounds its length by twice every tour's. `IsMetric` asks only for symmetry and the triangle inequality among cities. The triangle inequality covers all triples, including `i = k`, so each diagonal entry is at most twice any distance from its city; diagonal entries need not be zero (Williamson and Shmoys assume they are).

The [vertex-cover examples](../../ComplexityTests/VertexCoverApproximation.lean) pin the optimum of a path and a star exactly, so the factor `2` is attained. The [TSP examples](../../ComplexityTests/TSPApproximation.lean) include a matrix violating the triangle inequality where the tour costs `202` against a tour of cost `4`, so the metric hypothesis cannot be dropped. Concrete TSP runs first pin the sorted edge list with `simp [sortEdges_cons_cons]`, because `List.mergeSort` does not reduce in the kernel. No machine running time is certified for the TSP tour yet; that needs a polynomial-time certificate for Kruskal's algorithm on encoded matrices.

## Metric k-center: Gonzalez's 2-approximation and the dominating-set gap

Import `Complexity.Algorithms.Lean.KCenter.Gonzalez` ([source](../../Complexity/Algorithms/Lean/KCenter/Gonzalez.lean)) and `Complexity.Algorithms.Lean.KCenter.DominatingSet` ([source](../../Complexity/Algorithms/Lean/KCenter/DominatingSet.lean)). Like the set-cover and TSP algorithms above, these are pure Lean functions analyzed for solution quality, with no running time. A distance is any `d : V → V → α` into a linear order. The definitions are in [KCenter/Basic.lean](../../Complexity/Algorithms/Lean/KCenter/Basic.lean): `centerDist d S v : WithTop α` is the distance from `v` to its nearest center in `S` (`⊤` when `S` is empty), `radius d S` is the largest such distance over a finite nonempty `V`, and `optRadius d k` is the least radius of a center set with at most `k` points. This is the k-center problem of Section 2.2 of [Williamson and Shmoys][williamsonshmoys11].

- **Gonzalez's algorithm.** `gonzalez d P k` is Algorithm 2.1 of Williamson and Shmoys, which their chapter notes attribute to Gonzalez (1985). Over a candidate list `P` it runs `k` rounds of `farthestStep`. Each round appends the first point of `P` maximizing `centerDist` to the centers chosen so far (`List.argmax`), so the first center is the head of `P`. `length_gonzalez` gives exactly `k` centers when `P` is nonempty. `nodup_gonzalez` makes them distinct when `d` vanishes exactly on the diagonal and `P` has at least `k` distinct points.
- **The ratio.** `radius_gonzalez_le_two_mul` is Theorem 2.3: if `d` is symmetric and satisfies the triangle inequality, `P` lists every point and `optRadius d k ≤ r`, the radius is at most `2 * r`. The bound is stated against every upper bound `r` on the optimum, which avoids multiplication in `WithTop α`; `radius_gonzalez_le_two_mul_optRadius` specializes it to the finite optimum when `k ≥ 1`. Unlike Williamson and Shmoys, it does not assume `d i i = 0`. The proof is a packing argument instead of their cluster argument. If a point were farther than `2r` from every center, then the centers and that point would be `k + 1` points pairwise farther than `2r` apart (`IsFarthestFirst.pairwise_lt`). `length_le_card_of_pairwise_lt` shows that `k` centers covering within `r` cannot cover such points. The analysis holds for every farthest-first traversal (`IsFarthestFirst`), whatever its first point or tie-breaking. `centerDist_gonzalez_le_two_mul` also allows the competing centers to lie outside `P`.
- **The gap behind Theorem 2.4.** `domDist G` gives a simple graph the metric with `0` on the diagonal, `1` on edges and `2` elsewhere. `radius_domDist_le_one_iff` shows that a center set has radius at most `1` exactly when it is a `SimpleGraph.IsDominatingSet` ([Complexity/Foundations/Combinatorics/SimpleGraph/DominatingSet.lean](../../Complexity/Foundations/Combinatorics/SimpleGraph/DominatingSet.lean)). `optRadius_domDist_le_one_iff` and `optRadius_domDist_eq_two` then give an optimum of `1` or `2`, depending on whether a dominating set of at most `k` vertices exists. `isDominatingSet_of_radius_le_mul` and `exists_isDominatingSet_iff_of_radius_le_mul` show that a `ρ`-approximate solution with `ρ < 2` and at most `k` centers is dominating exactly when such a set exists, so it decides dominating set. Williamson and Shmoys attribute the hardness to Hsu and Nemhauser (1979). NP-hardness of dominating set on the library's encoded graphs is `DominatingSet_npComplete` (import `Complexity.Computability.Complexity.Problems.DominatingSet`, [source](../../Complexity/Computability/Complexity/Problems/DominatingSet.lean)). It uses a reduction from `VertexCover` that sends `(G, k)` to a graph with a hub, a pendant, a copy of every vertex and a vertex for every edge, and the target `k + 1` (`0` when `k` exceeds the number of distinct vertices). The statement that a polynomial-time `(2 - ε)`-approximation implies `P = NP` still needs a polynomial-time certificate for the map from graphs to distance matrices, and it is not formalized.

The [k-center examples](../../ComplexityTests/KCenter.lean) run Gonzalez on three points of a line at `0, 1, 2` with one center. It picks the endpoint and has radius `2`, while the middle point has radius `1`, so the factor `2` is attained. The same tight instance appears on the path `0 - 1 - 2` with `domDist`, where Gonzalez's center does not dominate, so the gap needs `ρ < 2`. A symmetric distance violating the triangle inequality makes Gonzalez pay `100` against an optimum of `1`. A distance vanishing between distinct points makes it repeat a center. The Hochbaum–Shmoys threshold algorithm, k-supplier and k-median are open ([ROADMAP](../../ROADMAP.md#combinatorial-optimization)).

## Linear-programming duality over ordered fields

Import `Complexity.Foundations.LinearAlgebra.Matrix.LinearProgramming` ([LinearProgramming.lean](../../Complexity/Foundations/LinearAlgebra/Matrix/LinearProgramming.lean)). This is mathematics with no machine model or running time. For a matrix `A : Matrix ι κ K` over any linearly ordered field `K` (so `ℚ` is included), the primal program maximizes `c ⬝ᵥ x` subject to `A *ᵥ x ≤ b` and the dual minimizes `y ⬝ᵥ b` subject to `0 ≤ y` and `y ᵥ* A = c`. Programs are plain matrix data; there is no bundled LP structure and no encoding.

- **Fourier–Motzkin elimination:** `Matrix.FourierMotzkin.exists_projection` ([FourierMotzkin.lean](../../Complexity/Foundations/LinearAlgebra/Matrix/FourierMotzkin.lean)) eliminates a finite block of variables `y` from `A *ᵥ y + B *ᵥ z ≤ b`. It returns an entrywise nonnegative `T` with `T * A = 0` and the same solvability in `z`. One step is `exists_smul_add_le_iff`.
- **Farkas' lemma:** `Matrix.not_exists_mulVec_le_iff` ([Farkas.lean](../../Complexity/Foundations/LinearAlgebra/Matrix/Farkas.lean)) shows that `A *ᵥ x ≤ b` is infeasible iff some `y ≥ 0` has `y ᵥ* A = 0` and `y ⬝ᵥ b < 0`. `exists_nonneg_mulVec_eq_iff` is the equality form with `x ≥ 0`. Mathlib's `ProperCone.hyperplane_separation` covers only closed cones in real locally convex spaces.
- **Duality:** weak duality is `dotProduct_le_dotProduct_of_mulVec_le`. Strong duality, `exists_isGreatest_isLeast_dotProduct`, says that when both programs are feasible both optima are attained and equal. `bddAbove_image_dotProduct_iff` and `bddBelow_image_dotProduct_iff` give the unbounded outcomes: a feasible program is bounded iff the other program is feasible. `exists_isGreatest_of_bddAbove` gives attainment, `dotProduct_eq_dotProduct_iff_of_mulVec_le` complementary slackness, and `exists_dual_le_of_forall_le` the affine Farkas lemma. `exists_isGreatest_isLeast_dotProduct_of_nonneg` covers the canonical pair `max {c ⬝ᵥ x | A *ᵥ x ≤ b, 0 ≤ x}` and `min {y ⬝ᵥ b | c ≤ y ᵥ* A, 0 ≤ y}`.

The [checked examples](../../ComplexityTests/Foundations/LinearAlgebra/Matrix/LinearProgramming.lean) give an infeasible system with its certificate, a feasible system with no certificate, an empty system, programs with values `3` and `22 / 5`, and an unbounded program with infeasible dual. Not formalized: bit-size bounds on solutions and certificates, membership of rational LP feasibility in NP ∩ coNP, and any polynomial-time LP algorithm ([ROADMAP](../../ROADMAP.md#optimization-and-duality)).

## LLL-reduced bases and lattice basis reduction

Import `Complexity.Algorithms.LatticeReduction.Potential` ([Reduced.lean](../../Complexity/Algorithms/LatticeReduction/Reduced.lean), [Potential.lean](../../Complexity/Algorithms/LatticeReduction/Potential.lean)). This is mathematics with no machine model or running time, following [Lenstra, Lenstra and Lovász, §1][lll82]. A family `b : Fin n → E` lives in an arbitrary real inner product space (for example `EuclideanSpace ℝ (Fin m)`). Its Gram–Schmidt vectors are Mathlib's `gramSchmidt ℝ b`, and its coefficients are `gramSchmidtCoeff ℝ b i j = ⟪b*ⱼ, bᵢ⟫ / ‖b*ⱼ‖²` ([GramSchmidtOrtho.lean](../../Complexity/Foundations/Analysis/InnerProductSpace/GramSchmidtOrtho.lean), a Mathlib candidate). The lattice is `Submodule.span ℤ (Set.range b)`.

- **Reduced bases and Proposition (1.11):** `IsReduced δ b` is size reduction (1.4) together with the exchange condition (1.5), where the constant `3/4` is replaced by `δ`. `IsReduced.norm_sq_le` proves `‖b₀‖² ≤ (4/(4δ-1))ⁿ ‖x‖²` for `b : Fin (n + 1) → E`, `1/4 < δ ≤ 1` and every nonzero lattice vector `x`. `IsReduced.norm_le_sqrt_two_pow_mul` is the case `δ = 3/4`, `‖b₀‖ ≤ (√2)ⁿ ‖x‖`. Neither statement assumes linear independence.
- **Steps:** `IsSizeStep` (`bᵢ ← bᵢ - r bⱼ`, `j < i`, `r ∈ ℤ`) keeps the lattice and every Gram–Schmidt vector. `abs_gramSchmidtCoeff_round_le_of_ne_zero` shows that rounding `μᵢⱼ` gives `|μᵢⱼ| ≤ 1/2` when `b*ⱼ ≠ 0` (`abs_gramSchmidtCoeff_round_le` for linearly independent `b`). `IsSwapStep δ` swaps `bᵢ, bᵢ₊₁` when (1.5) fails, and `gramSchmidt_swap_self` is the swap formula (1.22).
- **Potential:** `gramPrefixDet b k = ∏_{j<k} ‖b*ⱼ‖²` equals the Gram determinant of the first `k` vectors (`gramPrefixDet_eq_det`, via `det_gram_eq_prod_norm_gramSchmidt_sq`). `potential b` is their product `D`. `IsSwapStep.potential_lt` proves `D' < δ D`. For linearly independent `b` with integral inner products (`HasIntegralGram`, e.g. `bᵢ ∈ ℤᵐ`) and `‖bᵢ‖² ≤ B`, `one_le_potential` and `potential_le` give `1 ≤ D ≤ B^{n(n-1)/2}`. Along any run of `IsStep`s, `inv_pow_swapCount_le` and `swapCount_le` bound the number of exchange steps by `(n(n-1)/2) log B / log (1/δ)` for `0 < δ < 1`.
- **The algorithm:** import `Complexity.Algorithms.LatticeReduction.LLL` ([RationalGramSchmidt.lean](../../Complexity/Algorithms/LatticeReduction/RationalGramSchmidt.lean), [LLL.lean](../../Complexity/Algorithms/LatticeReduction/LLL.lean)). An integer basis is `B : Vector (Vector ℤ m) n`, with rows `rows B` and `realRows B` in `EuclideanSpace ℝ (Fin m)`. `gramSchmidtRows B` computes the Gram–Schmidt vectors exactly over `ℚ` (`gramSchmidtRowsAux_spec` identifies them with `gramSchmidt ℝ`). `lllLoop δ fuel B k` is the loop (1.15)–(1.21), with stage `k` here equal to stage `k + 1` of the source: at `0 < k < n` it rounds `μₖ,ₖ₋₁` (1.18), then either swaps `bₖ₋₁, bₖ` and steps back when (1.5) fails (Case 1) or size-reduces the rest of row `k` and advances (Case 2). `lll B` runs it with `δ = 3/4` for `n + 2 (swapBudget n (sqNormSum B) + 1)` rounds, where `sqNormSum B = Σᵢ ‖bᵢ‖²` (the source uses `max ‖bᵢ‖²`). Each size-reduction step subtracts `⌊μᵢⱼ⌉ bⱼ` unconditionally, while the source reduces only when `|μᵢⱼ| > 1/2`; the two differ only at `μᵢⱼ = ±1/2`. If the input rows are linearly independent over `ℝ` (decidable by `linearIndependent_realRows_iff`, a nonzero integer Gram determinant), `isReduced_lll` proves that the output is `3/4`-reduced and linearly independent and `dotProduct_lll_zero_le` gives (1.11) for it, `|b₀|² ≤ 2ⁿ |x|²` for every nonzero `x` in the lattice of `n + 1` rows. `span_lll` proves that the lattice is unchanged, with no hypothesis. The loop invariant `lllLoop_spec` is stated for every `δ > 0` but is meaningful only for `0 < δ < 1` (its potential hypothesis fails for `δ ≥ 1`), and the round budget comes from the potential (`potential_realRows_lt`). Each round recomputes the Gram–Schmidt rows with `O(n² m)` rational operations instead of the source's incremental update, and there is no cost model.

The [checked examples](../../ComplexityTests/Algorithms/LatticeReduction.lean) show that the standard basis of `ℤ²` is `3/4`-reduced and apply the SVP bound to it, and that `(e₀, ½ e₀ + e₁)` is `3/4`-reduced with `μ₁₀ = 1/2`. They also show that `(e₀, e₀ + e₁)` is not size reduced, and that swapping `(2 e₀, e₀ + e₁)` is an exchange step taking the potential from `4` to `2 < (3/4) · 4`. The [algorithm examples](../../ComplexityTests/Algorithms/LatticeReduction/LLL.lean) evaluate `lll` and `gramSchmidtRows` on small bases with `#guard`, and instantiate `isReduced_lll`, `span_lll` and `dotProduct_lll_zero_le` on the integer basis `((1, 0), (7, 1))`, which has an integral Gram matrix and linearly independent rows. Not formalized: a cost model for `lll` with the arithmetic-operation and bit-size bounds of (1.26), and a polynomial-time statement ([ROADMAP](../../ROADMAP.md#optimization-and-duality)).

## Goemans–Williamson MAX-CUT rounding

Import `Complexity.Algorithms.Lean.MaxCut.GoemansWilliamson` ([GoemansWilliamson.lean](../../Complexity/Algorithms/Lean/MaxCut/GoemansWilliamson.lean)). This analyzes random-hyperplane rounding of a given vector solution of the MAX-CUT semidefinite relaxation [Goemans and Williamson, Sections 2–3][goemanswilliamson95]. The rounding is an expectation under Mathlib's exact `stdGaussian`; no SDP solver, finite-precision sampler or running time is involved. A weighted multigraph is a `Fintype` of edges `ι` with `ends : ι → V × V` and weights `w : ι → ℝ`. `cutValue ends w side` is the weight of a cut and `sdpValue ends w v = ∑ e, w e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2` is the relaxation's objective at a vector assignment `v : V → F`. `hyperplaneSide v r i = decide (0 ≤ ⟪v i, r⟫)` is the rounded cut. The source draws `r` uniformly from the sphere; the side depends only on the direction of `r`, so a standard Gaussian gives the same distribution.

- **The constant:** `Real.goemansWilliamsonConstant` ([GoemansWilliamson.lean](../../Complexity/Foundations/Analysis/SpecialFunctions/GoemansWilliamson.lean)) is `α = inf_{0 < θ ≤ π} (2 / π) θ / (1 - cos θ)`. `goemansWilliamsonConstant_mul_le_arccos` is Lemma 3.4 (`α (1 - y) / 2 ≤ arccos y / π` on `[-1, 1]`). `lt_goemansWilliamsonConstant` is Lemma 3.5 (`0.87856 < α`), and `goemansWilliamsonConstant_lt` gives `α < 0.87857`. The numerics use the source's tangent-line argument at `θ₀ = π - 0.810474`, with degree-ten Taylor bounds `Real.cos_bound_ten` and `Real.sin_bound_ten` ([Trigonometric/Bounds.lean](../../Complexity/Foundations/Analysis/SpecialFunctions/Trigonometric/Bounds.lean)) and Mathlib's six-digit bounds on `π`.
- **Expectation:** `integral_cutValue_hyperplaneSide` is Theorem 3.1 (expected weight `∑ e, w e * arccos ⟪…⟫ / π` for unit vectors), from Sheppard's formula (`measureReal_stdGaussian_zero_mem_uIoc_eq_arccos`, the source's Lemma 3.2). `goemansWilliamsonConstant_mul_sdpValue_le_integral` is Theorem 3.3 for nonnegative weights.
- **Guarantee against the true optimum:** `sdpValue_signVector` shows that a cut's `±u` vector solution has objective equal to the cut's weight. Hence `goemansWilliamsonConstant_mul_sub_le_integral` gives `α (cutValue side - ε) ≤ E[cutValue (hyperplaneSide v r)]` for every cut `side`, when `v` are unit vectors within `ε` of optimal. `goemansWilliamsonConstant_mul_cutValue_le_integral` is the exact-optimum form. `exists_forall_goemansWilliamsonConstant_mul_sub_le` picks one hyperplane achieving the bound, and `exists_isMaxOn_sdpValue` shows that optimal unit vectors exist in every nontrivial finite-dimensional space.
- **Bridge:** in [GoemansWilliamsonCutWeight.lean](../../Complexity/Algorithms/Lean/MaxCut/GoemansWilliamsonCutWeight.lean), kept separate so the analysis does not import the machine-level `MaxCut` development, `cutValue_eq_cutWeight` identifies `cutValue` on an edge list with `Cslib.Complexity.MaxCut.cutWeight`, the weight used by the NP-complete `MaxCut` problem. `goemansWilliamsonConstant_mul_cutWeight_le_integral` restates the guarantee there.

The [checked examples](../../ComplexityTests/GoemansWilliamsonMaxCut.lean) use the triangle with three unit vectors at `120°`. Their objective `9 / 4` is optimal because `‖a + b + c‖² ≥ 0`, so the headline hypotheses are satisfiable. The rounded cut has expected weight exactly `2`, the maximum cut. Not formalized: polynomial-time SDP solving to precision `ε`, a `ProbComp` realization of the Gaussian, tightness (the Feige–Schechtman integrality gap), the MAX-2SAT and MAX-DICUT extensions and derandomization ([#3230](https://github.com/cslib-community/complexitylib/issues/3230)).

## Freivalds' matrix-product verification

Import `Complexity.Algorithms.Lean.Freivalds` ([Complexity/Algorithms/Lean/Freivalds.lean](../../Complexity/Algorithms/Lean/Freivalds.lean)). It checks a claimed product `A * B = C` of rectangular matrices `l × m`, `m × n` and `l × n` over any ring with decidable equality, following [Freivalds][freivalds79]. The deterministic check `checkM A B C x` computes `A *ᵥ (B *ᵥ x)` and `C *ᵥ x` in `TimeM` and compares them. The cost model charges `2` per dot-product entry (one multiplication, one addition) and `1` per compared entry; reads, sampling and the vector encoding are free, and ring operations have unit cost whatever the operand size. Under it, `time_checkM` is exactly `2 * (m * n + l * m + l * n) + l`, independent of `x`, and `time_checkAllM_square` gives `k * (6 * n ^ 2 + n)` for `k` checks of square matrices.

`verify e k A B C` is a `ProbComp` that draws `k` uniform vectors in `Fin n → S`, encodes the entries with `e : S → R` and runs every check. The guarantees are one-sided:

- **Completeness:** `eval_verify_of_mul_eq` gives acceptance with probability exactly `1` when `A * B = C`.
- **Soundness:** `eval_verify_true_le` bounds acceptance of an incorrect product by `(1/|S|)^k`, given that `s ↦ d * e s` is injective for every nonzero `d`. With `0`/`1` vectors (`bit`) this hypothesis holds over every ring and `eval_verify_bool_true_le` gives `(1/2)^k`; for `k = 1` this is Theorem 1.4 of [Mitzenmacher and Upfal][mitzenmacherupfal17]. Over a finite field with uniform vectors, `eval_verify_field_true_le` gives `(1/|F|)^k`.

The probability core is in [Complexity/Probability/Freivalds.lean](../../Complexity/Probability/Freivalds.lean). It contains the counting bound `card_filter_mulVec_eq_mul_card_le`, its `k`-vector form, and `isUniversalHash_mulVec`, which states `M ↦ M *ᵥ (e ∘ x)` as a `1/|S|`-universal family under the existing `IsUniversalHash` predicate. The [checked examples](../../ComplexityTests/Freivalds.lean) include several things. One is a `2 × 2` product that one vector misses and another exposes. Another is a `1 × 1` instance whose acceptance probability is exactly `1/2`, which shows the `0`/`1` bound is attained. A third is a `ZMod 4` instance where the encoding `id` fails the injectivity hypothesis and the counting bound fails with it. The randomized verifier is not a machine program: Karp–Rabin fingerprinting, rolling-hash matching, the fingerprint equality protocol and bit-level costs remain open ([ROADMAP](../../ROADMAP.md#randomized-verification-and-fingerprinting)).

## Luby's randomized maximal independent set

Import `Complexity.Algorithms.Lean.LubyMIS` ([Complexity/Algorithms/Lean/LubyMIS.lean](../../Complexity/Algorithms/Lean/LubyMIS.lean)). It formalizes the random-priority variant of Luby's algorithm, Algorithm 7.12 ("Fast MIS 2") of [Wattenhofer][wattenhofer16], which the source attributes to Métivier, Robson, Saheb-Djahromi and Zemmari. The graph is a Mathlib `SimpleGraph V` on a finite type, and the target is Mathlib's `Maximal G.IsIndepSet`. A `State` holds the chosen and the live vertices. `phase` is a `ProbComp` that draws a uniform ranking `σ : V ≃ Fin (card V)`, a uniform random permutation. It then takes the deterministic `step`: every live vertex that ranks below all its live neighbours joins (`joiners`), and the joiners and their neighbours stop being live. `run k` iterates `phase` `k` times from the all-live state (`OracleComp.iterate`), and `lubyMIS k` answers the chosen set. Probabilities are statements about `ProbComp.eval`.

- **Correctness:** `isIndepSet_of_mem_support_lubyMIS` says that every output is independent after any number of phases. `Invariant.maximal_iff` says that a reachable chosen set is maximal exactly when nothing is live. `maximal_of_mem_support_lubyMIS` says that after any `k ≥ card V` phases every output is maximal, because the least-ranked live vertex always joins. `liveGraph L` is Mathlib's `(G.induce L).spanningCoe` (`liveGraph_eq_spanningCoe_induce`).
- **Edge removal:** `two_mul_expect_liveEdges_phase_le` says that one phase keeps at most half the live edges in expectation (Lemma 7.14). It follows from the counting form `two_mul_sum_liveEdges_step_le`, a sum over all rankings, and from `card_filter_least_mul_card`: a fixed vertex of a set `S` ranks least on `S` for exactly `1/|S|` of the rankings.
- **Round bounds:** iterating gives `two_pow_mul_expect_liveEdges_run_le`, at most `|E| / 2^k` expected live edges after `k` phases. Markov's inequality then gives `two_pow_mul_toOuterMeasure_live_nonempty_le`. If `|E| ≤ 2^m`, `toOuterMeasure_not_maximal_lubyMIS_le` says that `m + t + 1` phases fail to give a maximal independent set with probability at most `2^-t`. `one_sub_le_toOuterMeasure_maximal_lubyMIS` and its `_clog` and `_card` forms state this as success at least `1 - 2^-t`, with `m` instantiated to `⌈log₂ |E|⌉` and to `2⌈log₂ n⌉`. `toOuterMeasure_not_maximal_lubyMIS_le_inv_pow` bounds the failure probability after `(c + 2)⌈log₂ n⌉ + 1` phases by `n^-c`.

The source draws independent reals in `[0, 1]`. Restricted to the live vertices, a uniform ranking has the same law as the order of those reals, but this equivalence is not formalized. The source gets its high-probability bound from Lemma 7.14 by a Chernoff argument (Corollary 7.18). Here the `O(log n)` bound comes from the first moment, with explicit constants. Theorem 7.15, the expected number of phases, is not formalized. The model is a centralized simulation of the synchronous phases, not a LOCAL message-passing algorithm. Messages, the rounds inside a phase and per-vertex views are not modelled, so it is not connected to the oriented-cycle LOCAL model of [Distributed rounds in the LOCAL model](../circuits-logic-and-other-models/query-and-communication.md#distributed-rounds-in-the-local-model). Luby's original marking algorithm with pairwise independence, its NC derandomization, Ghaffari's `O(log Δ) + poly(log log n)` bound and the Kuhn–Moscibroda–Wattenhofer lower bounds remain open; see `ROADMAP.md`. The [checked examples](../../ComplexityTests/Algorithms/Lean/LubyMIS.lean) run the phases on the paths with three and four vertices and on the triangle. They show that a phase need not remove every edge, count the live edges left on the four-vertex path over all `24` rankings, and show that the intermediate chosen set is not maximal. They also instantiate the Las Vegas statement nonvacuously and check one instance of the high-probability bound.

## Euler circuits in multigraphs

Import `Complexity.Algorithms.Lean.Euler.Circuit` ([source](../../Complexity/Algorithms/Lean/Euler/Circuit.lean)). A finite multigraph is an edge list `H : List (α × α)`, with parallel edges and self-loops allowed, and edges are compared up to orientation through `undirected`. A walk is a vertex list whose edges are its consecutive pairs (Mathlib's `List.consecutivePairs`). `IsEulerCircuit H u w` says that `w` runs from `u` back to `u` and uses every edge of `H` exactly once, in either direction. The degree of a vertex counts endpoints, so a self-loop counts twice.

`exists_isEulerCircuit_iff` is Euler's theorem in this model: an Euler circuit from `u` exists exactly when every degree is even and every edge is connected to `u` (`Relation.EqvGen` of the edge relation, analogous to Kruskal's tree). Unlike the textbook statement for connected loopless graphs, the model allows self-loops and the empty multigraph and ignores isolated vertices. The sufficiency direction is constructive. `eulerCircuit H u` is Hierholzer's algorithm [Hierholzer][hierholzer73] ([Korte and Vygen][kortevygen18], Section 2.4): `walkFrom` follows unused edges greedily, and `walkFrom_spec` shows that it can only stop at the other odd vertex, or back at its start when all degrees are even. `eulerLoop` then splices in closed walks from visited vertices that still have unused edges. `mem_of_isEulerCircuit` says that the circuit visits every vertex connected to its start, and `sum_map_consecutivePairs_eq` that it weighs as much as its multigraph under a symmetric weight. Mathlib's `SimpleGraph.Walk.IsEulerian` covers only simple graphs and only necessity. The list model is what Christofides' algorithm needs, since a spanning tree together with a matching may repeat an edge. No running time is charged.

The [examples](../../ComplexityTests/EulerCircuit.lean) run the algorithm on a bowtie (where a second triangle must be spliced in) and on a multigraph with parallel edges and a self-loop. They also refute Euler circuits for a path with odd endpoints and for two disjoint triangles whose degrees are even.

## Christofides' 3/2-approximation for metric TSP

Import `Complexity.Computability.Complexity.Problems.TSP.Christofides` ([source](../../Complexity/Computability/Complexity/Problems/TSP/Christofides.lean)); the generic algorithm is in `Complexity/Algorithms/Lean/TSP/Christofides.lean`. It uses the cost model of the MST 2-approximation above: vertices `Fin n`, costs `δ : Fin n → Fin n → ℕ` and closed-walk cost `cycleCost δ`. `christofides δ` takes Kruskal's tree `T` of the complete graph and the odd-degree vertices `oddVertices T`. It computes a minimum-weight perfect matching `M` on them with `minPerfectMatching`, runs Hierholzer's `eulerCircuit` on the edge list `T.map WeightedEdge.endpoints ++ M` (the multigraph `T ⊎ M`, where an edge in both appears twice) from vertex `0`, and shortcuts the result with `List.dedup`. A perfect matching on `O` is an edge list whose `VertexCover.endpoints` are a permutation of `O`. The proof follows Theorem 2.13 of [Williamson and Shmoys][williamsonshmoys11] ([Christofides][christofides76]):

- **Handshake:** `Euler.even_length_filter_odd_degree` ([Handshake.lean](../../Complexity/Algorithms/Lean/Euler/Handshake.lean)) holds for list multigraphs with parallel edges and self-loops. It gives `even_length_oddVertices`.
- **Shortcutting:** `cycleCost_le_of_sublist` ([Shortcut.lean](../../Complexity/Algorithms/Lean/TSP/Shortcut.lean)) says that under the triangle inequality, a subsequence of a closed walk costs no more. `cycleCost_dedup_le_of_isEulerCircuit` bounds a shortcut Euler circuit by the weight of its multigraph. `List.dedup` keeps the last visit to each vertex, whereas the textbook keeps the first; both are subsequences.
- **Matching bound:** `two_mul_sum_le_cycleCost` ([PerfectMatching.lean](../../Complexity/Algorithms/Lean/TSP/PerfectMatching.lean)) shows that a minimum-weight perfect matching on `O` costs at most half of any tour through `O`. The tour is shortcut to `O` and its edges are split into two alternating perfect matchings. This step needs no symmetry.
- **Bound:** `two_mul_cycleCost_shortcutTour_le_three_mul` holds for any `IsMinSpanningTree` and any minimum-weight perfect matching on its odd vertices. `two_mul_cycleCost_christofides_le_three_mul` is the algorithm's instance. On `TSP` instances, `christofidesTour_perm` and `two_mul_tourLength_christofidesTour_le_three_mul` state `2 · length ≤ 3 · length(p)` for every tour `p` of a metric matrix (`TSP.IsMetric`, as above).

`minPerfectMatching` is exhaustive search over `(2k − 1)!!` matchings, with optimality proved by `sum_minPerfectMatching_le`. So these results certify the approximation ratio, not a polynomial running time. Edmonds' weighted matching algorithm ([Edmonds][edmonds65]) and any machine-level certificate remain open. The [examples](../../ComplexityTests/TSPChristofides.lean) run the algorithm on a four-city star whose three perfect matchings cost `5`, `6` and `6`; exhaustive search picks the cheapest. The Euler circuit `[0, 1, 2, 0, 3, 0]` is shortcut to an optimal tour of length `11`. The examples also instantiate the general bound with Kruskal's tree, and check the empty and one-city instances.

## String algorithms

String algorithms are written in `Cslib.Algorithms.Lean.TimeM` and charge one tick per character comparison. Array reads and writes, index arithmetic, allocation and list/array conversions are free. Exact matching against a single pattern is Knuth–Morris–Pratt ([source](../../Complexity/Algorithms/Lean/KMP/Search.lean)). It makes at most `2 * (|p| - 1) + 2 * |t|` comparisons (`kmpSearchM_time_le`), and `mem_kmpMatchesList_iff` characterizes its output.

Suffix arrays index one text for many patterns. Import `Complexity.Algorithms.Lean.SuffixArray.Basic`, `.Kasai` and `.Search` ([Basic](../../Complexity/Algorithms/Lean/SuffixArray/Basic.lean), [Kasai](../../Complexity/Algorithms/Lean/SuffixArray/Kasai.lean), [Search](../../Complexity/Algorithms/Lean/SuffixArray/Search.lean)). The alphabet is any `LinearOrder`, ordered with Mathlib's lexicographic order on lists, so a proper prefix comes before the words that extend it. No end-of-word sentinel is assumed, and only the nonempty suffixes `w.drop i` with `i < |w|` are listed.

- **Specification.** `IsSuffixArray w sa` says that `sa` is a permutation of `List.range w.length` whose suffixes strictly increase [Manber and Myers][manbermyers93]. `IsSuffixArray.unique` shows that suffix arrays are unique. `suffixArray w` sorts the positions by their suffixes with `List.mergeSort`, and `isSuffixArray_suffixArray` proves it correct. This reference construction is uncharged and not linear-time.
- **LCP array.** `lcpArray w sa` has `0` at rank `0` and the longest-common-prefix length (`lcpLen`) of the suffixes of ranks `r - 1` and `r` at rank `r > 0`. `IsSuffixArray.getElem_lcpArray_sub_one_le` is the height lemma `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1` of [Kasai et al.][kasai01].
- **Kasai et al.'s algorithm.** `kasaiM w sa` visits positions in text order. It extends each common prefix from the previous length minus one. `ret_kasaiM` and `kasai_eq_lcpArray` show that it returns `lcpArray` whenever `sa` is a suffix array. `kasaiM_time_le` bounds its cost by `2 * |w|` comparisons for every input, valid suffix array or not. Building the rank array is uncharged.
- **Pattern search.** `searchM w sa p` runs two binary searches (`lowerBoundM`, in `Complexity.Algorithms.Lean.BinarySearch`) and returns a rank interval `[lo, hi)`. Each probe compares `p` with at most `|p|` characters of a suffix. `searchM_spec` shows that the suffix of rank `r` starts with `p` exactly when `lo ≤ r < hi`, so the occurrences form a contiguous interval of the suffix array. `mem_occurrences` turns this into membership of text positions. `searchM_time_le` bounds the cost by `2 * |p| * (⌊log₂ |sa|⌋ + 1)` comparisons. This is the plain `O(|p| log n)` search. The `O(|p| + log n)` search, which reuses precomputed LCP information between probes, is not formalized.

For the empty pattern the search returns every position `i < |w|`. KMP also reports the position `|w|` of the empty suffix. The [examples](../../ComplexityTests/SuffixArray.lean) check `banana` and `mississippi`: the suffix and LCP arrays, the comparison counts, and agreement with KMP on several patterns. They also include a kernel-checked suffix array with its uniqueness, a rejected non-sorted permutation, and absent and empty patterns. Linear-time construction (SA-IS, DC3), LCP-accelerated search and suffix trees remain open ([ROADMAP](../../ROADMAP.md#string-algorithms)).

## Lempel–Ziv incremental parsing (LZ78)

Import `Complexity.Algorithms.Lean.LempelZiv.LZ78Bits`. The parse and pair code are in [LZ78.lean](../../Complexity/Algorithms/Lean/LempelZiv/LZ78.lean), which needs only list imports. The phrase count is in [LZ78Count.lean](../../Complexity/Algorithms/Lean/LempelZiv/LZ78Count.lean), the bit code in [LZ78Bits.lean](../../Complexity/Algorithms/Lean/LempelZiv/LZ78Bits.lean), and the alphabet-generic [distinct-parsing bound](../../Complexity/Algorithms/Lean/LempelZiv/DistinctParsing.lean) in the namespace `DistinctParsing`. `LZ78.parse` is the incremental parsing of [Ziv and Lempel][zivlempel78] on `List α` for any type with decidable equality. Each phrase is the shortest prefix of the remaining input that is not an earlier phrase; when the input runs out first, the last phrase is the nonempty remainder and may repeat an earlier phrase. The phrases concatenate to the input (`flatten_parse`) and are nonempty. Each phrase is the shortest new prefix (`prefix_mem_take_parse`, `getElem_parse_notMem_take`), and the phrases before the last are pairwise distinct (`nodup_dropLast_parse`; all are distinct when the last phrase is new, `nodup_parse_of_getLast_notMem`). `LZ78.encode` writes phrase `w` as the pair (index of `w.dropLast` among `[]` and the earlier phrases, last symbol of `w`), and `decode_encode` says that `LZ78.decode` inverts it. `LZ78.encodeBits e` fixes a numbering `e : α ≃ Fin k` and writes the `i`-th pair with `⌈log₂ i⌉` pointer bits and `⌈log₂ k⌉` symbol bits, least significant bit first. `decodeBits_encodeBits` gives the round trip for `k ≥ 2`.

The bounds are for an alphabet of size `k ≥ 2`, an input of length `n` and `c` phrases. The basic inequality is `m * c ≤ n + 2 * k ^ m` for every `m` (`mul_length_le_of_nodup` for distinct parsings and `mul_length_parse_le` for LZ78, whose last phrase may repeat). Choosing `m` gives `c * ⌊log_k c⌋ ≤ n + 2c` (`length_parse_mul_log_le`) and `c (log_k n - log_k log_k n - 4) ≤ n` (`length_parse_mul_logb_sub_le`). It also gives `c ≤ n / ((1 - ε_n) log_k n)` for `n ≥ 2` and `ε_n < 1` (`length_parse_le_div`), where `epsilon k n = min 1 ((log_k log_k n + 4) / log_k n)` (`epsilon_def`) tends to `0` (`tendsto_epsilon`). For `k = 2` this is the distinct-parsing lemma of [Cover and Thomas][coverthomas06], §13.5; the general-`k` form, with logarithms to base `k`, is the same argument. The code length is exactly `∑_{i=1}^{c} (⌈log₂ i⌉ + ⌈log₂ k⌉)` (`length_encodeBits`). It is at most `c (⌈log₂ c⌉ + ⌈log₂ k⌉)` (`length_encodeBits_le`) and at most `⌈log₂ k⌉ (n + 4c)` (`length_encodeBits_le_mul_add`). It is also at most `⌈log₂ k⌉ n (1 + 4 / ((1 - ε_n) log_k n))` (`length_encodeBits_le_mul_one_add`), so LZ78 expands no input by more than a vanishing fraction over the fixed-length code (`exists_length_encodeBits_le`). The functions are reference implementations with list-based dictionary lookups, and no running time is claimed.

The [examples](../../ComplexityTests/Algorithms/Lean/LempelZiv.lean) check the Cover–Thomas input `ABBABBABBBAABABAA`: its phrases `A, B, BA, BB, AB, BBA, ABA, BAA`, its pairs, and its 25-bit code. They also cover the empty input and `AA`, whose repeated last phrase makes the parse not duplicate free. Further checks are a phrase list that is not tree structured, bit strings that fail to decode, `1 ^ 100` with 14 phrases and 55 bits, and an input length (`n = 256`) at which the `ε_n` hypotheses hold. Not formalized: optimality for stationary ergodic sources (Ziv's inequality, a compression ratio tending to the entropy rate), LZ77 and sliding windows, and the links to Kolmogorov complexity and finite-state compressibility ([ROADMAP](../../ROADMAP.md#pseudorandomness-coding-and-boolean-analysis)).

## Tree Evaluation

The [Cook–Mertz endpoint](catalytic-and-tree-evaluation.md) computes the root of an explicitly table-encoded perfect binary tree in native independent workspace `O(log n · log log n)` for positive value length and height. The output is not charged to workspace, and the theorem leaves time existential. The same page distinguishes borrowed-register restoration and fan-in/packed procedure variants.

## Known Limitations

The numeric values above are transcriptions of checked source statements, not results of new execution benchmarks. The source-reference audit checks locations and digests; it does not rerun Lean or prove asymptotic summaries. The full Haskell/Lean runtime behavior, allocator, operating system and hardware are outside these idealized RAM models.

[berge57]: ../sources.md#berge57
[berge58]: ../sources.md#berge58
[complexitylib]: ../sources.md#complexitylib
[bertsekas88]: ../sources.md#bertsekas88
[bertsekas98]: ../sources.md#bertsekas98
[bfprt73]: ../sources.md#bfprt73
[ccpv11]: ../sources.md#ccpv11
[christofides76]: ../sources.md#christofides76
[clrs09]: ../sources.md#clrs09
[coverthomas06]: ../sources.md#coverthomas06
[dilworth1950]: ../sources.md#dilworth1950
[edmonds65]: ../sources.md#edmonds65
[erdosszekeres1935]: ../sources.md#erdosszekeres1935
[fks84]: ../sources.md#fks84
[floyd62]: ../sources.md#floyd62
[fnw78]: ../sources.md#fnw78
[freivalds79]: ../sources.md#freivalds79
[fulkerson1956]: ../sources.md#fulkerson1956
[goemanswilliamson95]: ../sources.md#goemanswilliamson95
[goldbergtarjan88]: ../sources.md#goldbergtarjan88
[gomoryhu61]: ../sources.md#gomoryhu61
[gusfield90]: ../sources.md#gusfield90
[hierholzer73]: ../sources.md#hierholzer73
[hmu06]: ../sources.md#hmu06
[kasai01]: ../sources.md#kasai01
[kasami65]: ../sources.md#kasami65
[kortevygen18]: ../sources.md#kortevygen18
[lll82]: ../sources.md#lll82
[manbermyers93]: ../sources.md#manbermyers93
[mirsky1971]: ../sources.md#mirsky1971
[mitzenmacherupfal17]: ../sources.md#mitzenmacherupfal17
[nagamochiibaraki92]: ../sources.md#nagamochiibaraki92
[roth82]: ../sources.md#roth82
[rothpostlewaite77]: ../sources.md#rothpostlewaite77
[roughgarden13cs364a]: ../sources.md#roughgarden13cs364a
[schrijver03]: ../sources.md#schrijver03
[schrijver17]: ../sources.md#schrijver17
[schummervohra07]: ../sources.md#schummervohra07
[shapleyscarf74]: ../sources.md#shapleyscarf74
[sipser13]: ../sources.md#sipser13
[stoerwagner97]: ../sources.md#stoerwagner97
[vww18]: ../sources.md#vww18
[thorup13]: ../sources.md#thorup13
[wattenhofer16]: ../sources.md#wattenhofer16
[williamsonshmoys11]: ../sources.md#williamsonshmoys11
[younger67]: ../sources.md#younger67
[zivlempel78]: ../sources.md#zivlempel78
