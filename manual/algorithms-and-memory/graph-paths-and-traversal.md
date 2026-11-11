# Shortest paths, traversals, Euler circuits and arborescences

Part of the [representative algorithm endpoints](algorithm-endpoints.md); the conventions and limitations stated there apply to this page.

## Shortest paths and priority queues

[abstracts/CslibFrontierAbstracts/DijkstraAbstract.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/DijkstraAbstract.lean) (retired; its bridge applied [LogLinear.lean](../../CslibFrontier/Algorithms/WordRAM/Dijkstra/LogLinear.lean) and [Fibonacci.lean](../../CslibFrontier/Algorithms/WordRAM/Dijkstra/Fibonacci.lean)) represents directed weighted multigraphs by adjacency lists with natural weights; parallel edges and self-loops are allowed. Output distance is an extended natural, encoded as zero for infinity and `d+1` for a finite distance. The word condition is `8*(n+m+2)*(W+2) < 2^w`.

`dijkstra_logLinear` (library `logLinearStatement`) has `O((m+1)*(floorlog₂(n)+1))` instructions; `dijkstra_fibonacci` (library `fibonacciStatement`) has `O(m+n*(floorlog₂(n)+1))`. The graph is already installed in the machine's initial memory. The first bound can omit a standalone scan over isolated vertices because untouched zero memory represents infinity. Treating graph construction or a mandatory full output traversal as charged work would be a different end-to-end contract.

[abstracts/CslibFrontierAbstracts/FibonacciHeapAbstract.lean](https://github.com/cslib-community/cslib-frontier/blob/f65cf6aabf60f13270367fea7d080141c7a910f5/abstracts/CslibFrontierAbstracts/FibonacciHeapAbstract.lean) (retired; its bridge applied [FibonacciHeap/MinPQ.lean](../../CslibFrontier/DataStructure/PriorityQueue/WordRAM/FibonacciHeap/MinPQ.lean)) specifies bounded-capacity handles, bounded key/value ranges, fresh-handle insertion and arbitrary minimum ties. Initializer/operation code is chosen before capacity/key/value/base/width parameters. The amortized total is constant per ordinary operation plus a sum of logarithms of current size for extract-min; no per-call worst-case bound is stated, even for queries. The operation set has no non-removing find-min: extract-min is the only operation that locates a minimum entry, and it removes that entry. Fresh zeroed memory permits constant-time initialization; the reusable-memory version explicitly clears the region and costs linear time. Both theorems execute demonically admissible adaptive clients (`Client`, whose continuations observe returned handles and extracted entries); external argument preparation, result decoding and pure host continuation choices between `p_op` calls are uncharged.


### Native binary heap and Dijkstra

Choose the API by the cost contract you need. For standalone operation calls, import
`CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Certificate` and use the
`Cslib.DataStructure.PriorityQueue.BinaryHeap.Native` namespace. `dynamicProgram`, `certificate`,
`instruction_bound` and `run_client_bound` provide one fixed program, its representation and
halt-inclusive bounds for admissible calls and adaptive clients. The
[complete priority-queue client](../../CslibFrontierTests/WordRAMPriorityQueue.lean) supplies the
imports, argument-register setup, representation and valid-history proofs. The
[raw implementation client](../../CslibFrontierTests/WordRAMBinaryHeapImplementation.lean) also
checks zero capacity, narrow widths, noncanonical tags and retained outside memory.

Keep initialization separate from those call bounds. Here `n` is capacity, `K` the key bound
and `base` the owned base; `Fits w a` means `a < 2^w`. The linked clients supply bounded-state,
argument-matching and representation premises at the points where they are required:

| Route | Storage and prerequisite | Charged initialization |
|---|---|---|
| Fresh compact raw heap | `3*n+1` words, `Fits w (base+3*n+1)`, `Fits w K` and an explicitly zero owned block | The native fresh initializer; no clearing is needed under this premise |
| Dirty compact raw heap | The same `3*n+1`-word region with arbitrary bounded contents | Shared `initClear`: `initTime + 4*space + 6` body instructions, with any final halt separate |
| Allocated memory-program heap | Original `Memory.allocLayout`, with `Fits w (frontier+3*n+2)` and `3*n+2` reserved words | Two dirty memory queries preserve old contents; heap-invariant construction uses `ZeroAbove` |

The [complete initialization client](../../CslibFrontierTests/WordRAMBinaryHeapInitialize.lean)
checks these distinct layouts and width boundaries. The native certificates are in
[Native/Initialize.lean](../../CslibFrontier/DataStructure/PriorityQueue/BinaryHeap/Native/Initialize.lean).
The two-query count uses `Memory.charge`; its native realization also pays staging and copying.
Dirty allocation does not itself make memory zero, and local zero for one raw initialization is
not a reusable global allocator precondition. If fresh-zero premises are unavailable, retain the
linear dirty-clear allowance instead of applying the fresh theorem.

Standalone calls leave external argument delivery, result decoding and host continuation work
uncharged. For the fully compiled binary-heap Dijkstra client, import
`CslibFrontier.Algorithms.Lean.Dijkstra.Native.Binary`. In its
`Cslib.Algorithms.Lean.Dijkstra.Native.Binary` namespace, `realizes_run` certifies the original
allocated `Memory.run`; `exists_program_state` exports one program/register layout/factor before
all graphs and widths, with full final memory/frontier and the actual prefix, control and halt
charged. Use the [complete native client](../../CslibFrontierTests/DijkstraNativeBinary.lean) and
[headline client](../../CslibFrontierTests/WordRAMDijkstra.lean) for their imports, fitting hypotheses
and actual-run conclusions. The encoded graph is still supplied freely in the initial
`Data.init` memory with its zero tail: graph construction and installing those raw input words
are not included. The original word condition and `LogLinearStatement`
headline are unchanged.

The old `PriorityQueue.WordRAM.BinaryHeap` execution modules and their `Program`/`Sift` imports
are retired. Pure Model/Order declarations now live under `PriorityQueue.BinaryHeap`; use the
native route above for execution. Old fixed register/clock constants and the implementation
helpers with coefficients `200`/`230` are not replacement API guarantees. PQCode and the
Fibonacci execution core with live MinPQ consumers remain; these native Dijkstra endpoints do
not complete generic whole-client realization or the remaining heap migration.

### Native Fibonacci heap and Dijkstra

For the full shortest-path client, import
`CslibFrontier.Algorithms.Lean.Dijkstra.Native.Fibonacci` and use
`Cslib.Algorithms.Lean.Dijkstra.Native.Fibonacci.realizes_run` or `exists_program_state`.
The [checked client](../../CslibFrontierTests/WordRAMDijkstraFibonacci.lean) applies one native
program to the parallel-edge/multi-hop sample, unreachable vertices and sparse edgeless graphs;
it retains the whole source memory and exact allocated frontier. The stable
`fibonacciSpecStatement` and `fibonacciStatement` reader routes in
`CslibFrontier.Algorithms.WordRAM.Dijkstra.Fibonacci` keep their original types. The sharper clock
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
MinPQ remain. F2, its abstract-space decision and general whole-client
transfer remain open; the formal-abstract statements, since retired, were unchanged.

### All-pairs shortest paths and the (min,+) product

Import `CslibFrontier.Algorithms.Lean.Query.ShortestPaths.MinPlus` for the two reductions and `CslibFrontier.Algorithms.Lean.Query.Arith.FloydWarshall` for Floyd–Warshall; both import the pure walk and matrix-power theory in `CslibFrontier.Algorithms.ShortestPaths`.

These results use the query model `FreeM`, not the word RAM. A weighted digraph on `Fin n` is a matrix over `MinTropical R`, where `R` is any `LinearOrderedAddCommMonoidWithTop`, for example `WithTop ℤ` with negative weights. The tropical `0 = ⊤` means no edge, `*` adds weights and `+` takes minima, so the matrix product is the (min,+) product. [Walk.lean](../../CslibFrontier/Algorithms/ShortestPaths/Walk.lean) defines `walkWeight`, `NoNegCycle` (every closed walk has weight at least `0`) and `IsShortestDistances W D` (each `D i j` is the greatest lower bound of the weights of the walks from `i` to `j`). [Power.lean](../../CslibFrontier/Algorithms/ShortestPaths/Power.lean) proves `isShortestDistances_one_add_pow`: `(1 + W) ^ k` is the distance matrix for every `k ≥ n - 1` when there are no negative cycles. It also proves the negative-cycle test `noNegCycle_iff_one_le_one_add_pow_diag`, which makes `NoNegCycle` decidable [CLRS 25.1][clrs09].

The programs are generic in the entry type, so they combine weights only through `ArithQuery` queries: `.mul` adds weights and `.add` compares them. Correctness theorems assume an oracle that answers `.add` and `.mul` honestly. Cost theorems hold under every oracle. Indexing, `withOneDiag` and building the tripartite matrix are pure code, which `FreeM` does not charge.

| Declaration | Statement |
|---|---|
| `Cslib.Query.floydWarshall`, `cost_floydWarshall`, `isShortestDistances_floydWarshall` | Floyd–Warshall with pivots `0, …, n−1` makes exactly `n³` additions and `n³` multiplications and returns the distance matrix [Floyd 1962][floyd62], [CLRS 25.2][clrs09]. The pure lemma `Cslib.Algorithms.ShortestPaths.isShortestDistances_foldl_fwStep` proves the relaxation correct for every pivot list that contains each vertex, in any order |
| `Cslib.Query.schoolbookMatMul`, `cost_schoolbookMatMul` | the (min,+) product with `n²·(n·cMul + (n−1)·cAdd)` cost |
| `Cslib.Query.apspBySquaring`, `isShortestDistances_apspBySquaring`, `cost_apspBySquaring_le` | APSP from any product subroutine `mp` with `⌈log₂(n−1)⌉` calls, so cost `⌈log₂(n−1)⌉·t` when each call costs at most `t` |
| `Cslib.Query.minPlusViaAPSP`, `eval_minPlusViaAPSP`, `cost_minPlusViaAPSP` | the (min,+) product from one call of any APSP subroutine that is correct on `3n`-vertex graphs without negative cycles, at exactly the cost of that call |

The two reductions are in [MinPlus.lean](../../CslibFrontier/Algorithms/Lean/Query/ShortestPaths/MinPlus.lean), and the [tests](../../CslibFrontierTests/ShortestPaths.lean) run all programs on a graph with a negative edge. Together they show that a cost-`T(n)` algorithm for either problem gives one for the other with cost `⌈log₂(n−1)⌉·T(n)` or `T(3n)`. This is the starting point of the APSP class of [Vassilevska Williams and Williams][vww18].

#### Negative triangles and the (min,+) product

Import `CslibFrontier.Algorithms.Lean.Query.ShortestPaths.NegTriangleSubcubic` for the reduction from the (min,+) product to negative triangle detection. Its three steps are in [NegTriangleFinding.lean](../../CslibFrontier/Algorithms/Lean/Query/ShortestPaths/NegTriangleFinding.lean) and [MinPlusViaNegTriangle.lean](../../CslibFrontier/Algorithms/Lean/Query/ShortestPaths/MinPlusViaNegTriangle.lean). The last of these also has the converse.

The pure [NegativeTriangle.lean](../../CslibFrontier/Algorithms/ShortestPaths/NegativeTriangle.lean) states the problems on a tripartite graph with parts `I`, `J`, `K` and weight matrices `A : Matrix I K`, `B : Matrix K J`, `C : Matrix I J` over `MinTropical R`. `IsNegTriangle A B C i j k` means `A i k + B k j + C i j < 0`. `OnNegTriangle` asks for some `k`, and `HasNegTriangle` asks for some `i, j, k`. A finder answer `IsNegTriangleAnswer` is `none` exactly when there is no negative triangle. `onNegTriangle_iff` says the pair `(i, j)` lies on a negative triangle iff `(A * B) i j + C i j < 0`. `FiniteEntriesBounded A W` says the finite entries lie in `[-W, W]`, and `⊤` entries are allowed.

The reductions call subroutines. Finding and blocking are generic in the weights: they pass sub-matrices on and mask an edge by writing the no-edge weight `0`. The binary search and the converse are not generic. The binary search builds weights `-mid` and is specific to `MinTropical (WithTop ℤ)`, that is `ℤ ∪ {∞}`, and the converse compares the entries of the product. Unlike the APSP reductions above, these programs therefore build and compare weights in pure code. Correctness assumes that the subroutine is correct under the oracle. Cost theorems hold under every oracle and weight, given nonnegative per-call bounds. `FreeM` charges only subroutine calls. Building sub-instances, padding, loops, removed-edge bookkeeping, binary-search intervals and the converse's `n²` final comparisons are pure code and are free. So the cost theorems transfer the reduction's pattern of detector calls and are not intrinsic bounds on either problem. A detector that decides in pure code, issuing no queries, satisfies the exponent hypothesis with `c = 0`.

| Declaration | Statement |
|---|---|
| `Cslib.Query.findNegTri`, `isNegTriangleAnswer_findNegTri`, `cost_findNegTri_le` | finding a negative triangle on parts of size `2^L` by halving with a detector `det`: `8` calls per level and one at the bottom. The cost is at most `findNegTriCost τ L = τ 1 + ∑_{l<L} 8 τ(2^l)` when `det m` costs at most `τ m` for `m ≠ 0` [VWW Lemma 4.1][vww18] |
| `Cslib.Query.findNegTriCost_rpow_le` | Lemma 4.1 for polynomial costs: for `τ m = c·m^e` with `c ≥ 0` and `e ≥ 1`, `findNegTriCost τ L ≤ 8·c·(2^L)^e` |
| `Cslib.Query.allPairsNegTri`, `allPairsNegTri_eval`, `cost_allPairsNegTri_le` | all pairs on negative triangles, with parts split into `t` blocks of size `\|κ\|`. Each block triple is drained with a finder, and each triangle found has its `I`–`J` edge removed. This makes at most `t³ + (t\|κ\|)²` finder calls. It is the pairs form of [VWW Lemma 4.2][vww18]: the lemma outputs a maximal set of negative triangles with distinct `I`–`J` pairs, and the pairs on negative triangles are the consequence the paper states after it |
| `Cslib.Query.minPlusViaAPNT`, `eval_minPlusViaAPNT`, `cost_minPlusViaAPNT_le` | the (min,+) product by simultaneous binary search with an all-pairs subroutine: exactly `⌈log₂(2W+2)⌉` calls when the finite entries of `A * B` lie in `[-W, W]` [VWW Theorem 4.2][vww18] |
| `Cslib.Query.minPlusViaNegTri`, `eval_minPlusViaNegTri`, `cost_minPlusViaNegTri_le` | the composition, with blocks of size `s = 2^⌊⌊log₂ n⌋/3⌋` and `t = ⌊n/s⌋ + 1` blocks (padding with isolated vertices). The cost is at most `⌈log₂(2W+2)⌉·(t³ + (ts)²)·(τ 1 + ∑_{l<L} 8 τ(2^l))` |
| `Cslib.Query.cost_minPlusViaNegTri_le_rpow` | the exponent. If `det m` costs at most `c·m^(3−δ)` for `m ≠ 0`, with `c ≥ 0` and `δ ≤ 2`, the product costs at most `544·c·⌈log₂(2W+2)⌉·n^(3−δ/3)` for `n ≥ 1`. So truly subcubic detection gives a truly subcubic product with `δ' = δ/3`, matching the `O(n²·T(n^{1/3})·log W)` of Theorem 4.2 |
| `Cslib.Query.negTriViaMinPlus`, `eval_negTriViaMinPlus`, `cost_negTriViaMinPlus` | the converse in its one-product form: one call of a (min,+) product subroutine decides negative triangle at exactly the cost of that call. With `schoolbookMatMul` this is a cubic detector. It is weaker than [VWW Theorem 4.1][vww18], which reduces negative triangle detection to (min,+) product verification; that reduction is not formalized |

The [tests](../../CslibFrontierTests/NegativeTriangle.lean) run every step with the honest oracle and check the query counts. They also show that the binary search fails when the bound `W` is too small. Finally, they instantiate the exponent bound with the schoolbook detector, `δ = 0` and real weights via `Cslib.FreeM.map_cost`.

Helpers specific to this reduction (`halves`, `octant`, `block`, `maskedBlock`, `markPair`, `blockTriples` and the binary-search steps `bsMid`, `bsQuery`, `bsRounds`, `bsDecode`) live in the namespace `Cslib.Query.NegTri`.

Scope relative to the paper: the weights are `ℤ ∪ {∞}`, with no `−∞` and no general (min,⊙) structure. The paper's `W` is the largest finite weight of the structure, which bounds the inputs, and its product saturates outside `[−W, W]` (footnote 6). Here weights are added without saturation, and `W` bounds the finite entries of the product `A * B`. By `eval_minPlusViaNegTri_of_bounded`, inputs with finite entries in `[−M, M]` give `W = 2M`. The binary search queries the detector with `I`–`J` weights in `[−(W+1), W]`. The output-sensitive listing bound (Theorem 4.3) and the other problems in the class (minimum-weight cycle, replacement paths, metricity, product verification) are not formalized. Neither is a word-RAM realization with bit-length costs, so no statement here concerns subcubic running time on a machine. The statements concern subcubic query cost relative to a detector.

## Depth-first search, topological sort and Bellman–Ford

These are pure Lean functions on adjacency lists, with `TimeM` cost models (as for Kruskal and Edmonds–Karp), not machine programs.

- **Depth-first search.** Import `CslibFrontier.Algorithms.Lean.DFS.Basic` ([source](../../CslibFrontier/Algorithms/Lean/DFS/Basic.lean)). `dfs adj k roots` on `adj : V → List V` visits the roots in turn, with recursion budget `k`; `Fintype.card V ≤ k` suffices. `mem_dfs_visited_iff` and `mem_dfs_finished_iff` say that it discovers and finishes exactly the vertices reachable from the roots. `dfs_finished_order` says that for an edge `u → v` out of a finished vertex, `u` finishes after `v` unless `v` reaches `u`. This is the finishing-time argument in the proof of [Cormen et al., Theorem 22.12][clrs09], which rests on the no-back-edge lemma (Lemma 22.11 there). `time_dfsM` charges one unit per root and one per adjacency-list entry examined. The membership test, insertion and cons are treated as constant-time steps, not charged separately.
- **Topological sort.** Import `CslibFrontier.Algorithms.Lean.DFS.TopologicalSort` ([source](../../CslibFrontier/Algorithms/Lean/DFS/TopologicalSort.lean)). `topologicalSort adj vs` lists the vertices in reverse finishing order. When `vs` lists every vertex, `isTopologicalOrder_topologicalSort_iff` says that the output is a topological order exactly when `Relation.Acyclic (Edge adj)` holds [Cormen et al., Theorem 22.12][clrs09]. `time_topologicalSortM` gives the exact cost `|vs| + ∑ v, |adj v|`.
- **Strongly connected components.** Import `CslibFrontier.Algorithms.Lean.DFS.SCC` ([source](../../CslibFrontier/Algorithms/Lean/DFS/SCC.lean)). `sccs adj vs` runs Kosaraju's two-pass algorithm ([Cormen et al.][clrs09]; see also [Tarjan][tarjan72]): it computes `ord = topologicalSort adj vs`, builds the transpose adjacency lists `transposeAdj adj vs`, and peels DFS trees in `ord` via `peelSCCs`, using the component finishing-time lemma `dfs_scc_finished_order` ([Basic.lean](../../CslibFrontier/Algorithms/Lean/DFS/Basic.lean)). When `vs` covers `V`, `isSCCCondensation_sccs` proves `IsSCCCondensation adj (sccs adj vs)`: the emitted lists are nonempty, duplicate-free across components, cover `V`, equal the `StronglyConnected adj` classes, and appear in forward topological order of the condensation DAG. `time_sccsM_of_nodup` gives exact cost `3 * (|vs| + ∑ v, |adj v|)` on duplicate-free `vs`, and `indexComponents` / `indexComponentsM` build `O(|V|)` topological component indices (`IsSCCCondensation.indexComponents_eq_iff`, `indexComponents_le_of_edge`).
- **Linear-time 2-SAT.** Import `CslibFrontier.Algorithms.Lean.TwoSAT` ([source](../../CslibFrontier/Algorithms/Lean/TwoSAT.lean)). `solve vs φ` and `solveM vs φ` implement the [Aspvall–Plass–Tarjan][aspvallplasstarjan79] 2-SAT algorithm on the implication-graph adjacency lists `implicationAdj φ` by calling `sccsM` and `indexComponentsM` and setting `σ v := decide (compIdx (v, false) < compIdx (v, true))` when no variable shares a component with its negation (`solve_eq_some`, `isSome_solve_iff`, `time_solveM_le`). `solveFin` / `solveFinM` specialize to `CNF (Fin n)` with cost at most `12 * n + 8 * |φ| + 1` (`time_solveFinM_le`), and `solveNat` / `solveNatM` compact binary variable names to decide `Cslib.Complexity.TwoSAT` in `O(|φ.vars| + |φ|)` `TimeM` steps (`isSome_solveNat_iff`, `time_solveNatM_le`). Function-update steps on adjacency and index tables are charged as constant-time operations.
- **Bellman–Ford.** Import `CslibFrontier.Algorithms.Lean.BellmanFord.Basic` ([source](../../CslibFrontier/Algorithms/Lean/BellmanFord/Basic.lean)). Weights may be negative: they lie in a linearly ordered cancellative additive commutative monoid such as `ℤ`. Walks are `Quiver.Path`s, as for Dijkstra's `Instance.dist`. For a list `vs` of all the vertices, `bellmanFord_eq_none_iff` says that the algorithm returns `none` exactly when a negative cycle is reachable from the source. Otherwise `isShortestDist_of_bellmanFord_eq_some` says that each returned value is the least walk weight, or `⊤` with no walk. Together these are [Cormen et al., Theorem 24.4][clrs09] without the predecessor tree. `time_bellmanFordM` gives the exact cost `n + n (n + m)` for `n = |vs|` and `m` adjacency-list entries.

The [DFS examples](../../CslibFrontierTests/DFS.lean) include a triangle and a self-loop, on which topological sort is not a topological order, and the [SCC and 2-SAT examples](../../CslibFrontierTests/SCCAndTwoSAT.lean) check DAGs, cycles, two-component condensation graphs, satisfiable and unsatisfiable 2-CNF instances, and exact tick counts. The [Bellman–Ford examples](../../CslibFrontierTests/BellmanFord.lean) include a negative edge, a reachable negative cycle and an unreachable one, with exact tick counts. Bridges, biconnectivity and Bellman–Ford predecessor trees remain tracked in [#3053](https://github.com/cslib-community/cslib-frontier/issues/3053).

## Continuous metric graphs

Import `CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic` ([Basic.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Basic.lean)), along with [Geodesic.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Geodesic.lean), [Maps.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Maps.lean), [Subdivision.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Subdivision.lean), [Realization.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Realization.lean) and [Bipartite.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/MetricGraph/Bipartite.lean). Public declarations live in `SimpleGraph` and `SimpleGraph.MetricGraph`.

A `SimpleGraph.WeightedGraph V` pairs a connected `SimpleGraph V` with symmetric positive real edge lengths `weight : Sym2 V → ℝ` (`weight_pos`). When `[Finite V]` holds, `MetricGraph W` glues an interval of length `W.weight d.edge` along each dart and turns the quotient into a compact path-connected geodesic `MetricSpace` (`instMetricSpace`, `instCompactSpace`, `instPathConnectedSpace`). Points are constructed by `vertex v` and `edgePoint d t` (`t : unitInterval`), with closed-form distances `dist_vertex`, `dist_vertex_edgePoint`, `dist_edgePoint_vertex`, `dist_edgePoint_edgePoint_same` and `dist_edgePoint_edgePoint_of_edge_ne` expressed through discrete shortest-path distance `SimpleGraph.vertexDist W.graph W.weight` (no running time is charged). `dist_map_le_of_edgePoint_dist_le` deduces global `1`-Lipschitzness out of `MetricGraph W` into any pseudometric space from the per-dart bound along each edge segment.

- **Geodesics and metric intervals.** `IsGeodesic x y γ` characterizes unit-speed shortest paths (`exists_isGeodesic`). The metric interval `interval x y = { z | dist x z + dist z y = dist x y }` consists precisely of points lying on some unit-speed geodesic between `x` and `y` (`mem_interval_iff_exists_isGeodesic`, `exists_isGeodesic_through_of_mem_interval`).
- **Finite subdivisions and per-point breakpoints.** `subdivide W B hV` splits edges at any finite set `B : Finset (MetricGraph W)` containing all original vertices, with a global isometry `subdivideEquiv : MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`. For a fixed point `p`, `pointBreakpoints W p` inserts at most three interior breakpoints per edge (`pointBreakpoints_sdiff_card_le`) so that `τ ↦ dist p (subdivideEquiv hV (edgePoint d' τ))` is affine on every subdivided edge (`dist_subdivide_edgePoint_affine`, `dist_subdivide_edgePoint_affine'`).
- **Straight-edge Euclidean realization.** `realizationSubdivision W` splits each edge into three sub-segments at `realizationPoints W` (`realizationPoints_sdiff_card_le`), and `realizationFromGraph W` (`realizationMap W ∘ (subdivideEquiv _).symm`) gives a closed topological embedding into `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))` (`realizationFromGraph_isClosedEmbedding`) whose Euclidean chord distances induce a globally isometric subdivided graph `realizationEuclideanGraph W` (`realizationMap_edge_dist`, `realizationEuclideanEquiv`). When every edge weight of `W` is rational, every subdivided vertex receives rational coordinates (`realizationMap_vertex_rational`).
- **Equal-length and bipartite graphs.** `equalLength G hconn ℓ hℓ` assigns constant positive edge length `ℓ`. When `G.IsBipartite`, distances from any vertex differ by `ℓ` across every edge (`bipartite_dist_vertex_adj_diff`) and are already affine along every edge without subdivision (`bipartite_const_weight_dist_edgePoint_affine`, `bipartite_equalLength_dist_edgePoint_affine`). For an arbitrary constant-length graph `W`, bisecting every edge via `midpointSubdivision W` yields a bipartite equal-length graph of edge weight `ℓ / 2` (`midpointSubdivision_isBipartite`, `midpointSubdivision_weight_eq`, `midpointSubdivision_dist_edgePoint_affine`).

The [metric-graph tests](../../CslibFrontierTests/MetricGraph.lean) check an asymmetric `Fin 3` triangle (shortcut distances, direct vs. endpoint-detour edge distances, geodesic intervals), non-affineness on equal-length `C_3` vs. exact affineness on bipartite `C_4`, `midpointSubdivision` of `C_3`, breakpoint subdivision bounds, and rational 3-segment Euclidean realization. Note that importing `Bipartite.lean` opens `Mathlib.Combinatorics.SimpleGraph.Metric` inside `SimpleGraph`, where `SimpleGraph.dist` shadows metric `dist`; qualify `Dist.dist` inside `SimpleGraph` when both are in scope. The global two-variable piecewise-linear distance representation on `G × G` is not yet included; it awaits [#4325](https://github.com/cslib-community/cslib-frontier/issues/4325) and remains tracked in [#4324](https://github.com/cslib-community/cslib-frontier/issues/4324).

## Euler circuits in multigraphs

Import `CslibFrontier.Algorithms.Lean.Euler.Circuit` ([source](../../CslibFrontier/Algorithms/Lean/Euler/Circuit.lean)). A finite multigraph is an edge list `H : List (α × α)`, with parallel edges and self-loops allowed, and edges are compared up to orientation through `undirected`. A walk is a vertex list whose edges are its consecutive pairs (Mathlib's `List.consecutivePairs`). `IsEulerCircuit H u w` says that `w` runs from `u` back to `u` and uses every edge of `H` exactly once, in either direction. The degree of a vertex counts endpoints, so a self-loop counts twice.

`exists_isEulerCircuit_iff` is Euler's theorem in this model: an Euler circuit from `u` exists exactly when every degree is even and every edge is connected to `u` (`Relation.EqvGen` of the edge relation, analogous to Kruskal's tree). Unlike the textbook statement for connected loopless graphs, the model allows self-loops and the empty multigraph and ignores isolated vertices. The sufficiency direction is constructive. `eulerCircuit H u` is Hierholzer's algorithm [Hierholzer][hierholzer73] ([Korte and Vygen][kortevygen18], Section 2.4): `walkFrom` follows unused edges greedily, and `walkFrom_spec` shows that it can only stop at the other odd vertex, or back at its start when all degrees are even. `eulerLoop` then splices in closed walks from visited vertices that still have unused edges. `mem_of_isEulerCircuit` says that the circuit visits every vertex connected to its start, and `sum_map_consecutivePairs_eq` that it weighs as much as its multigraph under a symmetric weight. Mathlib's `SimpleGraph.Walk.IsEulerian` covers only simple graphs and only necessity. The list model is what Christofides' algorithm needs, since a spanning tree together with a matching may repeat an edge. No running time is charged.

The [examples](../../CslibFrontierTests/EulerCircuit.lean) run the algorithm on a bowtie (where a second triangle must be spliced in) and on a multigraph with parallel edges and a self-loop. They also refute Euler circuits for a path with odd endpoints and for two disjoint triangles whose degrees are even.

## Counting Eulerian circuits: the BEST theorem

Import `CslibFrontier.Foundations.Combinatorics.Multidigraph.BEST` ([source](../../CslibFrontier/Foundations/Combinatorics/Multidigraph/BEST.lean)). A finite multidigraph is a pair of maps `src tgt : E → V` on a finite arc type, with parallel arcs and loops allowed. `IsEulerianCircuit src tgt e₀ l` says that `l` lists every arc exactly once, starts with `e₀`, and closes up: each arc ends where the next starts, and the last ends where `e₀` starts. This is Stanley's Eulerian tour starting with `e₀` ([Stanley][stanley13], p. 189). `IsInArborescence src tgt r f` ([Arborescence.lean](../../CslibFrontier/Foundations/Combinatorics/Multidigraph/Arborescence.lean)) chooses an arc `f v` out of every `v ≠ r` such that following the chosen arcs leads to `r`. These are the oriented spanning trees rooted at `r`, given by their arcs, so arborescences that differ in a parallel arc count separately.

`natCard_isEulerianCircuit` is the BEST theorem of [van Aardenne-Ehrenfest and de Bruijn][vanaardenneehrenfestdebruijn51] ([Stanley][stanley13], Theorem 10.2). If every vertex has as many outgoing as incoming arcs and at least one outgoing arc, the number of Eulerian circuits starting with `e₀` is the number of arborescences rooted at `src e₀` times `∏ v, (d⁺ v − 1)!`. Stanley assumes a connected balanced digraph, which implies these hypotheses. The proof is his last-exit bijection. The last arcs out of each vertex `v ≠ src e₀` form an arborescence. A circuit is determined by the order in which it leaves each vertex. Every family of orders that starts with `e₀` and otherwise ends with the arborescence arc is realized by the walk that always takes the next arc in order.

`det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence` is the directed matrix-tree theorem for multidigraphs ([Tutte][tutte48]; [Stanley][stanley13], Theorem 10.4, there for connected digraphs). The reduced Laplacian of the arc-count matrix `arcMatrix src tgt R` has determinant equal to the number of arborescences, over any commutative ring. It is derived from `Digraph.det_laplacian_submatrix_eq_finsum_reachable`, the parent-function form of the theorem for weight matrices ([MatrixTree.lean](../../CslibFrontier/Foundations/Combinatorics/Digraph/MatrixTree.lean)). Together they give `natCard_isEulerianCircuit_eq_det_mul` ([Stanley][stanley13], Corollary 10.5). `IsEulerianCircuit.card_filter_src_eq` gives the converse balance condition. The name also credits [Smith and Tutte][smithtutte41], who according to Stanley counted the Eulerian tours of a special class of balanced digraphs. The root independence of the arborescence count for connected balanced digraphs (Corollary 10.3, proved there through the independence of the circuit count from `e₀`) and any polynomial-time counting algorithm are not formalized.

The [examples](../../CslibFrontierTests/BEST.lean) show three counts. The doubled `2`-cycle has `2` Eulerian circuits from a fixed arc, and both are exhibited. A `2`-cycle with a loop has `1`, since the loop does not enter the Laplacian. Two disjoint loops are balanced and have `0`. A loop next to an isolated vertex has one circuit and no arborescence, which shows that the outgoing-arc hypothesis is needed.

## Minimum-cost arborescences: Chu–Liu/Edmonds

Import `CslibFrontier.Algorithms.Lean.Arborescence.ChuLiuEdmonds` ([source](../../CslibFrontier/Algorithms/Lean/Arborescence/ChuLiuEdmonds.lean)). The declarations live in `Cslib.Algorithms.Lean.Arborescence`. The input is a finite digraph `G : Digraph V` with decidable arcs on a `FinEnum` vertex type, a root `r`, and arc costs `c : V → V → β` in a linearly ordered additive commutative monoid such as `ℕ`, `ℤ` or `ℚ`; negative costs are allowed. A spanning in-arborescence (arcs directed towards the root) is represented by its parent function `p`. `IsInArborescenceParent G.Adj r p` says that `p r = r`, that `v → p v` is an arc of `G` for every `v ≠ r`, and that iterating `p` reaches `r` from every vertex. Its cost is `parentCost c r p = ∑ v ≠ r, c v (p v)`. `isInArborescenceParent_iff` identifies these parent functions with the spanning in-arborescences `T ≤ G` of `Digraph.IsInArborescence`, the notion counted by the directed matrix-tree theorem. Both rest on the parent-function API of `CslibFrontier.Foundations.Combinatorics.Digraph.Arborescence` ([source](../../CslibFrontier/Foundations/Combinatorics/Digraph/Arborescence.lean)). There, `Digraph.parentDigraph r p` is the digraph with arcs `v → p v` for `v ≠ r`. `Digraph.isInArborescence_parentDigraph_iff` says it is an in-arborescence iff iterating `p` reaches `r` from every vertex, and `Digraph.IsInArborescence.exists_parentDigraph_eq` says every in-arborescence arises this way.

`edmonds G c r` is the cycle-contraction algorithm of [Chu and Liu][chuliu65] and [Edmonds][edmonds67b]. Every non-root vertex selects a cheapest arc to another vertex. If the selection has no cycle, it is returned. Otherwise a cycle `C` of the selection is contracted onto one of its vertices, keeping the vertex type: arcs into `C` become arcs into that vertex, at the cost of the cheapest arc into `C`. The cost of leaving `C` towards `w` is `min_{x ∈ C} (c x w + ∑_{y ∈ C, y ≠ x} c y (f y))`, where `f` is the selection (`exitCost`, `bestExit`). It needs no subtraction, so `ℕ` costs work. The contracted instance is solved recursively and expanded with `expandParent`. The results are:

- `edmonds_spec`: if `edmonds G c r = some p`, then `p` is a spanning in-arborescence of `G` rooted at `r` and `parentCost c r p ≤ parentCost c r t` for every other one `t`; if it is `none`, there is none.
- `edmonds_eq_none_iff`: the algorithm fails exactly when `G` has no spanning in-arborescence rooted at `r`.
- `edmonds_optimal`: the same optimality over digraphs `T ≤ G` with `T.IsInArborescence r`, measured by the arc cost `arcCost T c`.
- `edmondsOut_spec`: `edmondsOut` handles out-arborescences (arcs `p v → v` directed away from the root, Edmonds' orientation) by reversing arcs and costs.

The proof has two halves. `expandParent_spec` shows that an arborescence of the contracted instance expands to one of the original instance of exactly the same cost. `exists_contract_le` is the exchange argument: every arborescence of the original instance contracts to one of at most the same cost. In it, the vertex of `C` closest to the root keeps its arc out of `C`. Each contraction strictly shrinks the set of vertices with an arc to a vertex other than themselves and the root, so `|V|` levels of recursion suffice. The [examples](../../CslibFrontierTests/ChuLiuEdmonds.lean) run the algorithm by `decide` on a four-vertex digraph whose cheapest arcs `1→2`, `2→3`, `3→1` form a 3-cycle. They also check the same instance with negative `ℤ` costs and in the out-arborescence orientation, a digraph with no arborescence, and a single vertex.

Limitations:

- `edmonds` is executable but not efficient, and no running-time bound is proved. Each recursion level receives the contracted arcs and costs as unmemoised closures over the previous level's. Evaluating them repeats work, so the worst case is exponential in the number of nested contractions. A polynomial version (such as `O(n m)`) needs materialised per-level arc and cost tables. Neither Tarjan's `O(m log n)` implementation nor the Gabow–Galil–Spencer–Tarjan `O(m + n log n)` implementation is formalized.
- The source is [Edmonds][edmonds67b]. His Theorem 1 (stated in §3) asserts a polynomially bounded algorithm for optimum branchings, and §4 gives the algorithm and its proof. The library proves correctness and optimality of that contraction algorithm, specialised to rooted minimum-cost spanning arborescences. It proves neither the polynomial-time content of Theorem 1 nor the branching version (maximum-weight forests). The branching polytope (his Theorem 2) is not formalized.

[#3526](https://github.com/cslib-community/cslib-frontier/issues/3526) tracks the remaining work.

[aspvallplasstarjan79]: ../sources.md#aspvallplasstarjan79
[chuliu65]: ../sources.md#chuliu65
[clrs09]: ../sources.md#clrs09
[edmonds67b]: ../sources.md#edmonds67b
[floyd62]: ../sources.md#floyd62
[hierholzer73]: ../sources.md#hierholzer73
[kortevygen18]: ../sources.md#kortevygen18
[smithtutte41]: ../sources.md#smithtutte41
[stanley13]: ../sources.md#stanley13
[tarjan72]: ../sources.md#tarjan72
[vww18]: ../sources.md#vww18
[tutte48]: ../sources.md#tutte48
[vanaardenneehrenfestdebruijn51]: ../sources.md#vanaardenneehrenfestdebruijn51
