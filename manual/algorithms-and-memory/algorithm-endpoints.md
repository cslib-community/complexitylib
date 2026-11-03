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

## Hash families and dictionaries

[abstracts/ComplexityAbstracts/HashTablesAbstract.lean](../../abstracts/ComplexityAbstracts/HashTablesAbstract.lean) selects four expected-amortized dictionary implementations: multiply-shift chained hashing, five-wise linear probing, odd-stride uniform probing and cuckoo hashing. Each supports `query` and `insert` with overwrite, up to bounded distinct-key capacity. **Deletion is not included.** The operation list is fixed before initialization randomness; these are oblivious-sequence guarantees.

The initializer and operation programs are independent of runtime word width and base address, but their dependence on capacity/universe differs by theorem. The abstract does not bound static program-list length. Executed steps exclude caller argument preparation/dispatch. Universe restrictions include the chosen exponent-four polynomial regime; load-factor assumptions and exact initialization costs are visible. These distinctions prohibit a blanket claim of fully dynamic adaptive constant-time dictionaries.

[abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/HashFamiliesAbstract.lean) gives high-independence hashing with an explicit regime switch at capacity `2^320000`. Below it, finite-field polynomial hashing supplies exact k-wise independence; above it, fixed-parameter double tabulation has a high-probability transcript coupling, with an explicit condition under which the error bound becomes nontrivial. Queries per resampling epoch are restricted to at most `k` distinct keys. Programs may depend on `(k, capacity, universe, outputWidth)`; static code size is not bounded.

Across capacities the stated space is at most `(k+9232)*(capacity+1)` words, evaluation at most `111230*k+6862` instructions, and resampling at most `(5*k+46096)*(capacity+1)`. These constants are theorem bounds, not measured runtime or a practical implementation recommendation. The large-regime construction adapts Thorup's double-tabulation work; its fixed-k error statement is explicitly different from the source's original growing-independence asymptotic formulation [thorup13][thorup13].

## Global minimum cut

[abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean) treats weighted undirected multigraphs, `n≥2`, fitted total doubled edge weight and word widths sufficient for workspace/trial counters. A single contraction trial is one fixed 16-register program: `42*n²+12*n+21` worst-case instructions and at most `n-2` random calls, always returning a genuine nontrivial cut value. When minimum cut is positive, it succeeds with probability at least `2/(n*(n-1))`.

The Karger–Stein endpoint uses one fixed 24-register program, `O(n² log n)` worst-case steps and `O(n²)` matrix scratch per tree, with success at least `1/(floorlog₂(n)+15)`. Repetition gives minimum-cut **value** with failure at most `1/(2n)` in `O(n² log³ n)`. It does not enumerate all minimum cuts or attain the source's sparse-space formulation. The threshold is an integer inequality rather than a literal square-root expression; the abstract labels the implementation and proof adaptations.

## Other clients and classification

The source tree also contains native integer arithmetic, multiword circuit evaluation, matrix multiplication, primality/counting, predecessor structures, 3SUM/exact-triangle routines and randomized SAT algorithms. These broaden coverage of the machine library; they should be catalogued through the complete module census without counting each as a new model. In particular, a bounded frontend or a conditional transfer theorem should not be presented as completion of an unresolved fine-grained endpoint. The current `ROADMAP.md` and selected abstracts are better evidence of endpoint disposition than a directory name.

## Automatic native Exact Triangle solver

Import `Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting` and open
`Cslib.Algorithms.WordRAM.ExactTriangle`. Use `ParameterSelecting.runs_input_uniform` for a
complete initialized decision. The
[checked client](https://github.com/cslib-community/complexitylib/blob/233b273f3b0853557cf9dfb43493053e948b70cc/ComplexityTests/WordRAMParameterSelectingInput.lean)
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
halt are charged. The uniform initialized bound is `ParameterSelecting.callerTime n F`, already including
the header and halt reserve of 16.
Its fast body allowance retains all three component budgets plus 26; the small allowance
uses actual exhaustive code. No supplied solver, run, prime, layout or time law is required.

For an existing ordinary host, `ParameterSelecting.callee` supplies `ThreeSum.Host.Callee 633`:
633 scratch registers give 640 total, arguments 0–5 are restored and Boolean 6 is returned.
Its semantic execution permits arbitrary unused old words. Caller prefix-resource rules
separately require their original raw-word bound; arbitrary old memory is not asserted zero.
For initialized polynomial magnitudes `F <= (n+2)^κ`, `inputWidth_le_log` gives width at most
`(12332*(κ+9)+40)*clog₂(n+2)`, and `bounded_reachable_polynomial` bounds every admitted wider
prefix's words and zero support by `(n+2)^(12332*(κ+9)+41)`.

This is standard unit-instruction Word-RAM execution for signed integer matrices. It is not a
bit-time or arbitrary-real theorem. The large-family client is a checked symbolic run, not an
enormous interpreter benchmark. This conservative automatic component is distinct from the
later box-backed ordinary 1.9992 endpoint in [PR #2358](https://github.com/cslib-community/complexitylib/pull/2358).

## Conservative ordinary integer 3SUM

Import `Complexity.Algorithms.WordRAM.ThreeSum.Decision.Subquadratic`. In namespace
`Cslib.Algorithms.WordRAM.ThreeSum.Decision`, apply `exists_subquadratic_runs κ` to the actual
ordinary host with `ParameterSelecting.callee`. The complete
[checked client](https://github.com/cslib-community/complexitylib/blob/2f6fb39d034b8a27ddcd56dd7779b67ef9a236b9/ComplexityTests/WordRAMSubquadraticThreeSum.lean)
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
3SUM. Its conservative exponent is `2-1/5184`; the sharper box-backed 1.9992 theorem is the
separate [PR #2358](https://github.com/cslib-community/complexitylib/pull/2358).

## Tree Evaluation

The [Cook–Mertz endpoint](catalytic-and-tree-evaluation.md) computes the root of an explicitly table-encoded perfect binary tree in native independent workspace `O(log n · log log n)` for positive value length and height. The output is not charged to workspace, and the theorem leaves time existential. The same page distinguishes borrowed-register restoration and fan-in/packed procedure variants.

## Known Limitations

The numeric values above are transcriptions of checked source statements, not results of new execution benchmarks. The source-reference audit checks locations and digests; it does not rerun Lean or prove asymptotic summaries. The full Haskell/Lean runtime behavior, allocator, operating system and hardware are outside these idealized RAM models.

[complexitylib]: ../sources.md#complexitylib
[thorup13]: ../sources.md#thorup13
