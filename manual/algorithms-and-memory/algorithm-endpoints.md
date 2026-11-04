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

[abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean](../../abstracts/ComplexityAbstracts/FibonacciHeapAbstract.lean) specifies bounded-capacity handles, bounded key/value ranges, fresh-handle insertion and arbitrary minimum ties. Initializer/operation code is chosen before capacity/key/value/base/width parameters. The amortized total is constant per ordinary operation plus a sum of logarithms of current size for extract-min. Fresh zeroed memory permits constant-time initialization; the reusable-memory version explicitly clears the region and costs linear time. Both theorems execute demonically admissible adaptive clients (`Client`, whose continuations observe returned handles and extracted entries); external argument preparation, result decoding and pure host continuation choices between `p_op` calls are uncharged.


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

## Approximate membership filters

Import `Complexity.DataStructure.ApproximateMembership.WordRAM.QuotientFilter` ([Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter.lean](../../Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter.lean)) and construct `QuotientFilter.implOfEps` (for target error `ε ≠ 0` via `epsLog ε`) or `QuotientFilter.impl` (for dyadic error `(1 / 2) ^ k`); see [ComplexityTests/WordRAMQuotientFilter.lean](../../ComplexityTests/WordRAMQuotientFilter.lean) for a complete checked client and [abstracts/ComplexityAbstracts/ApproximateMembershipAbstract.lean](../../abstracts/ComplexityAbstracts/ApproximateMembershipAbstract.lean) for the self-contained formal abstract.

The specification `ApproximateMembership.spec U n ε` enforces strict set validity on active set `S` (`insert u` requires `u ∉ S ∧ #S < n`; `delete u` requires `u ∈ S`; `query u` is always valid) and guarantees zero false negatives on every random branch together with per-absent-query false-positive probability at most `ε` across any fixed valid operation sequence. The constructors require key bit-width `0 < w₀`, word width `2 * w₀ ≤ w` (needed to bit-pack remainders and derive `quotBits w₀ n < w`), universe bound `U ≤ 2 ^ w₀`, memory fit `base + QuotientFilter.space w w₀ n (epsLog ε) < 2 ^ w`, and zeroed owned memory `[base, base + QuotientFilter.space w w₀ n (epsLog ε))` with `qfReg 240 = base`. The single allocated block uses `QuotientFilter.space w w₀ n (epsLog ε) ≤ 640 * ((n * epsLog ε + w - 1) / w + 1)` words, and initialization takes `QuotientFilter.setupSteps w₀ n` expected body instructions. The randomized hash (`ReducedKWise`) and pure bit-packed layout accessors (`SlotArray`) are implemented as low-level primitives. The deterministic cluster navigation, scan, and shift phases in [Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter/Cluster.lean](../../Complexity/DataStructure/ApproximateMembership/WordRAM/QuotientFilter/Cluster.lean) are authored as `QuotientFilter.clusterOpProg : ClusterInput → Memory.Prog ℕ` and lowered via the `realize` tactic (`realizes_clusterOp.code`). Each operation charges at most `QuotientFilter.charge = opStepBound 290 = O(1)` expected executed body instructions, excluding the final `halt` step and caller argument delivery in `qfReg 1` and `qfReg 247`. Compiled programs `p_init` and `p_op` depend on `(w, w₀, n, ε)` with no static code-size bound.

## Global minimum cut

[abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/KargerMinCutAbstract.lean) treats weighted undirected multigraphs, `n≥2`, fitted total doubled edge weight and word widths sufficient for workspace/trial counters. A single contraction trial is one fixed 16-register program: `42*n²+12*n+21` worst-case instructions and at most `n-2` random calls, always returning a genuine nontrivial cut value. When minimum cut is positive, it succeeds with probability at least `2/(n*(n-1))`.

The Karger–Stein endpoint uses one fixed 24-register program, `O(n² log n)` worst-case steps and `O(n²)` matrix scratch per tree, with success at least `1/(floorlog₂(n)+15)`. Repetition gives minimum-cut **value** with failure at most `1/(2n)` in `O(n² log³ n)`. It does not enumerate all minimum cuts or attain the source's sparse-space formulation. The threshold is an integer inequality rather than a literal square-root expression; the abstract labels the implementation and proof adaptations.

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

When composing another proved record product with the existing verifier, use
`RecordWitness.exec_after_product` from `RecordWitness.AfterProduct`. Supply its actual
execution, actual output offset, exact signed matrix-product answers, outside-window memory
frame and all producer registers below 65, including ordinal register 64. The theorem invokes
`exec_consume` and retains its scan-dependent charge, original-coordinate witness and query
occurrence. The concrete original and box endpoints discharge this premise internally;
their public statements do not acquire a solver assumption. Keep their `19*m` and `21*m`
geometry, threshold instructions and admission proofs separate.

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
it discharges admission,
recovers a successful witness, and checks negative exhaustion. The standalone all-record
`FixedPrime.runs_input` and its existing client remain available.

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
`runs_input`. `StreamingFixedPrime.time_le_old` places every streaming charge, including halt,
within this old conservative envelope; that reference is never asserted for a reused slot. Its complete finite bound retains preparation, aggregate box charges,
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
[checked client](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/ThreeSumOne9992.lean)
shows the semantic interfaces, positive and negative inputs, repeated values at distinct
positions, rejection of an inadmissible magnitude, the charged halt and the same-state
prehalt prefix. On that source revision, run:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.ThreeSumOne9992
```

The native constructor `Decision.program κ solver` accepts only the finite callee code;
`Decision.flatProgram` assembles its halt. The canonical solver argument is
`ParameterSelecting.program`. Correctness and time certificates refer to that same syntax,
so evaluating it does not require evaluating proof-only resource metadata. There is no
separate `Decision.Code` import or duplicate `programOfCode` assembly.

For the preprocessing proof, import `Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing`
for initialized execution, readback, width and resources. Import its `PreprocessingExecute`
companion to use `Preprocessing.afterFrontend_exec` for the suffix after the frontend, in
namespace `Cslib.Algorithms.WordRAM.ThreeSum.ChanHe`. The setup and iteration companions
contain private stage proofs; callers need no snapshot, cursor or individual-stage contracts.

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

The caller places matrix workspace at the final preprocessing heap frontier `H`, copied by an
executed register instruction. The preprocessing
[output-layout contract](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalOutput.lean)
places the pointer-table endpoint and every live payload endpoint at or below `H`.
Each solver call preserves memory below `H` on return, so the caller can still read every
remaining instance. The separately computed polynomial envelope bounds signed values and
arithmetic width; it no longer determines the workspace address.
Preprocessing may have touched dead temporary scratch above `H`, which the solver can reuse.
This layout contract describes live output and a final-state frame, without asserting a ban
on transient callee writes. The existing polynomial prefix bounds still apply.

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
| Native preprocessing `Pκ(n)` | `Kκ*(n+2)*(sqrt(n+2)+1)*ell^13` | `Preprocessing.cost_bound` |
| Catalogue allowance `q` | `128*(κ+2)^2*ell^7` | `Decision.instanceBound_le_numBound` |
| ET side `s` | `Oκ(sqrt(n)*ell^2)` | `ChanHe.packed_side_le` |
| One Convolution call, including outer control | `2*s*T(s,F)+355*s^3` | `Decision.callerTime_add_twelve_le` |

The [runtime module](https://github.com/cslib-community/complexitylib/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ThreeSum/Decision/Runtime.lean)
connects these statements to the actual `Decision.cost`:
`Pκ(n) + 4*E + 32 + q*(Host.callerTime(...)+12)`, where
`E = Decision.envelopeExponent κ`. The fixed reserve includes setup and halt; the caller
term includes matrix construction and every ET invocation. The passed magnitude is
`F = 2*(n+2)^E+1`. `ChanHe.packed_weight_le` bounds it by `(s+2)^(2*E+2)`, so an ET theorem
for polynomial weights applies at the actual side `s`.

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
actual packed dimensions and catalogue counts, matrix/callee calls, control and halt. The
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

## Tree Evaluation

The [Cook–Mertz endpoint](catalytic-and-tree-evaluation.md) computes the root of an explicitly table-encoded perfect binary tree in native independent workspace `O(log n · log log n)` for positive value length and height. The output is not charged to workspace, and the theorem leaves time existential. The same page distinguishes borrowed-register restoration and fan-in/packed procedure variants.

## Known Limitations

The numeric values above are transcriptions of checked source statements, not results of new execution benchmarks. The source-reference audit checks locations and digests; it does not rerun Lean or prove asymptotic summaries. The full Haskell/Lean runtime behavior, allocator, operating system and hardware are outside these idealized RAM models.

[complexitylib]: ../sources.md#complexitylib
[thorup13]: ../sources.md#thorup13
