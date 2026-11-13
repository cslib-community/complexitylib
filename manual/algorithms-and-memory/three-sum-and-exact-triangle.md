# 3SUM and Exact Triangle native pipelines

Part of the [representative algorithm endpoints](algorithm-endpoints.md); the conventions and limitations stated there apply to this page.

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
The [parameter client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMExactTriangleDyadicParameters.lean)
evaluates actual code at zero, just below the new threshold and at the threshold. The headline
1.9992 exponent, distinct-position meaning and native resource guarantees below are unchanged.

## Maintaining the per-record product and witness clients

For a prepared record, use `RecordProduct.exec_of_output` or
`RecordBoxProduct.exec_of_output` with the genuine `Instances.Output`. Both concrete
programs derive their source spans through `RecordProduct.producer_readback` in
`CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback`; that pure module
also exposes the record data and ordered query decoder. It needs no initialized product run.

For original headers and signed weights, each adapter's `exec_input` uses
`RecordProduct.prepare_first_input` from
`CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Initialized`.
Its `InitializedFirstRecord` certificate supplies the actual producer run and occupied ordinal
zero. It certifies that selection preserves the producer's memory and that the selected record's
physical window fits. Use `exec_consumer` to append an adapter with its own certified time bound.
Preparation already charges the ordinal-selection instruction. `producer_frame` transfers a
consumer's low-register frame to the original producer
bank. The concrete entry programs, output locations and complete time bounds stay in their
respective `Entry` modules.

Use `RecordProduct.NumericBounds` and `RecordWitness.NumericBounds` for numerical width
and word estimates. The actual all-prefix execution theorems remain in `RecordProduct.SourceBounds` and
`RecordWitness.SourceBounds`, each following from its real `runs_input` theorem.

`RecordBoxProduct.program` uses the physical pointer front
[`PointerBoxProduct.exec`](../../CslibFrontier/Algorithms/WordRAM/MatrixMultiplication/Schonhage/CallableBox/Pointer/Exec.lean).
For a separate caller, initialize its five scalar/header words and appended threshold, supply
raw row-major X/Y pointers and the interleaved query pointer, and prove all three source ends
lie below the private base. The front computes its own virtual width and snapshot layout,
then physically gathers the header and external arrays directly into that snapshot. Physical
pointers occupy registers outside the normalized source bank and may exceed the virtual modulus.
Source/source aliases are permitted when their readback agrees. The private low matrix/query
payload and remaining workspace may be dirty.

The [pointer client](../../CslibFrontierTests/WordRAMSchonhagePointerBox.lean) executes raw binary
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
`CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec` and use
[`BoxProduct.exec_fromSnapshot`](../../CslibFrontier/Algorithms/WordRAM/MatrixMultiplication/Schonhage/BoxProduct/Exec.lean).
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

The [pure readback client](../../CslibFrontierTests/WordRAMExactTriangleRecordReadback.lean)
checks duplicate occurrence order with dirty unused memory. The
[consumer client](../../CslibFrontierTests/WordRAMExactTriangleRecordWitness.lean) checks
success, failure, zero answers and repeated failed candidates. The standalone original
product and witness clients remain available alongside the box clients.

## Box-backed fixed-prime Exact Triangle

To decide whether three signed integer matrices contain a zero-weight triangle, import
`CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime` and use
`StreamingFixedPrime.runs_input`. The complete initialized client is
[the streaming test module](../../CslibFrontierTests/WordRAMExactTriangleStreamingFixedPrime.lean):
it discharges admission, recovers a successful witness, and checks negative exhaustion. The
[general-threshold client](../../CslibFrontierTests/WordRAMExactTriangleFixedPrimeInput.lean)
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

Import `CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime`. For an initialized
call, use `CallableFixedPrime.runs_input` with the same `PreparationInput.input` layout and
geometry/prime premises above, and physical width at least
`CallableFixedPrime.inputWidth n (D m) g p values`. The complete
[initialized client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMCallableBoxFixedPrime.lean)
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
The [dirty caller client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMCallableBoxFixedPrimeCaller.lean)
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

Import `CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting` and open
`Cslib.Algorithms.WordRAM.ExactTriangle`. Use `ParameterSelecting.runs_input_uniform` for a
complete initialized decision. The
[checked client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMParameterSelectingInput.lean)
gives full imports, admitted positive/negative signed cases, empty input, and a symbolic fast
family with the actual selected-prime conclusion. From a checkout containing this endpoint:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMParameterSelectingInput
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

## Selected entries of ranked subset convolution

Chan, Itakura, Ma and Yu (STOC submission 1421, `[ChanItakuraMaYu2026]`) reach integer 3SUM
through selected entries of the ranked subset convolution instead of selected-entries matrix
multiplication. Their Theorem 2.2 is formalized in the unit-cost time monad `TimeM`, not on the
Word-RAM: import `CslibFrontier.Algorithms.Lean.TrimmedYates`, namespace
`Cslib.Algorithms.Lean.TrimmedYates`. The hashing reduction from 3SUM (Theorem 2.3),
Corollary 2.4 and the Section 3 results are in the subsections below; the remaining endpoints of
the submission are open in [#4667](https://github.com/cslib-community/cslib-frontier/issues/4667).

The inputs are look-up functions `f g : Finset ι → R` into a commutative ring, the coordinates
a duplicate-free list `l` of length `d`, and a threshold `s`. `solveM l s f g Cs` runs
`preprocessM` once, which keeps every stage of Yates's passes on the subsets of `l` with at most
`s` elements, and then `queryM` for each query set, which runs the passes only on the subsets
of the query with at least `s` elements and reads smaller sets from the preprocessed stages.
`ret_queryM_preprocessM` proves that a query returns `coveringProduct f g C` whenever
`C ⊆ l.toFinset` and `s ≤ #C`; the identity behind it is
`coveringProduct_eq_subsetMobius` in `CslibFrontier.Foundations.BooleanAnalysis.CoveringProduct`.
For ranked inputs, supported on sets of sizes `t₁` and `t₂`, with `#C = t₁ + t₂`,
`ret_solveM` gives the subset convolutions `subsetConvolution f g C`. `time_solveM` is the exact
tick count `3 (d + 1) (∑_{j ≤ s} (d choose j) + |Cs| ∑_{s ≤ j ≤ 2t} (2t choose j))` for
queries of size `2t`, derived from the program by `time_tabulateM` and `time_stagesM`.

One tick computes one table cell: one input look-up, one product, or one Yates pass at one set
with its dictionary reads. Enumerating cells, building dictionaries and loop control are
uncharged; the module docstring lists the charges. Since the inputs are look-up functions, the
paper's `n` term for storing the input sets does not appear. The
[tests](../../CslibFrontierTests/Algorithms/Lean/TrimmedYates.lean) run `solveM` on `Fin 4` by
kernel reduction, compare the answers and the tick count `210` with `ret_solveM` and
`time_solveM`, and show that covering product and subset convolution differ on unranked inputs.
Check a client with

```bash
lake build --wfail CslibFrontier.Algorithms.Lean.TrimmedYates
lake env lean CslibFrontierTests/Algorithms/Lean/TrimmedYates.lean
```

If `ret_solveM` does not apply, check the support hypotheses `∀ A, f A ≠ 0 → #A = t₁`, that
every query is a subset of `l.toFinset` with `t₁ + t₂` elements, and `s ≤ t₁ + t₂`.

The algorithm is written once for a *scheme of passes* (`Passes`: coordinates, a zeta and a
Möbius pass per coordinate, a grading of the cells and a tick cost per pass at one cell);
`solveM` is the instance `setPasses l` for subsets. A new scheme proves `Passes.Local` (each pass at
a cell reads only cells below it, the grading is monotone, the cells of interest are closed
downwards) and then gets `Passes.ret_solveM` and the exact `Passes.time_solveM`.

### The hashing reduction (Theorem 2.3)

Import `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction`, namespace
`Cslib.Algorithms.Lean.SubsetConvThreeSum`. `threeSumM d t s p seeds A B C` decides `c ∈ A + B`
for every `c ∈ C` (lists of natural numbers) for given random choices: a modulus `p` and a list of
`Seed p` values `(ξ, α, β)`, one per trial. It splits off the elements of `A` and `B` that share
a residue class modulo `p` and lists their sums exactly, then runs `trialM` per seed. A trial
hashes `a ↦ a ξ + α`, `b ↦ b ξ + β` and `c ↦ c ξ + α + β` modulo `p`, keeps the hashes with `t`
(for queries `2 t`) binary digits `1` below `2 ^ d`, and computes six moments per query with one
`solveM` run over `ℤ ^ 6`. The algorithm is `reduceM (fun σ => trialM d t s σ)`: the split, the
bad sums and the error analysis are stated once, for any trial program, in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialReduction`, and shared with the base-`r`
reduction of Theorem 3.4.
The independent-trial counting equality is `card_forall_not` in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Probability`; `card_forall_not_accepts`
is its specialization to subset trials. Both count all-rejecting tuples exactly, including
zero trials, rather than assuming a trial success probability.

- `exists_add_eq_of_mem_ret_threeSumM`: every reported `c` is a sum, for every `p` and all seeds.
- `ret_threeSumM`, `time_threeSumM`: the output and the exact tick count, which depends on the
  random choices through `|A_bad|`, `|B_bad|` and the per-trial `|A*|`, `|B*|`, `|C*|`.
- `miss_le`: for `c = a + b ∈ C`, a prime `p ≥ 2 ^ d` that is good for `c`
  (`4 #falsePairs (2 t choose t) ≤ p - 1`) and `μ` uniform seeds, the miss probability is at most
  `(1 - 3 #P / (4 p ^ 2)) ^ μ` with `#P = (d choose 2 t) (2 t choose t)` (`card_rankedPairs`).
- `average_miss_le`, `card_badPrimes_le`, `two_pow_le_card_primeWindow`: for a uniform prime of
  `[2 ^ d, 2 ^ (d + 1))`, the miss probability is at most
  `#bad / #window + (1 - 3 #P / 4 ^ (d + 2)) ^ μ`, and bad primes are few.

The probabilities are counts over finite uniform sample spaces (`seeds p`, tuples of seeds, the
prime window); sampling is not charged. The [tests](../../CslibFrontierTests/Algorithms/Lean/SubsetConvThreeSum.lean) run
the reduction with `p = 17`, `d = 4`, `t = 1` by kernel reduction and apply
`card_accepts_add_ge` and `miss_le` to a sum with no false pairs. Check with

```bash
lake build --wfail CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction
lake env lean CslibFrontierTests/Algorithms/Lean/SubsetConvThreeSum.lean
```

If `miss_le` does not apply, check that `p` carries a `Fact p.Prime` instance, that `2 ^ d ≤ p`,
and the goodness hypothesis, which is stated for the isolated sublists
`A.filter fun a => decide (Isolated p A a)` and its counterpart for `B`.

### Truly subquadratic integer 3SUM (Corollary 2.4)

This is the balanced case of the corollary. The paper allows unbalanced `A`, `B`, `C` (error
`O(1/N)`, time `O(n̂ ^ 1.965 + N n̂ ^ 0.899 + |C| n̂ ^ 0.965)` with a separate per-query term, and the
3SUM-indexing form); those remain open in ROADMAP. A statement for arbitrary input sizes, choosing
the least `m` with `n ≥` the sizes, is also not formalized.

Import `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Corollary`. `corollary_2_4 κ` gives
`K > 0` and `m₀` such that, for every unit `m ≥ m₀`, every `R` and all duplicate-free `A`, `B` and
any `C` with at most `n = 2 ^ (100 m)` elements below `n ^ κ`, the algorithm
`corollaryM m (budget K m) R A B C qs ωs`:

- costs at most `R (T + n) + n` ticks for every choice of the primes `qs` and seeds `ωs`, where
  `T = budget K m = ⌈20 K n ^ (2 - 1/100)⌉`;
- reports only values `a + b` with `a ∈ A`, `b ∈ B`;
- misses each `c ∈ C ∩ (A + B)` with probability `allFailProb ≤ (1/5) ^ R`.

The parameters (`Params`) are `t = 18 m`, `d = 119 m`, `s = 33 m` and
`μ = ⌊4 ^ (d + 2) / #P⌋ + 1`. Each copy runs the reduction under a step counter of `T` ticks and
is cut off, reporting nothing, if it would exceed it; the counter is not charged. The ingredients
are:

- binomial bounds with integer bases (`Nat.pow_le_succ_mul_choose_mul_pow_mul_pow`,
  `Nat.sum_choose_mul_pow_mul_pow_le_pow`);
- exact expectations: `sum_length_rankedTargets` gives `E |C*|`, and `mul_sum_length_bad_le`
  gives the bad elements summed over the window;
- the expected cost `avgTime ≤ K n ^ (2 - 1/100)` (`exists_avgTime_le`);
- per-copy failure at most `1/20` each from bad primes, from all trials rejecting and from the
  budget (Markov's inequality);
- independence of copies (`allFailProb_eq_pow`).

The exponent is `2 - 1/100`, not the paper's `1.965`, which uses real parameters `γ = 0.2`,
`δ = 0.033`. The [tests](../../CslibFrontierTests/Algorithms/Lean/SubsetConvThreeSumCorollary.lean)
check the binomial and seed counts on small instances. Check with

```bash
lake build --wfail CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Corollary
lake env lean CslibFrontierTests/Algorithms/Lean/SubsetConvThreeSumCorollary.lean
```

### Convolution in `[r]^d` and base-`r` trials (Section 3)

Import `CslibFrontier.Algorithms.Lean.VectorConvolution`, namespace
`Cslib.Algorithms.Lean.VectorConvolution`, for Lemma 3.2 and Theorem 3.3. Vectors are functions
`ι → ℕ` with a duplicate-free list `l` of all coordinates (for `Fin d`, `List.finRange d` with
`List.nodup_finRange` and `List.mem_finRange`), the cube `[r]^d` is the vectors with every
coordinate below `r`, and the size is `∑ i, x i`. `solveM l r s f g Cs` is the trimmed algorithm
for the binomial passes `Cslib.binomPass` (`vecPasses`); the paper's multiplicity-invariant sets in
`[d r]` are replaced by their multiplicity vectors.

- `ret_solveM`: for `f` supported on size `t₁`, `g` on size `t₂` and queries in the cube of size
  `t₁ + t₂`, the answers are `binomConvolution f g C = ∑_{a ≤ C} (∏ i, (C i choose a i)) f a g (C - a)`.
- `ret_solveM_factorial`: with inputs weighted by `vecFactorial`, the answers are
  `vecFactorial C * vecConvolution f g C`, the convolution of Problem 3.1 times a nonzero factor.
- `time_solveM`: exactly `3 (r d + 1)` ticks per cube vector of size at most `s` and per vector
  below a query of size at least `s`. A pass at one vector costs `r` ticks.

The identity behind it is `Cslib.binomTransform_neg_one_mul_eq_binomConvolution` in
`CslibFrontier.Foundations.Combinatorics.BinomialZeta`: in one coordinate it is a finite-difference
identity for `k ↦ (k choose a) (k choose b)`.

For Theorem 3.4, import `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorProbability`.
`vtrialM r d s σ Ag Bg C` is one trial: hashes are read as base-`r` digit vectors (`digitVec`),
queries need a balanced target (each digit `k < r` occurs `d / r` times), and the moments come
from one `VectorConvolution.solveM` run per split of `balancedSize r d`.

- `ret_vtrialM`, `time_vtrialM`: the accepted queries (`VAccepts`) and the exact cost, for
  `s ≤ balancedSize r d`.
- `exists_add_eq_of_vaccepts`: soundness for every modulus and seed.
- `card_vaccepts_add_ge`, `four_mul_card_vaccepts_ge`: for a witness `c = a + b` with isolated
  `a`, `b` and `r ^ d ≤ p`, `#balancedPairs (p - 1) ≤ #accepting seeds + #balancedPairs #L (r !) ^ (d / r)`.

The reduction itself is `vthreeSumM r d s p seeds A B C` in
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorReduction`: the reduction `reduceM` of
`TrialReduction` (split off `A_bad`, `B_bad`, list the bad sums, run one trial per seed), shared
with Theorem 2.3, applied to `vtrialM`. `exists_add_eq_of_mem_ret_vthreeSumM` is one-sided error
for every modulus and all seeds; `time_vthreeSumM` is the exact cost for given random choices;
`vmiss_le` bounds the miss probability of `μ` uniform seeds for a good prime `p ≥ r ^ d` by
`(1 - 3 #balancedPairs / (4 p ^ 2)) ^ μ`; and `vaverage_miss_le` averages over a uniform prime of
`[2 ^ e, 2 ^ (e + 1))` with `r ^ d ≤ 2 ^ e` (the paper uses `(r ^ d, 2 r ^ d]`), with
`card_badPrimesOf_le` bounding the bad primes. The
[reduction tests](../../CslibFrontierTests/Algorithms/Lean/VectorReduction.lean) run it with
`p = 29` and apply `vmiss_le`.

The count of pairs is exact: import
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.BalancedCount` for
`card_balancedPairs` (`#balancedPairs r d = d! / ((d/r)!)^r · (r!)^(d/r)` for `0 < r`, `r ∣ d`;
proved by orbit–stabilizer for the permutations of the `d` positions) and `balancedVecs_eq_empty`
(no balanced vectors when `r ∤ d`). `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorParameters`
uses it to choose the number of trials: with `μ = vTrials k e r d`, computed from `k`, `e`, `r`
and `d` only, `vaverage_miss_le_exp` bounds the miss probability by `#bad / #window + exp (-k)`.
The [count tests](../../CslibFrontierTests/Algorithms/Lean/BalancedCount.lean) compute
`#balancedPairs 3 3 = 36` both ways and instantiate the bound.

`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorDimension` computes all parameters from
the input. `pow_mul_le_card_balancedPairs` bounds `#P ≥ r ^ d (r!)^(d/r) / (d + 1) ^ r` (through
`Nat.pow_mul_pow_factorial_le`, the maximality of the balanced multinomial coefficient), and
`three_mul_vTrials_le` bounds the number of trials from above. `vDim r n L` is `r j` for the least
`j ≥ 1` with `480 (r!)^j n L ≤ (r^(r j) - 1) r^(r j)`, where `n = |A × B|` and `L = log₂ M`;
`twenty_mul_card_badPrimesOf_le` then makes at most `1/20` of the window's primes bad. End to end,
`vaverage_miss_le_vDim` gives miss probability at most `1/20 + exp (-k)` with
`d = vDim r n L`, `e = ⌈log₂ r ^ d⌉` and `μ = vTrials k e r d`, for `r ≥ 2` and
`|a + b - c| ≤ M` on `A × B`. The constants (`480`, `log₂ M`, the binary window) differ from the
paper's, and `d` is defined as a least solution rather than as `2 log_ρ n̂ + O(log log N)`. The
[dimension tests](../../CslibFrontierTests/Algorithms/Lean/VectorDimension.lean) compute `d = 8`
for a small input and instantiate the bound.

For finite cost bounds import
`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorExpectation`.
`sum_length_balancedTargets` gives the exact expected query count from the uniform seed count.
`avg_time_vthreeSumM_le` bounds the actual `TimeM` ticks over a uniform prime and uniform seeds,
for given `r`, `d`, `s`, `μ`, `e`, duplicate-free `A`, `B` below `M`, and `r ^ d ≤ 2 ^ e`.
Its bound is `3 |A| + 3 |B| + |C| + μ G₀ + μ G₁ |C| #balancedVecs / 2 ^ e`, plus the bad-element
term `(|A|² |B| + |A| |B|²) log₂ M / (e #primeWindow)`. Here `G₀` contains the low-cube count and
`G₁` the high-cell binomial sum; their exact expressions are local definitions in the theorem.
The averaging definition `avgTimeOf` and its lemma `avgTimeOf_le` in `TrialExpectation` also serve the
subset reduction, replacing its separate averaging argument. The cost model still leaves
arithmetic, enumeration, dictionary construction and sampling uncharged.
`VectorDimensionBound` gives finite upper bounds from the failed dimension condition at the
preceding index (`pow_two_mul_vDim_le`, `three_mul_vTrials_vDim_le`), without asserting the source
asymptotic formulas. The [expected-cost client](../../CslibFrontierTests/Algorithms/Lean/VectorExpectedCost.lean)
checks a nonempty instance with expected cost at most 161 ticks and the zero-scale dimension case.
Run `scripts/build.sh CslibFrontierTests.Algorithms.Lean.VectorExpectedCost`.

Not formalized: the full multinomial `Θ` estimate, the source asymptotic dimension and trial-count
bounds, the final asymptotic running-time bound with the chosen parameters, its worst-case conversion and
amplification, the choice of `r`, `δ` and `d` for Corollary 3.5, Corollary 3.5 itself, odd k-SUM
(Corollary 3.6), the unbalanced and per-query forms, and Word-RAM realizations. The [tests](../../CslibFrontierTests/Algorithms/Lean/VectorConvolution.lean) run
`solveM` on `[3]^2` and a base-`3` trial with `p = 29` by kernel reduction. Check with

```bash
lake build --wfail CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorProbability
lake env lean CslibFrontierTests/Algorithms/Lean/VectorConvolution.lean
```

If `ret_solveM` does not apply, check the size hypotheses `∀ a, f a ≠ 0 → ∑ i, a i = t₁`, that
every query has all coordinates below `r` and size `t₁ + t₂`, and `s ≤ t₁ + t₂`.

For explicit table sizes, import `CslibFrontier.Algorithms.Lean.VectorConvolution.CostBounds`.
`time_solveM_le` bounds the cost for queries of size `t` and `s ≤ d (r - 1) / 2 - ε` by
`3 (r d + 1) (r ^ d exp (-2 ε ^ 2 / (d (r - 1) ^ 2)) + |Cs| ∑_{j ≤ t - s} (t choose j))`, and
`time_solveM_le_of_le_mul` gives `r ^ d exp (-δ ^ 2 d / 2)` for `s ≤ (1 - δ) d (r - 1) / 2`. The
counts behind them are in `CslibFrontier.Foundations.Combinatorics.CubeCounts`:
`card_cube_sum_le_le` (McDiarmid's inequality for the size of a uniform cube vector, the paper's
Chernoff bound on `H_r(d, ≤ s)`), `card_Iic_filter_le_sum_le` (at most `∑_{j ≤ t - s} (t choose j)`
large vectors below each query, the paper's `H_r(d, t, ≥ s) ≤ binom(t, ≥ s)`) and its entropy form
`card_Iic_filter_le_mul_pow_mul_pow_le`. These are inequalities for every `r`, `d`, `s`; the
paper's asymptotic forms are not stated. The
[tests](../../CslibFrontierTests/Algorithms/Lean/VectorConvolutionCostBounds.lean) compute both
counts on small cases and instantiate `time_solveM_le`. Check with

```bash
lake build --wfail CslibFrontier.Algorithms.Lean.VectorConvolution.CostBounds
lake env lean CslibFrontierTests/Algorithms/Lean/VectorConvolutionCostBounds.lean
```

## Conservative ordinary integer 3SUM

Import `CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Subquadratic`. In namespace
`Cslib.Algorithms.WordRAM.ThreeSum.Decision`, apply `exists_subquadratic_runs κ` to the actual
ordinary host with `ParameterSelecting.callee`. The complete
[checked client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMSubquadraticThreeSum.lean)
includes imports, positive repeated-zero inputs, negative all-one/all-minus-one inputs, and
rejection of two zeros because the positions must be distinct. From an endpoint checkout:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMSubquadraticThreeSum
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

Import `CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.One9992`. In namespace
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
[checked client](../../CslibFrontierTests/ThreeSumOne9992.lean)
shows the semantic interfaces, positive and negative inputs, repeated values at distinct
positions, rejection of an inadmissible magnitude, the charged halt and the same-state
prehalt prefix. The [native visitor client](../../CslibFrontierTests/NativeChanHeVisitor.lean)
checks actual node calls, skipped descriptors and resumption with dirty solver scratch.
From a checkout containing this visitor, run:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.ThreeSumOne9992   CslibFrontierTests.NativeThreeSumDecision CslibFrontierTests.NativeChanHeVisitor
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
`CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing` for initialized execution,
readback, width and resources. Its `PreprocessingExecute` companion supplies
`Preprocessing.afterFrontend_exec` after the frontend, in namespace
`Cslib.Algorithms.WordRAM.ThreeSum.ChanHe`. This standalone producer remains separate from
the ordinary visitor. Ordinary clients use `Decision.exec_input` or `Decision.runs_input`;
they need no snapshot, cursor or individual-stage contracts. The lower-level
[`Decision.exec_large`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/Execute.lean)
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
[`Visitor.exec_consume`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorCall.lean).
The return frame preserves every cell below `H`, including the current packed block, pending
heavy arrays, native stack and frontend descriptors. Arbitrary higher scratch may be dirty
and can be reused. The polynomial value envelope bounds signed values and arithmetic width;
it does not supply a workspace address.

The proof composition keeps the original construction-state emission and the actual call's
register/prefix frames. It transports only the live child and pending-source views needed for
the next iteration. Root initialization is shared with the standalone catalogue producer through
[`Traversal.initializeRoot_exec`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalInitialize.lean).

The prefix frame is a return-state guarantee, not a ban on transient callee writes.
After consuming the node, one actual copy sets the committed heap to its packed pointer.
[`VisitorRelease`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorRelease.lean)
proves that all heavy children and pending ancestor columns end below that released frontier.
The packed block, residue workspace and histogram tail can be overwritten by later construction;
the copy itself changes no memory cells. Persistent heavy-buffer allocation remains monotone,
and the old table gap stays reserved.

The actual
[`Visitor.live_transition`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorTransition.lean)
postcondition gives final committed heap equal to the body's initial heap plus
`3 + len(column0) + len(column1) + len(column2)`; skipped bodies leave it unchanged.
The three count cells and full heavy-buffer capacities remain allocated. The discarded tail
has `len(column0)+len(column1)+len(column2)+4*N+M` words, where `N` is the common group count
and `M` is this node's selected modulus. These are native body storage equalities, not a bound
on arbitrary callee scratch or touched high-water memory. The existing polynomial word/support
envelope remains unchanged; no improved total-space bound is claimed.

The [native fixture source](../../CslibFrontierTests/NativeChanHeVisitor.lean) includes an initial
heap of 100 with expected final frontiers 106 for one live node and 115 for the two-node
branching case. It also overwrites a released packed cell after the actual child pushes and
checks an empty heavy column whose pointer equals the frontier. The build command above checks
these local cases alongside the endpoint clients; they are not asymptotic-space measurements.

The [actual automatic callee](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ExactTriangle/ParameterSelecting/Callee.lean)
executes parameter computation, prime selection and the real box-backed calls. Its integer
parameters and the reason for their constants are explained below; the parameter `n` there
is the ET dimension, rather than the original 3SUM length.
The [parameter boundary client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMExactTriangleDyadicParameters.lean)
checks the actual VM at zero, below `2^2394` and at `2^2394`;
the [automatic Exact Triangle client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMParameterSelectingInput.lean)
checks symbolic fast-family executions, including the selected-prime conclusion. These huge
matrix clients are proof witnesses, not execution benchmarks. Small ordinary-input VM checks
also reject lengths below three. The complete finite ledger charges preprocessing, selector,
global original-weight scan reserve, matrix preparation, every box call, outer control and
halt. Polynomial logarithmic factors are absorbed before the ordinary reduction is applied.

The intermediate native Exact Triangle bound is `Oκ(n^(3-33/20000)) = Oκ(n^2.99835)`;
this does not claim the source Exact Triangle exponent 2.9983. The final
[ordinary theorem and source mapping](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ThreeSum/Decision/One9992.lean)
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

The [runtime module](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/Runtime.lean)
connects these statements to the actual `Decision.cost`:
`Pκ(n) + 4*E + 32 + q*(Host.callerTime(...)+12)`, where
`E = Decision.envelopeExponent κ`. The fixed reserve includes setup and halt; the caller
term includes matrix construction and every ET invocation. The passed magnitude is
`F = 2*(n+2)^E+1`. `ChanHe.packed_weight_le` bounds it by `(s+2)^(2*E+2)`, so an ET theorem
for polynomial weights applies at the actual side `s`.

The Convolution consumer alone costs `Host.callerTime(...)+7`. The one-copy packed-tail
release makes the traversal's callback-and-release charge `Host.callerTime(...)+8`.
[`Visitor.cost_ledger`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorCost.lean)
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
`CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Runtime`. In the `Decision` namespace,
`exists_cost_bound` takes a concrete `Host.Callee r`, `0 < δ <= 1`, a target exponent
`a > 2-δ/2`, and its proved uniform polynomial-weight time bound `Oκ(n^(3-δ))`.
It derives the full ordinary `Decision.cost` bound `Oκ(n^a)`, retaining native preprocessing,
actual packed dimensions and emitted-node counts, matrix/callee calls, control and halt. The
constant and threshold precede all original inputs and admitted physical widths.

Import `CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Transfer` for
`exists_runs_of_callee_time`, which adds the complete initialized execution, distinct-position
verdict, same-state prefix/halt and every-wide polynomial word/support guarantees. These generic
modules import no particular ET supplier. Their quantitative premise must be proved for actual
code; it is not an execution or time oracle for the final algorithm. For ordinary use of the
canonical implementation, apply `exists_one9992_runs` directly and supply only the original
input magnitude and physical-width premises described above.

The canonical callee uses `δ = 33/20000`. Both `a = 2499/1250` and the older conservative target
`a = 2-1/5184` satisfy the strict inequality, so both endpoint proofs reuse this same transfer
and concrete solver. The [ordinary client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/ThreeSumOne9992.lean)
and [conservative client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMSubquadraticThreeSum.lean)
check the resulting concrete run/resource contracts. From a checkout containing this revision:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.ThreeSumOne9992 CslibFrontierTests.WordRAMSubquadraticThreeSum
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

The [parameter family](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/ExactTriangle/ParameterChoice.lean)
chooses `g=4^(2b)`, `m=63b`, `D=4^m`, and the existing box tensor depth `L=21m`.
The product balance is the small integer inequality `4*125 <= 63*8`, or `500 <= 504`;
`63b` also satisfies the box tradeoff's divisibility by nine.
The stronger reserve `D^19 <= n` requires `2394*b <= floor(log2(n))`, because
`2394 = 2*63*19`. This gives `b=floor(log2(n)/2394)`.
The [cost-geometry lemmas](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/ExactTriangle/ParameterChoice/CostGeometry.lean)
prove the conditions and `n^3/g <= 16*n^(3-2/1197)`, retaining integer rounding.

The raw saving `2/1197` is not yet a full runtime exponent. The
[finite coefficient](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/Complexity/Algorithms/WordRAM/ExactTriangle/DyadicCost/Asymptotics.lean)
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
