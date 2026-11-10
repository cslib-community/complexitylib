# State transitions, memory, refinement, and callable implementations

## Relational operations and adaptive clients

[StateTransitionSpec](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition.lean#L95) gives a state type, operation type, dependent result type, valid-operation predicate and relational step. A specification need not be deterministic or total; those are separate properties. A priority-queue insertion may choose any fresh handle and an extract-min may choose any tied minimum [cslib-frontier][complexitylib].

`Client` is a typed free program whose next operation can depend on the previous result. `DemonicValid` requires every continuation to remain valid for every allowed result. `ClientRun` records an actual permitted path and transcript. Totality turns demonic validity into existence of a run. `ofFn` specializes a deterministic transition function; `toLTS` and `toFLTS` connect with upstream transition-system interfaces.

A client charge sums explicitly chosen operation weights. Pure Lean work in the continuation is uncharged. An abstract client bound therefore measures interaction with the supplied backend, not total machine time. Refinement packages an invariant, abstract-state map and lower-level method programs; composition transports correctness and cost bounds. [CslibFrontier/DataStructure/StateTransition/Amortized.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition/Amortized.lean) adds potential-based telescoping.

For a deterministic specification, `clientResult`, `clientState` and `clientHistory` give the
answer, final state and operation history of a client run. To split them at the binds of a `do`
block, use `simp only [client_simps]` instead of rewriting with `clientState_bind` and its
relatives by hand. The simp set also splits `totalCost` and `ValidHistory` of the history at the
state where the first client stops, and, with `WordRAM.Realization` imported, `memoryCost`. It
does not unfold individual operations: add their step lemmas yourself. See the
[client-splitting regressions](../../CslibFrontierTests/StateTransitionClientSimps.lean), which
cover a generic specification and `Memory.spec w`.

For deterministic methods, import `CslibFrontier.DataStructure.StateTransition.LinkCongr` to
use `StateTransitionSpec.runClient_link_congr` when replacing methods under an adaptive client.
Its premise equates each complete method run at every starting state and operation: answer,
final state and lower-operation history. The linked client retains all three. This transports
semantics; native call and argument-staging costs need their own realization. Open the complete
[linked-run clients](../../CslibFrontierTests/StateTransitionLinkCongr.lean): `linked_write_read`
preserves changed memory and history, while an extra-read counterexample shows why equal
answers and final states alone do not preserve the charged history.

## Randomized and oblivious interfaces

[RandomizedSpec](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition/Randomized.lean#L98) supplies a PMF stateful handler. Support induces the relational specification, while `withCoins` allows clients their own samples. `RandomizedRefinement` requires the exact output/state law, not just a relation between possible outcomes. `run_link` transports this law through adaptive clients. `ExpectedAmortized.client` and `.comp` telescope expected lower-level costs plus potential and compose refinement layers. Until-bad rules transport explicit error bounds when exact equality is unavailable.

[CslibFrontier/DataStructure/ObliviousSequence.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/ObliviousSequence.lean) instead accepts a fixed finite operation list and constrains its joint typed transcript law. It is deliberately state-free at the interface and nonadaptive. A theorem over all lists chosen before the random seed does not allow a client to choose the next query after observing random outputs. The hash-family and hash-table headline theorems use this boundary explicitly.

### Cell-probe state-transition and oblivious-sequence implementations

Import [`CslibFrontier.DataStructure.CellProbe.StateTransition`](../../CslibFrontier/DataStructure/CellProbe/StateTransition.lean), [`CslibFrontier.DataStructure.CellProbe.Randomized.StateTransition`](../../CslibFrontier/DataStructure/CellProbe/Randomized/StateTransition.lean), and [`CslibFrontier.DataStructure.CellProbe.Randomized.ObliviousSequence`](../../CslibFrontier/DataStructure/CellProbe/Randomized/ObliviousSequence.lean) to connect `Cslib.CellProbe` schemes ([query and communication complexity](../circuits-logic-and-other-models/query-and-communication.md#adaptive-cell-probe-trees-and-schemes)) to `StateTransitionSpec` and `ObliviousSequenceSpec`. Persistent state between operations lives solely in `Mem cells w` (`cells` words of `w` bits, with no persistent registers); reads and writes cost one probe each, while local computation and private coin draws cost zero probes.

- `CellProbe.StateTransitionImpl D P s₀` certifies a deterministic `CellProbe.Scheme` with potential-amortized probe charge `charge`, projecting via `toBaseImpl`, `toAmortized`, and (when `potential = 0`) `toBound` over `ExecOp P` to adaptive `D.Client` bounds (`run_client_amortized`, `run_client_bound`) and multi-step `P.runSeq` / `P.seqProbes` bounds (`runSeq_amortized`, `runSeq_ofFn`), with cell-count monotonicity `padCells`.
- `CellProbe.Randomized.StateTransitionImpl D P s₀` couples `Randomized.Scheme` execution with a latent `Seed` (`seedSlack * seedLaw`), `CoupledState` / `CoupledOutcome` marginals, and an addition-only `ℝ≥0∞` amortized-in-expectation probe inequality (`seq_expected_amortized`, `seq_expected_amortized_ofFn`), lifting deterministic implementations via `toRandomized` and projecting to `CellProbe.Randomized.ObliviousSequenceImpl` via `toObliviousSequenceImpl`.
- For **zero-error (Las Vegas)** schemes on deterministic specifications (`[D.HasStepFn f]`) against oblivious sequences (bounded-error Monte Carlo schemes and adaptive sequence adversaries are out of scope), `CellProbe.Randomized.exists_det_indexedScheme_le_expectedSeqProbes` and `StateTransitionImpl.le_expected_totalCost_of_det_indexedScheme` package the **averaging (easy) direction of Yao's principle** over an explicit finite `opsAlphabet : Finset D.Op` and `horizon : ℕ` (separating `correctSeqs` from `hardDist`, so infinite operation types such as `Dictionary.Op U` need no `[Fintype]` instance). Because per-step coin fixing returns a step-indexed `IndexedScheme` (the **time-aware relaxation** with a free step clock outside cell memory), any deterministic cell-probe lower bound paired with it must hold against step-indexed `IndexedScheme`s; in the **random initial memory / coin-free steps** specialization (`IsCoinFree`), `exists_det_scheme_le_expectedSeqProbes` and `StateTransitionImpl.exists_det_scheme` return a time-invariant `CellProbe.Scheme` without `opsAlphabet` or `horizon`.

Open the complete [checked client](../../CslibFrontierTests/DataStructureCellProbe.lean) for a non-zero-potential 2-bit binary counter (`4` probes on carry vs. amortized charge `3`), a worst-case direct-mapped `Dictionary.spec` instance, a randomized 2-key dictionary combining a uniform initial swap seed with per-query coin flips, zero-error coin-fixing over non-`Fintype` `Dictionary.Op 2`, and a `3 / 2` probe lower-bound transfer check across arbitrary `cells` and `w`. Run `scripts/build.sh --wfail --iofail CslibFrontierTests.DataStructureCellProbe`. Word-RAM-to-cell-probe simulation bridges follow separately; these modules do not by themselves transfer cell-probe lower bounds to Word-RAM instruction counts.

## Word memory as an oracle

[CslibFrontier/DataStructure/Memory/Spec.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Memory/Spec.lean) has total memory `Nat → Nat`, a monotone allocation frontier and word width. Reads/writes must address allocated cells; values/frontier must fit. Zeroed allocation charges `k+1` for a `k`-cell block in its abstract currency, whereas dirty allocation charges one and retains previous cell contents. There is no automatic deallocation or reuse. `Memory.Prog` uses the same free-program client syntax.

The native allocation library [CslibFrontier/Computability/WordRAM/Allocation.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Allocation.lean) implements zero-fill, frontier allocation and indexed access as ordinary Word-RAM programs. Zero-fill costs `4*k+2` instructions, zeroed allocation `4*k+7`, and indexed read/write two instructions. These are different currencies from the abstract memory-oracle weights, joined by explicit realizations rather than definitionally equated.

## Dynamic calling conventions and native controllers

[DynamicProgram](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Dynamic.lean#L84) packages one structured operation program and output register with an input-register mask, operation encoding and result decoder. Delivering arguments preserves maintained memory; the operation code is fixed across calls. This layer leaves encoding/argument delivery/decoding uncharged, while actual operation instructions and halt are counted. Initialization is a separate hypothesis. A failed interpreter/decoder is distinct from a successful operation whose result is `Option.none`.

`DynamicCertificate` supplies representation, fitting bounds and successful-run certificates, exporting a reusable state-transition implementation and an instruction bound. A native caller can close the remaining convention: [Refines](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Controller.lean#L61) relates an admissible abstract client to actual structured RAM execution. Binding requires one continuation code that handles all answers, and `call` charges native argument preparation. This stops arbitrary Lean continuation computation from becoming free machine computation.

[Realizes](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Realization/Basic.lean#L95) is a graded realization interface. It chooses scratch registers, a constant and a uniform code emitter **before** arguments, width and memory. It requires faithful register encodings, a whole-memory/frontier abstraction, register framing and explicit safety/work bounds. Its instruction allowance is proportional to `memoryCost + work + 1`. The `work` term is necessary because pure/control code can take time without making memory queries. `Realizes.exists_refines` connects it to the native controller layer. Primitive, bind and branch modules provide a compositional foundation, not a compiler for every arbitrary Lean function.

### Retain resources through a dependent bind

Import `CslibFrontier.Computability.WordRAM.Realization.Bind` and use
`Realizes.Witness.bind` when a continuation consumes a runtime answer and you need to
retain concrete code and resources. It keeps the predecessor’s answer live while sharing its
dead auxiliary registers with the continuation. With `l` answer words and component scratch
sizes `n₁`, `n₂`, its scratch size is `l + max n₁ n₂`; the factor remains the maximum
component factor. The original safe-domain and valid-history obligations still apply at the
actual intermediate state. `Witness.bind_execWithin` can tighten the two component execution
budgets on that same code and add them, retaining the full memory, output and register frame.
A new sequential constructor over the same `bindSharedLeft`/`bindSharedRight` layout gets both
stages' register premises from `bindShared_layout`, as `RealizesRand.Witness.bind` does.

The complete checked [dependent-read client](../../CslibFrontierTests/WordRAMRealizationBindScratch.lean)
reads a pointer and then its target using one supplied emitter. Its generic Backend has five
registers, compared with six for the former disjoint-bank layout, and executes two loads;
argument installation and halt are separate. The client checks a maximum fitting payload,
a zero pointer, aliased input registers and an unallocated second address that fails the
original history condition. For probabilistic clients, use the joint-law data route below.
For supplying its data to a Backend, follow
[Retain concrete realization resources](wordram-and-bridges.md#retain-concrete-realization-resources).

### Retain a randomized joint law

Import `CslibFrontier.Computability.WordRAM.Realization.Random` and retain a
`RealizesRand.Witness` when you need the supplied scratch, factor and code for a client with
private coins. Its `code_spec` is the same `RealizesRand.Spec` used by the existential
`RealizesRand` judgment: every supported path obeys the time and draw budgets, and the result
words together with the entire memory/frontier have the specified joint law. Erasure by
`Witness.toRealizesRand` supplies the existing judgment but does not identify a later
classically selected emitter with your supplied one.

Compose `RealizesRand.coinWitness`, deterministic `Realizes.Witness.toRand` and
`RealizesRand.Witness.bind`. Deterministic entry retains the same code/resources with zero
draws; a coin uses the existing unit-cost inclusive native `rand` on `[0, upper]`,
including one charged draw when `upper = 0`. This is not a fair-bit sampler.
Bind retains the shared bank described above. Its continuation domain and time/draw ceilings
must hold for **every supported answer and memory state**, and its native contract must handle
every bounded scratch state. Correlation with predecessor scratch is not a new independence
premise. Use `code_spec` on the chosen layout to retain its concrete resource evidence.

The complete [supplied randomized client](../../CslibFrontierTests/WordRAMRealizationRandomWitness.lean)
samples a word, writes it to a runtime address and reads it back. One six-register emitter
replaces the disjoint layout's seven registers; its certified body bound is six instructions
and at most one `rand` call. A four-outcome distribution checks that the returned word and
written cell are correlated, with the rest of memory/frontier framed. Zero upper bound,
aliased inputs and invalid continuation history are also checked. Input delivery/installation
and halt remain separate. The existing existential flat-program export is available for its
own admitted inputs; this supplier adds no randomized Backend and proves no fixed Karger
register count or numerical clock.

### Export a canonical initialized flat program

Import `CslibFrontier.Computability.WordRAM.Realization.Program.Standard` when you have a
`Realizes .exact` certificate and want one flat program with a fixed register layout.
The [canonical exports](../../CslibFrontier/Computability/WordRAM/Realization/Program/Standard.lean)
choose the program, frontier register, result bank, halt location and constant factor before
runtime word width and input. You supply the encoding and admissibility proofs; the exports
supply the register placement and disjointness proofs.

Choose the conclusion your client needs:

- `Realizes.exists_standard_init_program_state_from_words` lets the raw memory list vary
  independently of the register-encoded argument. Use it when a small argument controls an
  operation on a larger input already in memory. The first `k` raw words must agree pointwise
  with the `k` encoded argument words.
- `Realizes.exists_standard_init_program_state` specializes that rule to a chosen `raw d`
  list for each argument `d`. It retains the actual final native state, complete memory and
  frontier, every encoded result word, and the fixed halting location.
- `Realizes.exists_standard_init_program` projects the same run to scalar `Executes` at a
  fixed result coordinate `i : Fin l`. Use the state variant when a later proof needs memory
  or other result coordinates. Zero-output Unit clients use the separate Unit-observation
  exports in [Program](../../CslibFrontier/Computability/WordRAM/Realization/Program.lean).

For each runtime input, prove `k ≤ words.length`, `Fits w (words.length + 1)`,
`InputFits w words`, the certificate's `safe w d (inputState words)` condition, and
`Memory.spec`'s `ValidHistory` for that client from `inputState words`. The raw-words rule
also requires the prefix equality described above; the other two take that equality for
`raw d` when choosing the program. The resulting instruction bound is
`C * (memoryCost + work + 1) + 1`, including the executed prefix, body and halt.
If an application fails, check the prefix, fit, safe-domain and history obligations before
changing the program or dropping a premise. Even an empty input needs `Fits w 1`; these
exports do not initialize at word width zero.

`Data.init` places the raw input list in memory by the existing **uncharged calling
convention**. The charged native prefix takes at most `2*k+5` instructions to install the
frontier and the first `k` argument registers while preserving memory. It does not construct
or copy the whole graph or other raw-memory input. Work used to obtain that initial input
requires a separate bound if the surrounding application charges it.

Open the complete checked
[StandardProgram clients](../../CslibFrontierTests/WordRAMRealizationStandardProgram.lean),
including their imports, encodings and premises, for a starting point.
`writeRead_native` uses the state export for a write followed by a read, with a concrete
maximum-fitting payload `15`; `emptyInput_native` uses the scalar export and exposes the
positive frontier-fit premise. `graphHeader_native` uses the raw-words export with a Unit
register argument and actual Dijkstra adjacency-list encodings. One program handles two
different graphs, reads their first header word and preserves the entire input memory.
This client is a header-read demonstration, not a Dijkstra execution or shortest-path bound.

## Footprints, traces, and memory windows

### Call fixed code in a disjoint register bank

Import `CslibFrontier.Computability.WordRAM.Call` when the callee already has a native execution
proof and the caller must prepare arguments and consume the result. `ExecWithin.call` takes
an injective register embedding, a charged preparation, the callee's execution and
postcondition, and a charged continuation. The continuation sees the callee postcondition
on its register bank and equality of every register outside that bank. Memory assertions
refer to the actual returned memory. The total allowance is `tPrep+tCall+tCont`; register
renaming emits no instructions.

The complete [fixed-call client](https://github.com/cslib-community/cslib-frontier/blob/4b571e0f55c64471a95728d28955f3532ed9329f/ComplexityTests/WordRAMCall.lean)
delivers an argument, calls a routine that increments it and writes memory, then retrieves the
result in five charged instructions. It proves that an unrelated register and other memory
cells survive, even when unused old words exceed the physical word bound. This rule does not
add a whole-state boundedness or finite-footprint premise to the supplied callee theorem.
If a call proof fails, check the embedding's injectivity, the callee's actual preconditions,
and the registers the continuation needs to preserve. A memory frame belongs in the callee's
postcondition; register disjointness alone says nothing about its writes.

From a checkout containing this API, check the client with
`scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMCall`.
The ordinary 3SUM visitor's
[`Visitor.exec_consume`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorCall.lean)
uses the same rule for its Convolution host. Actual copies deliver the current node's packed
pointer and allocation endpoint; the complete traversal register bank and lower live prefix
survive the call, while higher scratch may be dirty. This permits pending heavy arrays to be
used after the call without publishing or reading a packed-pointer catalogue.

The subsequent
[`Visitor.exec_releasePacked`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorRelease.lean)
executes one copy from the actual packed pointer to the heap register, making the dead packed,
residue and histogram tail reusable. The memory function is unchanged by that copy. Heavy-buffer
capacities and count cells remain below the committed frontier, whose persistent allocation
advances monotonically; the old reserved gap remains too. Keep the `Emission` witness anchored
at the construction state before the consumer call: its `heap_eq` describes the complete node
endpoint. `construct_consume` returns that state, both charged executions and the actual
callee register/prefix frames. Transport the live stack and child arrays through those frames;
the continuation needs no reconstructed packed-array readback after consumption.
Use `release_frontier` and `release_children_ends` with the retained emission and register frame
for the smaller released frontier and actual child arrays. The visitor's body storage equality is in
[`live_transition`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorTransition.lean);
it does not bound total space or arbitrary callee high-water scratch.
For a renamed execution without a surrounding preparation and continuation, use
`Exec.rename_post` or `ExecWithin.rename_post`. They return the postcondition on the callee
bank and the unchanged outside registers; the first retains an exact instruction count.

The Chan–He traversal's record helpers are another `Exec.rename_post` client.
[`Traversal.WordStack.pushRecord_exec` and `popRecord_exec`](https://github.com/cslib-community/cslib-frontier/blob/8609e5ae206693e3c35a920ba2cf24ef76135d26/Complexity/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalStack.lean#L225)
move a fixed register bank through the traversal's own nine-register word stack in exactly
`9*n+1` and `14*n+1` instructions. They are local to the hand-stepped traversal, not a library
stack API; the library's bounded stack is `Stack.Memory`, run natively by `Stack.Native`.

Both root controllers reuse
[`Traversal.initializeRoot_exec`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalInitialize.lean).
It proves the actual four setup instructions and seven-word root push in 68 instructions,
with exact stack readback and the stack write frame. `Exec.rename_post` lifts this same prefix
into the visitor's register bank. The catalogue and visitor loops then establish their own
output invariants; neither caller supplies a root-prefix execution as an assumption.

### Reuse routine postconditions and register frames

For a proved native routine, keep its whole postcondition when calling
`ExecWithin.rename_post`; consume only the named fields needed by the continuation.
For example, [`ArrayCopySum.Post`](../../CslibFrontier/Computability/WordRAM/CopySum.lean)
records the resulting memory, retained source/destination/length and accumulated sum.
Its memory and sum facts refer to the original input state, so a caller can use `post.memory`
and `post.total` without reconstructing register extensions or a positional tuple.
The actual source/destination separation and numerical fit premises still belong to the
routine. This is the same charged execution; the postcondition emits no instructions.

[`WordRAMProcedureContracts`](../../CslibFrontierTests/WordRAMProcedureContracts.lean) is a
complete ordinary-import client. From the repository root, run
`scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMProcedureContracts`.
It checks the real copy routine, including dirty destination words and its frame;
use its full imports and premises when adapting a call. If transport fails, check the bank's
injectivity and distinguish facts about the source view from protected caller registers.

For a contiguous bank, import
[`CslibFrontier.Computability.WordRAM.RegisterFrame`](../../CslibFrontier/Computability/WordRAM/RegisterFrame.lean)
and use `Code.preserves_rename_of_offset`. Supply the equation
`(bank j).val = offset + j.val` and the outside interval premise
`i.val < offset ∨ offset + sourceRegisters ≤ i.val`.
`Exec.regs_eq` or `ExecWithin.regs_eq` then gives the protected register equality for the actual
execution. This works with arbitrary basis and register counts; an enumerated map can supply
its offset equation once. For a sparse map, `Code.preserves_rename_of_forall_ne` protects a
register outside the bank image, given `∀ j, bank j ≠ i`.

For a preserved register inside an injective bank, first prove the routine's own
`h : code.Preserves i`. Then `Code.preserves_rename hf h`, with `hf : bank.Injective`, gives
`(code.rename bank).Preserves (bank i)`. Apply `Exec.regs_eq` or `ExecWithin.regs_eq` to obtain
the actual register equality. The native visitor's
[`Visitor.oneRoot_preserves`](../../CslibFrontier/Algorithms/WordRAM/ThreeSum/Decision/VisitorRoot.lean)
uses this shared rule for saved preprocessing controls. If this step fails, check the source
routine's preservation fact and injectivity separately; being inside the bank requires that
source fact, while the outside-image and offset rules retain their existing uses.

The complete [register-frame client](../../CslibFrontierTests/WordRAMRegisterFrames.lean)
copies inside an interior bank in one instruction and retains dirty registers on both sides
and arbitrary memory. Its negative control checks that an owned destination can change.
Run `scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMRegisterFrames`.

### Pay variable native loop work with a ghost potential

Import
[`CslibFrontier.Computability.WordRAM.GhostLoop`](../../CslibFrontier/Computability/WordRAM/GhostLoop.lean)
and use `ExecWithin.loop_potential_state` for a native loop whose body paths have different
charged costs. Choose proof state `σ`, a relation `I : σ → Data r → Prop` and a natural-valued
potential `μ : σ → ℕ`. For every `s` and `x` satisfying `I s x` and the actual loop
condition, supply a successor `s'`, native state `y` and charge `t` with
`ExecWithin W body x y t`, `I s' y` and `t + 2 + μ s' ≤ μ s`.
The two extra units pay that iteration's loop control. The conclusion executes the fixed native
loop within `μ s + 2`, preserves the final relation and establishes that its condition is false;
the final two units pay the exit. Proof state and potential insert no machine instructions.
The body premise still requires execution of the actual code, including its fit and memory
obligations. The uniform-body `loop_invariant_state` rule remains available.

The complete [checked client](../../CslibFrontierTests/NativeGhostPotential.lean) includes its
`GhostLoop` import, phase relation and actual branch executions. Its counter follows
`1 → 2 → 0`, with body costs two and four. Ghost potentials `10 → 6 → 0` pay those bodies and
loop control, yielding a twelve-step loop bound; the evaluator independently checks that exact
clock and preserved dirty memory. From the repository root, run
`scripts/build.sh --wfail --iofail CslibFrontierTests.NativeGhostPotential`.
If the potential inequality fails, include each branch's actual cost and both control units;
if execution fails, resolve the native body or invariant premise before changing its charge.

### Derive word admission from a numerical envelope

Import [`CslibFrontier.Computability.WordRAM.Admission`](../../CslibFrontier/Computability/WordRAM/Admission.lean)
for the scalar bridge from binary ceiling logarithms to `Fits W v`, meaning `v < 2^W`:
`fits_of_clog_lt` admits an envelope `B` when `Nat.clog 2 B < W`;
`fits_of_lt_clog_le` admits `v < B` when `Nat.clog 2 B ≤ W`.
Prove the algorithm-specific envelope bound once, then use `Fits.of_le` for smaller values and
`Fits.mono` for larger widths. These sufficient rules do not infer memory separation,
old-word bounds, or workspace geometry.

The strict endpoint matters: width three holds seven but not eight, even though
`Nat.clog 2 8 = 3`. For the envelope itself retain a spare bit. The complete
[admission client](../../CslibFrontierTests/WordRAMAdmission.lean) checks these boundaries with
actual native constant instructions and includes width zero.
Run `scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMAdmission`.
If admission fails, check whether the intended value is strictly below the envelope or is the
envelope, then check the original value bound; do not replace a strict premise by a non-strict one.

### Use an explicit memory frame

[HeapAssertion](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Heap.lean#L62) records a finite support and a predicate on total memory. Separating conjunction uses disjoint supports; `Modifies` records agreement outside an allowed write set. This is an explicit-footprint frame calculus inspired by separation logic, not a replacement semantics in which inaccessible cells disappear [reynolds02][reynolds02].

[CslibFrontier/Computability/WordRAM/Trace.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Trace.lean) decorates actual executions with address/value reads and writes. `TraceExec.exec` erases the trace; `Exec.exists_trace` supplies one for every ordinary execution; trace length is bounded by instructions. These are access costs of a fixed RAM computation. They are not a general cell-probe model allowing arbitrary uncharged local computation; for adaptive `w`-bit cell-probe trees and randomized cell-probe schemes (`Cslib.CellProbe`), see [query and communication complexity](../circuits-logic-and-other-models/query-and-communication.md#adaptive-cell-probe-trees-and-schemes).

[CslibFrontier/Computability/WordRAM/MemoryWindow.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/MemoryWindow.lean) compiles standard code to a caller-owned region with three extra registers. Loads use address addition, load and normalization; stores use addition and store. `view` clips dirty memory to the source width. No bulk zeroing is silently inserted, and the view is a relation on ordinary RAM states, not another execution machine. Signed pairs and multiword banks similarly implement representations inside the ordinary instruction model.

## Retroactive rebuilding

[CslibFrontier/DataStructure/Retroactive/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Retroactive/Basic.lean) edits a timeline, resets the backend and replays the entire edited history. Admissibility rechecks the whole history because an insertion/deletion can invalidate later operations. The realized bound includes editing, reset and replay; the edit primitive must pay for storing/exposing the changed list. Pure client computation remains uncharged, and no fixed Word-RAM compiler is supplied there. This is a proved rebuilding transformation, not an efficient rollback or historical-query data structure.

## Known Limitations

The survey checks the semantic and charging boundaries of the interfaces and representative clients. It does not certify all data-structure implementations or all possible refinements. In particular, a theorem about a memory charge, amortized abstract operation count or oblivious transcript cannot be silently promoted to a total native runtime or an adaptive randomized guarantee.

[complexitylib]: ../sources.md#complexitylib
[reynolds02]: ../sources.md#reynolds02
