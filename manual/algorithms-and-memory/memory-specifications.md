# State transitions, memory, refinement, and callable implementations

## Relational operations and adaptive clients

[StateTransitionSpec](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition.lean#L95) gives a state type, operation type, dependent result type, valid-operation predicate and relational step. A specification need not be deterministic or total; those are separate properties. A priority-queue insertion may choose any fresh handle and an extract-min may choose any tied minimum [complexitylib][complexitylib].

`Client` is a typed free program whose next operation can depend on the previous result. `DemonicValid` requires every continuation to remain valid for every allowed result. `ClientRun` records an actual permitted path and transcript. Totality turns demonic validity into existence of a run. `ofFn` specializes a deterministic transition function; `toLTS` and `toFLTS` connect with upstream transition-system interfaces.

A client charge sums explicitly chosen operation weights. Pure Lean work in the continuation is uncharged. An abstract client bound therefore measures interaction with the supplied backend, not total machine time. Refinement packages an invariant, abstract-state map and lower-level method programs; composition transports correctness and cost bounds. [Complexity/DataStructure/StateTransition/Amortized.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition/Amortized.lean) adds potential-based telescoping.

## Randomized and oblivious interfaces

[RandomizedSpec](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/StateTransition/Randomized.lean#L98) supplies a PMF stateful handler. Support induces the relational specification, while `withCoins` allows clients their own samples. `RandomizedRefinement` requires the exact output/state law, not just a relation between possible outcomes. `run_link` transports this law through adaptive clients. `ExpectedAmortized.client` and `.comp` telescope expected lower-level costs plus potential and compose refinement layers. Until-bad rules transport explicit error bounds when exact equality is unavailable.

[Complexity/DataStructure/ObliviousSequence.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/ObliviousSequence.lean) instead accepts a fixed finite operation list and constrains its joint typed transcript law. It is deliberately state-free at the interface and nonadaptive. A theorem over all lists chosen before the random seed does not allow a client to choose the next query after observing random outputs. The hash-family and hash-table headline theorems use this boundary explicitly.

## Word memory as an oracle

[Complexity/DataStructure/Memory/Spec.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Memory/Spec.lean) has total memory `Nat → Nat`, a monotone allocation frontier and word width. Reads/writes must address allocated cells; values/frontier must fit. Zeroed allocation charges `k+1` for a `k`-cell block in its abstract currency, whereas dirty allocation charges one and retains previous cell contents. There is no automatic deallocation or reuse. `Memory.Prog` uses the same free-program client syntax.

The native allocation library [Complexity/Computability/WordRAM/Allocation.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Allocation.lean) implements zero-fill, frontier allocation and indexed access as ordinary Word-RAM programs. Zero-fill costs `4*k+2` instructions, zeroed allocation `4*k+7`, and indexed read/write two instructions. These are different currencies from the abstract memory-oracle weights, joined by explicit realizations rather than definitionally equated.

## Dynamic calling conventions and native controllers

[DynamicProgram](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Dynamic.lean#L84) packages one structured operation program and output register with an input-register mask, operation encoding and result decoder. Delivering arguments preserves maintained memory; the operation code is fixed across calls. This layer leaves encoding/argument delivery/decoding uncharged, while actual operation instructions and halt are counted. Initialization is a separate hypothesis. A failed interpreter/decoder is distinct from a successful operation whose result is `Option.none`.

`DynamicCertificate` supplies representation, fitting bounds and successful-run certificates, exporting a reusable state-transition implementation and an instruction bound. A native caller can close the remaining convention: [Refines](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Controller.lean#L61) relates an admissible abstract client to actual structured RAM execution. Binding requires one continuation code that handles all answers, and `call` charges native argument preparation. This stops arbitrary Lean continuation computation from becoming free machine computation.

[Realizes](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Realization/Basic.lean#L95) is a graded realization interface. It chooses scratch registers, a constant and a uniform code emitter **before** arguments, width and memory. It requires faithful register encodings, a whole-memory/frontier abstraction, register framing and explicit safety/work bounds. Its instruction allowance is proportional to `memoryCost + work + 1`. The `work` term is necessary because pure/control code can take time without making memory queries. `Realizes.exists_refines` connects it to the native controller layer. Primitive, bind and branch modules provide a compositional foundation, not a compiler for every arbitrary Lean function.

## Footprints, traces, and memory windows

[HeapAssertion](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Heap.lean#L62) records a finite support and a predicate on total memory. Separating conjunction uses disjoint supports; `Modifies` records agreement outside an allowed write set. This is an explicit-footprint frame calculus inspired by separation logic, not a replacement semantics in which inaccessible cells disappear [reynolds02][reynolds02].

[Complexity/Computability/WordRAM/Trace.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Trace.lean) decorates actual executions with address/value reads and writes. `TraceExec.exec` erases the trace; `Exec.exists_trace` supplies one for every ordinary execution; trace length is bounded by instructions. These are access costs of a fixed RAM computation. They are not a general cell-probe model allowing arbitrary uncharged local computation.

[Complexity/Computability/WordRAM/MemoryWindow.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/MemoryWindow.lean) compiles standard code to a caller-owned region with three extra registers. Loads use address addition, load and normalization; stores use addition and store. `view` clips dirty memory to the source width. No bulk zeroing is silently inserted, and the view is a relation on ordinary RAM states, not another execution machine. Signed pairs and multiword banks similarly implement representations inside the ordinary instruction model.

## Retroactive rebuilding

[Complexity/DataStructure/Retroactive/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/DataStructure/Retroactive/Basic.lean) edits a timeline, resets the backend and replays the entire edited history. Admissibility rechecks the whole history because an insertion/deletion can invalidate later operations. The realized bound includes editing, reset and replay; the edit primitive must pay for storing/exposing the changed list. Pure client computation remains uncharged, and no fixed Word-RAM compiler is supplied there. This is a proved rebuilding transformation, not an efficient rollback or historical-query data structure.

## Known Limitations

The survey checks the semantic and charging boundaries of the interfaces and representative clients. It does not certify all data-structure implementations or all possible refinements. In particular, a theorem about a memory charge, amortized abstract operation count or oblivious transcript cannot be silently promoted to a total native runtime or an adaptive randomized guarantee.

[complexitylib]: ../sources.md#complexitylib
[reynolds02]: ../sources.md#reynolds02
