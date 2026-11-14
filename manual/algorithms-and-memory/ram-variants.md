# Natural, generic, and exact algebraic RAM

## Unbounded natural registers

[CslibFrontier/Computability/RAM/Defs.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Defs.lean) defines `Cslib.RAM` over the upstream URM register store. Registers hold arbitrary natural numbers; inputs occupy the initial registers, the remainder starts at zero, and register zero is the output. Instructions include constants, addition, truncated subtraction, multiplication, indirect loads/stores and a positive branch. Falling past the program list halts; subsequent clocked runs stutter. A partial evaluator and relational execution are linked by determinism and run/evaluation correspondence [cslib-frontier][complexitylib].

This is an adaptation of Cook–Reckhow-style RAM, not a literal copy: its data are naturals rather than integers, multiplication is supplied, and the initial register input is a convention rather than charged finite-alphabet I/O. Those choices matter before comparing complexity classes [cookreckhow73][cookreckhow73].

[CslibFrontier/Computability/RAM/Cost.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Cost.lean) makes the charge function explicit. `unitCost` assigns one to a step, while `logCost` uses bit lengths of relevant operands/addresses; `bitLength 0 = 1`. `HaltsWithResultInTime` and `ComputesInTime` quantify costed successful runs. `RAM/Input` adds explicit input encodings and preparation programs when a comparison needs to charge them.

The cost distinction is witnessed by [repeatedSquaring](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/RAM/Squaring.lean#L74), an eight-instruction program computing `2^(2^k)`. `time_unitCost_repeatedSquaring` gives its exact unit-step cost. `two_pow_lt_of_computesInTime_logCost` and `exists_mul_pow_lt_of_computesInTime_logCost` force exponential output-bit-length cost under the logarithmic convention and rule out each polynomial bound in `k`. The result is a concrete warning against treating unit-cost unbounded multiplication as ordinary bit computation.

## Generic partial-operation RAM

[Model](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Defs.lean#L64) supplies types of values, addresses and configurations; literal syntax; operation/test signatures; partial evaluation; partial address extraction; produced-value admissibility; move validity; and control-label validity. The shared interpreter supplies finite registers, indirect total memory, program counter, explicit halt and a separate fault outcome.

Separating literal syntax from values lets an instance restrict program constants; the generic `Const` type and its interpretation remain arbitrary. The natural/rational restriction belongs to the algebraic instances below. Partial address extraction makes conversion to an address explicit and allows it to fail; the chosen model supplies that conversion. The generic interpreter itself chooses neither binary encodings nor an implementation of primitive operations. Unit-step semantics and `Executes.unique` establish deterministic execution for a chosen interpretation, not effective computability of all interpretations.

Word-RAM maps into this core step for step. `WordRAM.step_toGeneric`, `run_toGeneric` and `executes_toGeneric_iff` preserve its concrete semantics. This is more than a resemblance between definitions: it permits generic execution metatheory to be reused without changing instruction counts.

## Exact algebraic instances

[CslibFrontier/Computability/GenericRAM/Algebraic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Algebraic.lean) uses tagged values `Nat ⊕ K`. Only the natural arm can address memory. A width bounds natural words and control labels by `2^w`; exact field values are not bounded that way. Word arithmetic faults on overflow/underflow or zero divisor; field division by zero faults. There is a word-to-field conversion and no reverse conversion, floor, square root or transcendental operation.

Literal symbols are natural words or rationals. A rational denominator that maps to zero in positive characteristic faults. `Algebraic.real` adds exact real comparison and noncomputable mathematical semantics; `Algebraic.primeField` uses executable prime-field arithmetic and equality without an order test on the field arm. Both use the generic one-instruction currency.

The local documentation maps the real instance to Erickson–van der Hoog–Miltzow §6.1. Its tagged single memory differs from that source's separate word/real arrays, and checked arithmetic differs from modular word arithmetic. The primary source explicitly distinguishes finite word addresses from exact real storage; the formalization's modifications should remain visible [erickson24][erickson24]. No bit-cost or exact-real Turing implementation is asserted.

## Native representation and sparse memory

[CslibFrontier/Computability/GenericRAM/Native.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Native.lean) introduces `Model.Encoding` and `Model.NativePrimitives`. Each value/address/configuration encoding is faithful, and scalar operations, tests, literal checks and validity conditions receive native certificates. Configuration and operands are runtime inputs. The source instruction is fixed for the scalar certificate, so constants may depend on the fixed source program.

`NativeCertificate` records an actual finite machine with independent time, workspace and encoded-output-size bounds. These are ingredients for a simulator, not a blanket theorem that every generic RAM is efficient.

[CslibFrontier/Computability/GenericRAM/SparseMemory/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/SparseMemory/Basic.lean) represents memory by a default value and finite association list. The encoded object is that finite representation, not the mathematical total function. [CslibFrontier/Computability/GenericRAM/Simulation/Turing.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/GenericRAM/Simulation/Turing.lean), `Simulation/Run` and `Simulation/Degree` compile the finite transition and iterate it with explicit costs. Initialization and extracting an answer remain additional obligations. The Word-RAM specialization discharges those obligations with fitting word widths and a chosen step budget.

## Allocating pointer-machine foundation

Import `CslibFrontier.Computability.PointerMachine.Abstract` for `Cslib.PointerMachine`.
This is the compact definition file, with no correctness proofs.
`PointerMachine.Basic` supplies invariants and resource bounds; `PointerMachine.Reference`
contains the private allocation representation. Unlike the retired formal abstracts,
`Abstract` defines the model itself, so no duplicate definitions or bridge are needed.
`Model k` specifies finitely many data sorts, their carrier types, and named binary
operations and predicates with typed arguments and results. `Layout k` fixes the
number of pointer registers and fields and the number of data registers and fields
of each sort. The model, layout, and finite instruction list are fixed independently
of input size. A many-sorted signature is our way of making the source's type
restrictions explicit; the paper does not present a formal dependent type system.

`State M L` keeps references separate from data. References identify records through
`NodeId`; neither arithmetic nor conversion to or from data is a machine instruction.
Data instructions contain operation symbols from `M`, whose interpretations are fixed
by the model. An operation receives only its typed data arguments, not references or
the heap. This makes the scalar basis an explicit parameter rather than an implicit
choice of natural arithmetic. General interpretations are mathematical functions;
executable or bit-efficient interpretations require additional evidence.

Pointer registers and fields distinguish undefined contents, null, and a reference
to an allocated node. Data registers and fields similarly distinguish undefined
contents from a datum. Allocation creates one fresh record with all fields undefined.
A load or store through null does nothing except advance control. Using undefined
contents, dereferencing an unallocated node, or applying an undefined primitive
faults. The fault convention makes unsuccessful behavior explicit; it is not an
additional successful output. Defined values can overwrite undefined destinations.
Control labels are zero-based; falling outside the finite code faults, and explicit
`halt` succeeds with the final registers and heap as output.

`State.Valid` requires each defined, nonnull register pointer and every defined link
in allocated storage to name an allocated node. It allows cycles, sharing, and
unreachable allocated records. Applications supply valid input states, with preparation cost separate;
`Runs.valid` preserves that hypothesis.
`State.empty` supplies an empty graph. The provenance and validity results are
independent of the chosen data operations: a resulting pointer must be copied from
an existing register, loaded along a field of a node addressed by a register, or
returned by fresh allocation. No arithmetic operation can create a reference.

`Runs` reuses CSLib's `Relation.RelatesInSteps`; `Executes` also charges the final halt.
Each instruction costs one unit, including a data primitive or an allocation.
`size` counts initially allocated records plus allocations, including unreachable
records. There is no deletion or implicit garbage collection. `Runs.size_le` bounds
allocated records by initial records plus continuing steps. These are instruction
and record measures, not bit-time, bit-space, or host allocation costs. Changing the
primitive signature changes what one instruction can accomplish.

For a symbol-only sort, its carrier type alone does not establish opacity: an
operation `Symbol → Int` would reveal an encoding. The protected-symbol instance
is `Symbols.model` from `CslibFrontier.Computability.PointerMachine.Symbols`.
It permits copying, loading, storing, and equality of symbols, with arithmetic
restricted to separate integer slots. It supplies no symbol literal, packing
operation, conversion, or symbol-producing primitive. Abstract symbols and integer
counters can therefore coexist in one fixed-format record, as they do in Tarjan's
weighted-union example. Symbol preservation and renaming properties express this
restriction separately from pointer provenance.

After the [standard setup](../workflows/getting-started.md), check the
[typed clients](../../CslibFrontierTests/PointerMachine.lean) with
`lake build CslibFrontierTests.PointerMachine --wfail --iofail`.
They exercise abstract symbols, numerical metadata, and references in the same
machine, with exact instruction accounting and boundary cases for allocation,
undefined contents, and null access. The clients are model examples, not a verified
union-find implementation or lower bound.

GenericRAM was assessed for reuse: its `evalOp` receives only register operands and
fixed configuration, and `Data.mem` has no allocation state. Its `admissible` and
`validMove` checks cannot consult a changing heap. Tagging values and restricting
`address` would prevent scalar address conversion but would not establish provenance
or fresh allocation. The pointer-machine module supplies its own small-step
instruction semantics while reusing the common exact-step relation and its resource
lemma. It introduces no second recursive run interpreter. A common control engine or
certified GenericRAM lowering would need a separate semantic preservation argument.

The inspected source is [Tarjan 1979](https://doi.org/10.1016/0022-0000(79)90042-4),
§2, pp. 111–112: separate data/pointer registers and fields, identical record layouts,
explicit-reference access, binary data operations and predicates, fresh allocation
with undefined fields, null-access no-ops, and one unit per instruction. The finite
sort index and typed operation families make these conventions explicit. Zero-based
labels normalize its one-based labels. The semantics also defines faults for code
fall-through and invalid or undefined uses; §2 requires a final halt but does not
fully specify undefined-value evaluation. No claim of a step-exact translation of
every source program, or of equivalence with pure atomistic SMM/KUM models, is made.

Tarjan's union-find application adds assumptions (3.1)–(3.5), pp. 113–114. Element and
set identities are equality-only symbols; the initial memory is separated by sets;
and each invocation resets other registers and supplies designated input pointers.
The paper explains that symbol opacity prevents packing a whole set into one datum
and moving it at unit cost. These application assumptions are essential to the
stated lower bound and are not bundled into the general machine. The weighted-union
algorithm, pp. 114–115, combines symbol identities, integer sizes, and parent pointers.
The current foundation does not prove that algorithm or Tarjan's lower bound.

## Known Limitations

The source survey does not establish a uniform finite encoding of exact real inputs, nor a native certificate for every algebraic interpretation. It does not identify the natural RAM, generic RAM and upstream typed-bank RAM by naming alone. An upstream typed-bank RAM proposal (CSLib #1158) was closed unmerged on 2026-11-02; no local semantic identification with that design was found in the inspected sources.

[complexitylib]: ../sources.md#complexitylib
[cookreckhow73]: ../sources.md#cookreckhow73
[erickson24]: ../sources.md#erickson24
