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
That file is the whole model and contains no proofs. `PointerMachine.Basic` supplies
invariants and resource bounds.

`Model` gives one type of data values, a distinguished `undefined` value, and named
binary operations and predicates with total interpretations. `Layout` fixes the number
of pointer registers, data registers, pointer fields and data fields. The model, the
layout and the finite instruction list are fixed independently of input size. A basis
with several kinds of data uses a sum type whose operations return `undefined` on
operands of the wrong kind.

`State M L` holds a control label, the two register banks and `heap`, the list of all
records in order of creation. A `Pointer` is null or the position of a record in that
list. Positions are natural numbers, but no instruction takes or returns one: programs
obtain pointers only by copying a register, loading a pointer field of a record that a
register specifies, or creating a record. `Instr.effect_provenance` states this.
There is no theorem yet that execution is invariant under reordering the heap.

`Instr.effect` gives each instruction's effect on registers and records, and
`Instr.next` the label that follows. Both are total. A load or store through null does
nothing. A new record has null pointer fields and `undefined` data fields. Control
labels are zero-based. `step` is undefined at `halt` and outside the program;
`Executes` requires the final label to hold `halt`.

`State.Valid` requires every nonnull pointer in a register or record to specify a
record. It allows cycles, sharing and unreachable records. Applications supply valid
input states, with preparation cost separate; `Runs.valid` preserves the hypothesis.
Outside valid states a pointer that specifies no record acts like null until a
later creation gives it one; `Instr.create_fresh` shows that in a valid state no
register or record already holds the pointer that `create` returns.

`Runs` reuses CSLib's `Relation.RelatesInSteps`; `Executes` also charges the final halt.
Each instruction costs one unit, including a data primitive or a creation.
Space is `heap.length`: initial records plus creations, including unreachable
records. There is no deletion or garbage collection. `Runs.length_le` bounds
space by initial records plus instructions executed. These are instruction
and record measures, not bit-time, bit-space, or host allocation costs. Changing the
primitives changes what one instruction can accomplish.

`PointerMachine.Data` shows that a predicate on data which holds of `undefined` and is
closed under the operations is preserved by execution. `PointerMachine.Renaming` shows
that a permutation of the data commuting with the primitives commutes with execution,
with the same cost.

For symbols, the carrier type alone does not establish opacity: an operation from
symbols to integers would reveal an encoding. The protected-symbol instance
is `Symbols.model` from `CslibFrontier.Computability.PointerMachine.Symbols`.
Its values are undefined, a symbol or an integer. It supplies equality of data,
integer addition and subtraction, and integer order; arithmetic on a symbol returns
`undefined`. Abstract symbols and integer counters can therefore coexist in one
record, as they do in Tarjan's weighted-union example. `Symbols.hasSymbol_of_runs`
and `Symbols.symbolRenaming` state that programs neither produce symbols nor tell
them apart except by equality.

After the [standard setup](../workflows/getting-started.md), check the
[clients](../../CslibFrontierTests/PointerMachine.lean) with
`lake build CslibFrontierTests.PointerMachine --wfail --iofail`.
They run one program on symbols, integers and pointers with exact instruction
accounting, and cover null access, new records and invalid pointers. The clients
are model examples, not a verified union-find implementation or lower bound.

GenericRAM was assessed for reuse: its `evalOp` receives only register operands and
fixed configuration, and `Data.mem` has no allocation state. Its `admissible` and
`validMove` checks cannot consult a changing heap. Tagging values and restricting
`address` would prevent scalar address conversion but would not establish provenance
or fresh allocation. The pointer-machine module supplies its own small-step
instruction semantics while reusing the common exact-step relation and its resource
lemma. A common control engine or certified GenericRAM lowering would need a separate
semantic preservation argument.

The source is [Tarjan 1979](https://doi.org/10.1016/0022-0000(79)90042-4),
§2, pp. 111–112: separate data and pointer registers and fields, identical records,
access by explicit reference only, binary data operations and predicates, record
creation, null access doing nothing, a final halt, and one unit per instruction.
The formalization differs in four ways. Labels start at zero, and running past the
last instruction is not a successful halt. The source fills every field of a new
record with a special undefined value; here pointer fields are null and only data
fields are undefined. The source has a built-in equality test on data; here equality
is a predicate the model may supply. The source does not say what an operation does
on undefined data; here the model decides. No claim of a step-exact translation of
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
