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

## Known Limitations

The source survey does not establish a uniform finite encoding of exact real inputs, nor a native certificate for every algebraic interpretation. It does not identify the natural RAM, generic RAM and upstream typed-bank RAM by naming alone. `UPSTREAM.md` records coordination with an upstream typed RAM design; no local semantic identification with that design was found in the inspected sources.

[complexitylib]: ../sources.md#complexitylib
[cookreckhow73]: ../sources.md#cookreckhow73
[erickson24]: ../sources.md#erickson24
