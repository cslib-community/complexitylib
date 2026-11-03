# Word-RAM, random sampling, and Turing bridges

## Concrete machine and operation basis

[Complexity/Computability/WordRAM/Defs.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Defs.lean) uses finite register indices, natural memory addresses and word values below `2^w`. The program is a finite instruction list. The default memory is zero; input length is stored at address zero and input words at `1,…,n`. A scalar result is returned by `halt`, which costs one instruction. Installing the input and reading the result are conventions, not hidden execution steps [complexitylib][complexitylib].

`Basis` separates ALU symbols/arity from their interpretation. `standard` uses natural truncated subtraction and Lean's total division/modulo conventions; `exact` faults on subtraction underflow and division/modulo by zero. Both check result width rather than silently wrapping arithmetic modulo `2^w`. Restricted additive/arithmetic bases expose which operations an algorithm uses. `Basis.Hom` preserves interpretation; successful-run simulations can relate a partial basis to a more total one.

Copies and memory moves rely on a bounded-state invariant rather than rechecking every existing word. The program counter is naturally unbounded in the base Word-RAM; code-length/address restrictions are separate. An instruction can explicitly read the width, and `ReadsWidth` tracks that feature. Without it, successful runs have a width-monotonicity theorem.

Structured [Complexity/Computability/WordRAM/Structured.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Structured.lean) has operations, sequencing, branches and loops. Its `Exec` relation counts actual branch/jump overhead, and assembly preserves exact counts. Hoare and potential rules prove executions of this code; they do not treat a source-language loop as one machine instruction.

## Uniformity and output conventions

[WordSizeDependentProgram](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Time.lean#L149) chooses code from the width with a fixed register count and a global instruction-list-length bound. Literals may depend on width, and the selector itself is uncharged. `UniformDecidableInTime` instead uses one fixed program, which may read the width. These are distinct contracts.

Time bounds, input encodings and permitted input/width pairs can depend on width. Every contract is conditional on `InputFits`. Empty allowed conditions or inputs that never fit can make a proposition vacuous; a logarithmic threshold in the number of input words does not bound those words' values. Input-dependent width schedules can convey advice. These points are explicit in the source and must accompany comparisons with uniform Turing classes.

[Complexity/Computability/WordRAM/Function.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Function.lean) treats scalar word-valued functions. [ExecutesList](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/ListOutput.lean#L92) treats list output as the length-prefixed array addressed by the returned word in the pre-halt memory. Returning zero without writing can therefore return the original input. This is an output convention on the same machine; it does not charge the mathematical observer for copying that array out.

## Proved deterministic bridges

| Bridge | Statement and costs | Restrictions |
|---|---|---|
| Word-RAM ↔ generic interpreter | `step_toGeneric`, `run_toGeneric`, `executes_toGeneric_iff` in [Complexity/Computability/WordRAM/Defs.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Defs.lean) | Same basis, exact state correspondence and step count |
| Multitape TM → Word-RAM | `ComputableInPolyTime.exists_wordRAM` and `exists_wordRAM_nat` in [Complexity/Computability/WordRAM/OfTuring.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/OfTuring.lean) | One fixed additive program; tapes represented by interleaved addresses; scalar answer must fit |
| Word-RAM → native TM | [Complexity/Computability/WordRAM/Turing/Overhead.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Turing/Overhead.lean) | Efficient scalar operations, encoded fitted input, width and step budget construction charged |
| Polynomial-time decisions | [mem_P_iff_uniformPolynomialTime](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/P/WordRAM.lean#L153) | Fixed program; basis contains additive operations and has polynomial native scalar cost; specified encoding and threshold |
| Polynomial-time scalar functions | [Complexity/Computability/WordRAM/Invariance.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Invariance.lean) | General polynomial-bit answers use a polynomial width threshold; logarithmic-width equivalence additionally requires polynomially bounded answer values |
| Word-RAM → unbounded log-cost RAM | [Complexity/Computability/WordRAM/RAM.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/RAM.lean) | Additive fragment; eight target slots per instruction; successful forward simulation, not overflow-reflecting equivalence |

The fixed-program, scalar-output route to native polynomial time has these inputs:

```mermaid
flowchart TB
program["Fixed Word-RAM program<br/>basis and registers"]
fits["Admitted width<br/>all inputs fit"]
run["Successful RAM run<br/>polynomial step bound"]
operations["Checked operations<br/>native cost certificates"]
setup["Efficient setup<br/>unary width and words"]
simulation["Clock and simulator<br/>finite sparse memory"]
result["ComputableInPolyTime<br/>binary scalar output"]
program -->|"prove computation"| run
fits -->|"supply valid inputs"| run
run -->|"bound step count"| simulation
operations -->|"implement operations"| simulation
setup -->|"prepare state"| simulation
simulation -->|"charge the whole simulation"| result
```

Every incoming requirement is explicit in [Program.ComputesInTime.turingComputableInPolyTime_of_width](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Turing.lean#L514). The chosen width is computable in unary, the fitted input words are computable from the original encoding, and each checked basis operation has a native certificate. The bounds are measured in that original encoded input length. [WordRAMTuring](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/WordRAMTuring.lean#L65) demonstrates the route. List-output and width-selected code use their own contracts.

The reverse TM simulation's displayed overhead for a `T`-step, `n`-word, width-`w` run with scalar degree `d` is `O((T+1)*((n+T+1)*(w+1))^max(3,d))`, in addition to setup/clock obligations. The cubic floor reflects the finite association-list representation used by this simulator; it is not asserted to be an optimal RAM/TM overhead. The additive case has scalar degree two and still pays this cubic floor.

For scalar functions, polynomial output **bit length** differs from polynomial output **value**. `UniformComputableInPolyTime.polyBounded` records the necessity of the latter for a logarithmic-width scalar output. The general-width equivalence and logarithmic-width equivalence should not be merged into one unqualified theorem.

## Randomized instructions and exact laws

[Complexity/Computability/WordRAM/Randomized/Defs.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Randomized/Defs.lean) keeps the same flat instruction syntax and gives `rand dst src` the exact uniform law on `0,…,R[src]`, provided the bound fits. The deterministic interpreter faults on `rand`; the probabilistic interpreter produces a `ProbComp` tree. Halted and faulted outcomes are absorbing, and a halt retains final registers and memory.

The extension records worst-case successful halting, fault-freedom, random-call count and an explicit bit currency. Even `rand 0` makes one call while consuming zero bits in that currency. A bound of `R` calls implies at most `R*w` such bits. This is a unit-cost finite-uniform-word model, not an assertion that every instruction is exactly executable in bounded fair-coin time. The native strict-PPT distinction is explained in [programs and realization](../programs-crypto-and-probability/programs-and-realization.md).

[Complexity/Computability/WordRAM/Randomized/Structured.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Randomized/Structured.lean) uses `ExecRand` to certify a finite fault-free structured execution tree with the distribution of final data and exact instruction count. Compilation and random/cost bounds preserve its law.

### Realize memory clients with private coins

Import `Complexity.Computability.WordRAM.Realization.Random` for
[`RealizesRand`](../../Complexity/Computability/WordRAM/Realization/Random.lean), and
`Complexity.Computability.WordRAM.Realization.RandomLoop` for runtime-bounded iteration.
Start with a memory client with private coins, faithful input/output word encodings, a safe
entry domain, and separate time and random-call budgets. The realization chooses its emitter,
scratch size and exchange constant before runtime arguments, word widths and initial memories.
It requires bounded initial data, the encoded argument in its source registers, disjoint
scratch/frontier placement, the safe-domain premise and demonic admissibility of the client.

[`ExecRandLaw`](../../Complexity/Computability/WordRAM/Randomized/Law.lean) relates the emitted
code to the **joint** law of encoded result words and the entire memory function and frontier.
A result-only marginal cannot preserve a later memory-dependent call. The code keeps registers
outside its scratch bank and frontier, and every path terminates within `C*(time+1)` native
instructions and the separate random-call budget. Deterministic components enter through an
existing `Realizes` certificate and `Realizes.toRand`; their time is memory charge plus local
work and their random-call budget is zero.

`RealizesRand.bind` requires the continuation's domain and uniform time/call bounds for every
supported intermediate answer and memory. `RealizesRand.iterate` requires the corresponding
bounds at every supported loop prefix, using one body emitter. Supply those obligations at
reached memories; a bound only at the initial state, or only in expectation, is insufficient.
The native rules account for register copies, loop counters, headers and exits.

`RealizesRand.exists_init_program` compiles a selected result coordinate to the existing flat
program semantics, retaining its joint law with full memory/frontier and exporting both
`RandHaltsWithin` and `RandCallsBounded`. Keep the raw-input prefix equality, length/fit,
safe-domain and demonic-admissibility premises. `Data.init` raw-memory placement is an
**uncharged calling convention**; the charged `2*k+5` native prefix installs the frontier and
first `k` argument registers, not the whole graph. Its allowance `C*(time+1)+1` includes that
prefix, the body and trailing halt. The random budget counts primitive inclusive-range calls,
even `rand(0)`; it does not prove a bounded-cost exact fair-bit sampler.

Open the complete checked
[WordRAMRealizationRandom clients](../../ComplexityTests/WordRAMRealizationRandom.lean),
including their imports and encodings. `sample_program` samples an input position, retaining
repeated values' multiplicity; its input is nonempty and must fit. The runtime-repeat client
bounds every iteration. `storeSample_result_eq_cell` and `realizesRand_storeSample` retain the
correlation between the returned sample and the written cell, while preserving other memory
and the frontier. These are realization clients, not a completed native Karger implementation:
K2 still needs its method/setup and exact-resource deletion train, and K3 needs recursive
frame-stack realization. No expected-cost or uniform-word claim becomes a strict fair-coin
runtime claim through this interface.

## Expected time and unbounded termination

[expectedTime](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Randomized/Expected.lean#L165) sums, over horizons `t`, the probability that execution is still running. It is valued in extended nonnegative reals. Since both halt and fault are absorbing, this is time until either; concluding almost-sure **successful** halting also requires fault-freedom. `Executes.expectedTime_eq` recovers deterministic instruction counts, and worst-case halting reduces the sum to a finite horizon.

There are two structured interfaces. `expectedCodeTime` uses the finite fault-free `ExecRand` tree when one exists and is infinite otherwise; it can conservatively assign infinity to an unbounded almost-surely terminating loop. `ExecCodeDist` separately pairs a genuine output PMF with an expected step bound and supports unbounded geometric Las Vegas loops via `ExecCodeDist.loop_geometric` and `program_halts`. Distinguish this distributional certificate from finite-tree structured execution.

## Known Limitations

The inspected bridges establish their explicit deterministic models and encodings. They do not give a blanket equivalence for arbitrary width advice, arbitrary mathematical input encodings, all unbounded-integer operations at unit cost, or the randomized uniform-word instruction under strict fair-coin time. List-output extraction and dynamic caller argument preparation have their stated conventions; full end-to-end costs require a native caller when those steps matter.

[complexitylib]: ../sources.md#complexitylib
