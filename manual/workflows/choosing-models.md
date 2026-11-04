# Choose a model and state its contract

Start with the claim you need: a function runs in polynomial time, a transducer uses logarithmic workspace, a circuit has bounded depth, or a stateful client makes few operations. These conclusions use different currencies. Select the predicate before implementing the algorithm. The [complete model map](../model-map.md) and [resource conventions](../machines-and-classes/native-and-resources.md) supply the reference details. [complexitylib][complexitylib]

## Choose an entry point

Module names in this table follow `Complexity.`; open the linked client for its complete imports and namespace context.

| Task | Model and entry import | Existing client | Resource claim and next bridge |
|---|---|---|---|
| Certify an ordinary function | Native multitape machine; `Tactic.PolyTime` | [PolyTimePlainDriver](../../ComplexityTests/PolyTimePlainDriver.lean) | `ComputableInPolyTime`; compose certificates relative to explicit encodings. |
| Produce a long answer using little workspace | Native transducer; `Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words` | [LogSpaceWords](../../ComplexityTests/LogSpaceWords.lean) | `ComputableInLogSpace`; composition replays intermediate output. |
| Count bounded-word instructions | Word-RAM; `Computability.WordRAM.Turing` | [WordRAMTuring](../../ComplexityTests/WordRAMTuring.lean) | Instruction count at a width and basis; supply fitting inputs, an efficient width schedule and native operation certificates to reach Turing polynomial time. |
| Specify and amortize a data structure | `StateTransitionSpec`; `DataStructure.StateTransition.Refinement` | [StateTransitionRefinement](../../ComplexityTests/StateTransitionRefinement.lean) | Backend-operation charge; a native realization must also implement and charge the client's control computation. |
| Build a uniformly generated circuit family | `Circuit`; `Computability.Complexity.Problems.CircuitValue.Compilation` | [UniformCircuits](../../ComplexityTests/UniformCircuits.lean) | Circuit correctness and a polynomial-time code constructor; inspect size/depth separately when those are the target bounds. |
| Evaluate an ordered finite-model query | FO(LFP); `Computability.Complexity.Classes.P.FirstOrder` | [FOLeastFixedPointPolyTime](../../ComplexityTests/FOLeastFixedPointPolyTime.lean) | Native model-checking over encoded structures; distinguish executable raw syntax from well-formed positive formulas used for least-fixed-point semantics. |
| Reason about random choices or oracle calls | `ProbComp` / `OracleComp`; `Languages.Probabilistic.Simulation` | [Programs](../../ComplexityTests/Programs.lean) | Interpretation proves a distributional law; follow the [probabilistic workflow](probabilistic-workflows.md) for native efficiency and oracle charges. |

Adapt the client's contract to your types. A failed bridge usually means a missing implementation, encoding or resource hypothesis.

## Write the contract before the proof

Record the input and output types; their encodings; the measured input size; the time, workspace, gate or query bound; and what is fixed before the input varies. For native computation, an encoding has type `α ↪ List Bool`: injectivity is part of the data. Reuse `encBits`, `encBool`, binary `encNat`, unary `encUnary`, `encPair` and `encList` before defining another representation. A new embedding needs an injectivity proof and size lemmas suitable for the intended bound. [Encoding length lemmas](../../Complexity/Computability/Machines/Turing/MultiTape/Encodings/Length.lean) and [pair lengths](../../Complexity/Computability/Machines/Turing/MultiTape/Encodings/Pair.lean) show where framing overhead enters.

Binary and unary naturals are different contracts. A loop count computed into `encUnary` pays for writing its value; a short binary representation alone does not justify that many iterations. Framed lists charge both elements and delimiters. State bounds must include that representation overhead.

An arbitrary embedding supplies neither a decoder nor a decision procedure for malformed strings. Native correctness on values encoded by `enc` is a statement about valid inputs. If the application accepts arbitrary bytes, supply the parser, its correctness and its resource bound. Inspect any malformed-input guarantee in the chosen model checker rather than inferring it from injectivity.

To reuse a theorem under different encodings, match its representation first. For a function certified from `oldIn` to `oldOut`, supply efficient identity translations from `newIn` to `oldIn` and from `oldOut` to `newOut`, then compose. If the encoded words are literally equal, [ComputableInPolyTime.of_eq](../../Complexity/Computability/Machines/Turing/MultiTape/PolyTime.lean) gives the copy-machine case. A mathematical bijection by itself is insufficient to preserve complexity.

## Check uniformity and implementation

A native certificate chooses one finite machine before quantifying over inputs. Separate existence proofs for every length need not supply such a machine. Likewise, a circuit for every width does not establish an efficient constructor. `UniformCircuits.reverseFamily` explicitly provides one code-generating function and its `ComputableInPolyTime` certificate.

For RAM, read the operation interpretation and cost convention. The generic interpreter permits arbitrary semantic primitives; a generic execution theorem alone does not implement them on bits. The [RAM reference](../algorithms-and-memory/ram-variants.md) describes native primitive certificates; the [Word-RAM bridge](../algorithms-and-memory/wordram-and-bridges.md) adds initialization and width obligations. For stateful specifications, [refinement and realization](../algorithms-and-memory/memory-specifications.md) separate abstract operation counts from native instructions. Consult the [circuit](../circuits-logic-and-other-models/circuits-and-formulas.md) and [finite-model](../circuits-logic-and-other-models/finite-model-logic.md) references before transporting those theorems.

Continue with the [deterministic workflows](deterministic-workflows.md) once you have a Lean goal, a client and explicit bridge hypotheses.

[complexitylib]: ../sources.md#complexitylib
