/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Encoding.Check
public import Complexity.Computability.Circuit.Encoding.Evaluation
public import Complexity.Crypto.Protocols.VOLE.Native

/-!
# Native arithmetic-circuit VOLE kernels

The public input carries the existing arithmetic circuit code, the unary private-input count,
public input/output lists and auxiliary bits. All loop counts come from that unary count or
actual lists. Binary wire indices are used only by bounded lookup and comparison. The gate
validator is the shared `Circuits.codeCheck`; output count and wire bounds are checked before
setup. Kernels receive only the role's own share. They implement one fresh-mask session, not a
raw-bit adversary transport or a repeated-session security definition.

## Main definitions

* `NativeCircuit.validInput`: public validation using the existing code predicate.
* `NativeCircuit.layout`: multiplication gates in actual code order.
* `NativeCircuit.linearValues`: sparse public-input, gate and output rows.
* `NativeCircuit.senderFirst`, `NativeCircuit.senderReply`: sender-local kernels.
* `NativeCircuit.verify`: receiver-local verifier with explicit list-frame checks.
* `NativeCircuit.execute`, `NativeCircuit.simulate`: actual four-phase programs.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.NativeCircuit

open Circuits Probability

/-- Private input count, existing gate/output code, public inputs/outputs, auxiliary word. -/
abbrev Input (F : Type) :=
  ℕ × (List (ArithOp F × List ℕ) × List ℕ) × List F × List F × List Bool

/-- Sender-only vectors, including one untouched final mask coordinate. -/
abbrev SenderShare (F : Type) := List F × List F

/-- Corrections and linear mask openings, sent together before the weights. -/
abbrev First (F : Type) := List F × List F

/-- Complete receiver share, first message, transmitted weights, reply and private result. -/
abbrev View (F Result : Type) :=
  Native.Share F × First F × List F × (F × F) × Result

variable {F State Result : Type}

/-- Public and private inputs together, with the private count supplied in unary. -/
def inputCount (input : Input F) : ℕ := input.2.2.1.length + input.1

/-- All input and gate wires; this count never uses a binary wire index. -/
def wireCount (input : Input F) : ℕ := inputCount input + input.2.1.1.length

/-- Number of sparse linear rows, including a zero row at every multiplication gate. -/
def rowCount (input : Input F) : ℕ :=
  input.2.2.1.length + input.2.1.1.length + input.2.2.2.1.length

/-- Validate arities/back references, output count and output bounds before any setup. -/
def validInput (input : Input F) : Bool :=
  codeCheck (arithSignature F) (inputCount input) input.2.1.1 &&
    decide (input.2.1.2.length = input.2.2.2.1.length) &&
    input.2.1.2.all (· < wireCount input)

/-- Multiplication triples in their actual gate-list order, with total malformed defaults.
Only validated public codes are executed; the runtime theorem also covers malformed codes. -/
def layout (input : Input F) : Native.Input :=
  (wireCount input, (input.2.1.1.zipIdx.filterMap fun (gate, i) =>
    match gate.1 with
    | .mul => some (gate.2.getD 0 0, gate.2.getD 1 0, inputCount input + i)
    | _ => none), input.2.2.2.2)

variable [CommRing F]

/-- Sparse row evaluation: public inputs, each gate row, then designated outputs.
Repeated input occurrences are added separately, as in the existing coefficient matrix. -/
def linearValues (input : Input F) (values : List F) : List F :=
  (Native.weights input.2.2.1.length values) ++
    (input.2.1.1.zipIdx.map fun (gate, i) => match gate.1 with
      | .add => values.getD (gate.2.getD 0 0) 0 + values.getD (gate.2.getD 1 0) 0 -
          values.getD (inputCount input + i) 0
      | .mul => 0
      | .const _ => values.getD (inputCount input + i) 0) ++
    input.2.1.2.map (fun i => values.getD i 0)

/-- Public target of every input, gate and output row. -/
def targets (input : Input F) : List F :=
  input.2.2.1 ++ (input.2.1.1.map fun gate => match gate.1 with
    | .const c => c
    | _ => 0) ++ input.2.2.2.1

/-- Native trace of the existing arithmetic evaluator, retaining all input and gate values. -/
def trace (input : Input F) (w : List F) : List F :=
  evalCode (arithInterpretation F) 0 (input.2.2.1 ++ w) input.2.1.1

/-- Honest first message from the trace and sender-only vectors. -/
def senderFirst (input : Input F) (a : List F) (share : SenderShare F) : First F :=
  (List.zipWith (· - ·) a share.1, linearValues input share.2)

/-- Sender initialization rejects wrong witness or setup-vector lengths. The returned trace and
first message may be retained across the challenge without consulting receiver data. -/
def senderInit (input : Input F) (w : List F) (share : SenderShare F) :
    Option (List F × First F) :=
  if validInput input && decide (w.length = input.1) &&
      decide (share.1.length = wireCount input + 1) &&
      decide (share.2.length = wireCount input + 1) then
    let a := trace input w
    some (a, senderFirst input a share)
  else none

/-- Honest affine reply. The final setup coordinate is used once to mask the two coefficients. -/
def senderReply (input : Input F) (a : List F) (share : SenderShare F) (r : List F) : F × F :=
  let gates := (layout input).2.1
  let weighted := gates.zip (Native.weights gates.length r)
  (((weighted.map fun (gate, weight) => weight *
      voleMulCrossTerm (a.getD gate.1 0) (share.2.getD gate.1 0)
        (a.getD gate.2.1 0) (share.2.getD gate.2.1 0) (share.2.getD gate.2.2 0)).sum +
      share.1.getD (wireCount input) 0),
    (weighted.map fun (gate, weight) => weight *
      voleMulConstTerm (share.2.getD gate.1 0) (share.2.getD gate.2.1 0)).sum +
        share.2.getD (wireCount input) 0)

/-- Corrected tags, computed only from receiver-local data and the public corrections. -/
def adjusted (input : Input F) (share : Native.Share F) (d : List F) : List F :=
  List.zipWith (fun q c => q + c * share.1) (share.2.take (wireCount input)) d

/-- Receiver-side reconstruction used by the simulator. Sender realizability requires the
existing true-trace relation; the honest sender instead computes `senderFirst`. -/
def publicFirst (input : Input F) (share : Native.Share F) (d : List F) : First F :=
  (d, List.zipWith (fun value target => value - target * share.1)
    (linearValues input (adjusted input share d)) (targets input))

/-- Receiver-local checking with explicit public and list-frame rejection. Pair replies have a
fixed typed shape; parsing arbitrary bit strings is a separate transport obligation. -/
def verify [DecidableEq F] (input : Input F) (share : Native.Share F)
    (first : First F) (r : List F) (reply : F × F) : Bool :=
  validInput input && decide (share.2.length = wireCount input + 1) &&
    decide (first.1.length = wireCount input) && decide (first.2.length = rowCount input) &&
    decide (r.length = (layout input).2.1.length) &&
    (((linearValues input (adjusted input share first.1)).zip (targets input)).zip first.2).all
      (fun (row, mask) => decide (row.1 = row.2 * share.1 + mask)) &&
    decide (Native.checkValue (layout input) share first.1 r = reply.1 * share.1 + reply.2)

/-- Include reconstructed linear openings in the complete native simulator view. -/
def expandView (input : Input F) (view : Native.View F Result) : View F Result :=
  (view.1, publicFirst input view.1 view.2.1, view.2.2.1, view.2.2.2.1, view.2.2.2.2)

/-- Witness-free simulator, rejecting malformed public code before sampling or callbacks. -/
def simulate (sample : ProbComp F)
    (receiver : Native.Receiver F (Input F) (First F) State Result) (input : Input F) :
    ProbComp (Option (View F Result)) :=
  if validInput input then do
    let view ← Native.simulate sample receiver layout publicFirst input
    return some (expandView input view)
  else return none

/-- Actual native setup and four role-local callback phases. Sender kernels receive only the
sender share; callbacks receive only the receiver share. A typed cached-World law identifies this
trusted setup runner with the interaction, while retaining the separate role interfaces. -/
def execute (sample : ProbComp F)
    (receiver : Native.Receiver F (Input F) (First F) State Result)
    (input : Input F) (w : List F) : ProbComp (Option (View F Result)) :=
  if validInput input && decide (w.length = input.1) then do
    let u ← OracleComp.replicate (wireCount input + 1) sample
    let v ← OracleComp.replicate (wireCount input + 1) sample
    let delta ← sample
    let share := (delta, List.zipWith (fun x y => x * delta + y) u v)
    let state ← receiver.init input share
    let some (a, first) := senderInit input w (u, v) | return none
    let (r, state) ← receiver.challenge input share state first
    let r := Native.weights (layout input).2.1.length r
    let reply := senderReply input a (u, v) r
    let state ← receiver.receive input share state reply
    let result ← receiver.terminal input share state
    return some (share, first, r, reply, result)
  else return none

/-- Malformed public code performs no setup or callback operations in the actual program. -/
theorem execute_invalid (sample : ProbComp F)
    (receiver : Native.Receiver F (Input F) (First F) State Result)
    (input : Input F) (w : List F) (h : validInput input = false) :
    execute sample receiver input w = pure none := by
  simp [execute, h]

/-- The simulator also rejects malformed public code before any operation. -/
theorem simulate_invalid (sample : ProbComp F)
    (receiver : Native.Receiver F (Input F) (First F) State Result)
    (input : Input F) (h : validInput input = false) :
    simulate sample receiver input = pure none := by
  simp [simulate, h]

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
