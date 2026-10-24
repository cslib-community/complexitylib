/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Data.List.GetD

/-!
# Boolean circuits scheduled in layers

Each node reads only the preceding layer. Constants allow evaluation with no input wires;
copies carry values across layers; NAND nodes may read a wire twice. The last layer supplies
all outputs, and the empty program preserves all inputs. Wire indices have binary encodings.

The number of scheduled layers counts copies and empty layers too. It is not identified here
with the depth of a De Morgan circuit. `Layered.Compile` converts ordinary shared circuits into
exactly two layers per designated-output depth, with output selection as separate wiring.

## Main definitions

* `Cslib.Circuits.Boolean.Layered.Node`, `Cslib.Circuits.Boolean.Layered.Node.code`,
  `Cslib.Circuits.Boolean.Layered.Node.Valid`, `Cslib.Circuits.Boolean.Layered.Node.eval`:
  constants, copies and NANDs, together with their tuple code, reference validity, and node
  evaluation.
* `Cslib.Circuits.Boolean.Layered.evalLayer`, `Cslib.Circuits.Boolean.Layered.eval`: evaluation of a
  single layer and of a list of layers.
* `Cslib.Circuits.Boolean.Layered.outputWidth`: the number of wires in the final row.
* `Cslib.Circuits.Boolean.Layered.select`: ordered output wiring, allowing repeated wires.
* `Cslib.Circuits.Boolean.Layered.WellFormed`: all references read the preceding layer.
* `Cslib.Circuits.Boolean.Layered.encNode`: two tag bits and binary wire indices.

## References

The consecutive-layer presentation, including inserted copy gates, is used in
[C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- A node whose inputs are positions in the preceding layer. -/
inductive Node where
  | const (value : Bool)
  | copy (wire : ℕ)
  | nand (first second : ℕ)
  deriving DecidableEq

/-- The two tag bits distinguish the four operations; unused wire positions are zero. -/
def Node.code : Node → (Bool × Bool) × ℕ × ℕ
  | .const b => ((false, b), 0, 0)
  | .copy i => ((true, false), i, 0)
  | .nand i j => ((true, true), i, j)

/-- A node is uniquely determined by its tag-and-index tuple `Node.code`. -/
theorem Node.code_injective : Function.Injective Node.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Node.code]

/-- Encode nodes with two operation bits and binary wire indices, including invalid indices. -/
def encNode : Node ↪ List Bool :=
  ⟨fun node => encPair (encPair encBool encBool) (encPair encNat encNat) node.code,
    (encPair (encPair encBool encBool) (encPair encNat encNat)).injective.comp
      Node.code_injective⟩

/-- A node is valid when each of its references exists in the preceding layer. -/
def Node.Valid (width : ℕ) : Node → Prop
  | .const _ => True
  | .copy i => i < width
  | .nand i j => i < width ∧ j < width

/-- Evaluate one node. Invalid references read `false`; correctness of a client interpreter
may require `Node.Valid` rather than preserving this fallback. -/
def Node.eval (inputs : List Bool) : Node → Bool
  | .const b => b
  | .copy i => inputs.getD i false
  | .nand i j => !(inputs.getD i false && inputs.getD j false)

/-- Evaluate a layer, preserving its order and repeated references. -/
def evalLayer (inputs : List Bool) (layer : List Node) : List Bool :=
  layer.map (Node.eval inputs)

/-- Evaluating a layer produces one output bit per node in the layer. -/
@[simp] theorem length_evalLayer (inputs : List Bool) (layer : List Node) :
    (evalLayer inputs layer).length = layer.length := List.length_map _

/-- Execute the layers in order. No layers means identity, including on an empty input. -/
def eval (inputs : List Bool) : List (List Node) → List Bool
  | [] => inputs
  | layer :: layers => eval (evalLayer inputs layer) layers

/-- Evaluating an empty schedule leaves the inputs unchanged. -/
@[simp] theorem eval_nil (inputs : List Bool) : eval inputs [] = inputs := rfl

/-- Evaluating `layer :: layers` evaluates `layer` on the inputs and then runs `layers`. -/
@[simp] theorem eval_cons (inputs : List Bool) (layer : List Node) (layers : List (List Node)) :
    eval inputs (layer :: layers) = eval (evalLayer inputs layer) layers := rfl

/-- Evaluating a concatenation of layer schedules runs the first schedule and then the second. -/
theorem eval_append (inputs : List Bool) (first second : List (List Node)) :
    eval inputs (first ++ second) = eval (eval inputs first) second := by
  induction first generalizing inputs with
  | nil => rfl
  | cons layer layers ih => exact ih (evalLayer inputs layer)

/-- The number of wires after the schedule, retaining the input width for an empty schedule. -/
def outputWidth (inputCount : ℕ) : List (List Node) → ℕ
  | [] => inputCount
  | layer :: layers => outputWidth layer.length layers

/-- The output width of an empty schedule is the input width. -/
@[simp] theorem outputWidth_nil (inputCount : ℕ) : outputWidth inputCount [] = inputCount := rfl

/-- The output width of `layer :: layers` is the output width of `layers` from `layer.length`. -/
@[simp] theorem outputWidth_cons (inputCount : ℕ) (layer : List Node)
    (layers : List (List Node)) :
    outputWidth inputCount (layer :: layers) = outputWidth layer.length layers := rfl

/-- The output width of a concatenated schedule is the output width of the second from the first. -/
theorem outputWidth_append (inputCount : ℕ) (first second : List (List Node)) :
    outputWidth inputCount (first ++ second) =
      outputWidth (outputWidth inputCount first) second := by
  induction first generalizing inputCount with
  | nil => rfl
  | cons layer layers ih => exact ih layer.length

/-- Evaluation has the width determined by the syntax, regardless of reference validity. -/
@[simp] theorem length_eval (inputs : List Bool) (layers : List (List Node)) :
    (eval inputs layers).length = outputWidth inputs.length layers := by
  induction layers generalizing inputs with
  | nil => rfl
  | cons layer layers ih => simp only [eval_cons, ih, length_evalLayer, outputWidth_cons]

/-- Select output wires in order, allowing repetitions. Selection adds no circuit layer. -/
def select (inputs : List Bool) (outputs : List ℕ) : List Bool :=
  outputs.map (inputs.getD · false)

/-- Output selection produces one bit per requested wire index. -/
@[simp] theorem length_select (inputs : List Bool) (outputs : List ℕ) :
    (select inputs outputs).length = outputs.length := List.length_map _

/-- Extending a prefix executes precisely its next scheduled layer. -/
theorem eval_take_succ (inputs : List Bool) (layers : List (List Node)) {i : ℕ}
    (hi : i < layers.length) :
    eval inputs (layers.take (i + 1)) =
      evalLayer (eval inputs (layers.take i)) (layers.getD i []) := by
  rw [List.take_succ_eq_append_getElem hi, eval_append, eval_cons, eval_nil,
    List.getD_eq_getElem _ _ hi]

/-- All references are in range in the immediately preceding layer. -/
def WellFormed (inputCount : ℕ) : List (List Node) → Prop
  | [] => True
  | layer :: layers => (∀ node ∈ layer, node.Valid inputCount) ∧ WellFormed layer.length layers

/-- The empty layer schedule is well-formed for any input width. -/
@[simp] theorem wellFormed_nil (inputCount : ℕ) : WellFormed inputCount [] := trivial

/-- `layer :: layers` is well-formed iff every node in `layer` is valid for `inputCount` and
`layers` is well-formed for `layer.length`. -/
@[simp] theorem wellFormed_cons (inputCount : ℕ) (layer : List Node)
    (layers : List (List Node)) :
    WellFormed inputCount (layer :: layers) ↔
      (∀ node ∈ layer, node.Valid inputCount) ∧ WellFormed layer.length layers := Iff.rfl

/-- A concatenated schedule is well-formed iff the first is well-formed and the second is
well-formed for the output width of the first. -/
theorem wellFormed_append (inputCount : ℕ) (first second : List (List Node)) :
    WellFormed inputCount (first ++ second) ↔
      WellFormed inputCount first ∧ WellFormed (outputWidth inputCount first) second := by
  induction first generalizing inputCount with
  | nil => simp
  | cons layer layers ih => simp only [List.cons_append, wellFormed_cons, outputWidth_cons,
      ih, and_assoc]

/-- Each scheduled layer reads valid wires of the evaluated prefix. -/
theorem WellFormed.valid_getD {inputs : List Bool} {layers : List (List Node)}
    (h : WellFormed inputs.length layers) {i : ℕ} (hi : i < layers.length) :
    ∀ node ∈ layers.getD i [], node.Valid (eval inputs (layers.take i)).length := by
  induction layers generalizing inputs i with
  | nil => simp at hi
  | cons layer layers ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero, List.take_zero, eval_nil] using h.1
    | succ i =>
      have htail : WellFormed (evalLayer inputs layer).length layers := by
        simpa only [length_evalLayer] using h.2
      simpa only [List.getD_cons_succ, List.take_succ_cons, eval_cons] using
        ih htail (Nat.lt_of_succ_lt_succ hi)

end Cslib.Circuits.Boolean.Layered
