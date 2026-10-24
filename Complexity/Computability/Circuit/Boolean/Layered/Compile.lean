/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered
public import Complexity.Computability.Circuit.Boolean.DepthTime
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Compiling shared Boolean circuits into consecutive layers

Each original depth uses a preparation layer and a finishing layer. Original input and gate
values retain their wire numbers. Two further slots per gate hold NAND intermediates, including
the two negated operands of OR. Copies carry earlier values between levels. The first layer
creates the working slots directly from the original inputs; it requires no padding layer.

Output selection is separate wiring, so an empty schedule preserves depth-zero circuits.

## Main definitions

* `Cslib.Circuits.Boolean.Layered.carry`, `Cslib.Circuits.Boolean.Layered.prepareFirst`,
  `Cslib.Circuits.Boolean.Layered.prepareSecond`, `Cslib.Circuits.Boolean.Layered.finish`:
  per-node microlevel constructors for carrying wires and decomposing De Morgan gates into NANDs.
* `Cslib.Circuits.Boolean.Layered.prepareLayer`: prepare one depth's NAND intermediates.
* `Cslib.Circuits.Boolean.Layered.finishLayer`: finish gates at that depth and carry older wires.
* `Cslib.Circuits.Boolean.Layered.schedule`: two consecutive layers per original depth.
* `Cslib.Circuits.Boolean.Layered.compile`: compute depths, schedule layers, and retain outputs.
* `Cslib.Circuits.Boolean.Layered.encCompiled`: encode the layers and binary output indices.

## Main results

* `Cslib.Circuits.Boolean.Layered.length_compile`: exactly twice the designated-output depth.

`Compile.Correctness` proves well-formedness and semantic preservation. `Compile.Size` bounds
the complete encoded result; `Compile.PolyTime` certifies the actual compiler on all raw codes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

/-- Carry an already computed main wire; unused slots contain a constant placeholder. -/
def carry (depths : List ℕ) (level wire : ℕ) : Node :=
  if depths.getD wire 0 < level then .copy wire else .const false

/-- The first NAND intermediate, or the value itself for a constant gate. -/
def prepareFirst (gate : Op × List ℕ) : Node :=
  match gate.1 with
  | .const b => .const b
  | .not => .nand (gate.2.getD 0 0) (gate.2.getD 0 0)
  | .and => .nand (gate.2.getD 0 0) (gate.2.getD 1 0)
  | .or => .nand (gate.2.getD 0 0) (gate.2.getD 0 0)

/-- OR needs a second negated operand; the other operations need only one intermediate. -/
def prepareSecond (gate : Op × List ℕ) : Node :=
  match gate.1 with
  | .or => .nand (gate.2.getD 1 0) (gate.2.getD 1 0)
  | _ => .const false

/-- Finish a gate using the two scratch positions allocated after all main wires. -/
def finish (inputCount gateCount gateIndex : ℕ) : Op → Node
  | .and => .nand (inputCount + gateCount + gateIndex) (inputCount + gateCount + gateIndex)
  | .or => .nand (inputCount + gateCount + gateIndex) (inputCount + 2 * gateCount + gateIndex)
  | _ => .copy (inputCount + gateCount + gateIndex)

/-- Keep completed main wires and prepare the active depth in two scratch blocks. -/
def prepareLayer (inputCount : ℕ) (gates : List (Op × List ℕ)) (depths : List ℕ)
    (level : ℕ) : List Node :=
  (List.range (inputCount + gates.length)).map (carry depths level) ++
    (List.range gates.length).map (fun j =>
      if depths.getD (inputCount + j) 0 = level then
        prepareFirst (gates.getD j (.const false, [])) else .const false) ++
    (List.range gates.length).map (fun j =>
      if depths.getD (inputCount + j) 0 = level then
        prepareSecond (gates.getD j (.const false, [])) else .const false)

/-- Update the active main slots, retain earlier values, and clear the scratch blocks. -/
def finishLayer (inputCount : ℕ) (gates : List (Op × List ℕ)) (depths : List ℕ)
    (level : ℕ) : List Node :=
  (List.range inputCount).map Node.copy ++
    (List.range gates.length).map (fun j =>
      if depths.getD (inputCount + j) 0 = level then
        finish inputCount gates.length j (gates.getD j (.const false, [])).1
      else carry depths level (inputCount + j)) ++
    List.replicate (2 * gates.length) (.const false)

/-- Generate both microlevels at each depth, retaining shared wire slots. -/
def schedule (inputCount : ℕ) (gates : List (Op × List ℕ)) (depths : List ℕ)
    (depth : ℕ) : List (List Node) :=
  (List.range depth).flatMap fun k =>
    [prepareLayer inputCount gates depths (k + 1), finishLayer inputCount gates depths (k + 1)]

/-- Compile raw De Morgan code, retaining its designated outputs as free final wiring.
Depths are computed from the code, not supplied as extra input. Malformed codes have total
fallback behavior; semantic agreement is specified for well-formed circuits. -/
def compile (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (List Node) × List ℕ :=
  (schedule inputCount code.1 (wireDepthsCode inputCount code.1) (depthCode inputCount code),
    code.2)

/-- Encode the complete schedule and all binary output selectors. -/
abbrev encCompiled : List (List Node) × List ℕ ↪ List Bool :=
  Turing.MultiTapeTM.encPair (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encList encNode))
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat)

/-- `compile` preserves the designated output wire indices unchanged. -/
@[simp] theorem compile_outputs (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (compile inputCount code).2 = code.2 := rfl

/-- Every preparation layer has width `inputCount + 3 * gates.length`. -/
@[simp] theorem length_prepareLayer (inputCount : ℕ) (gates : List (Op × List ℕ))
    (depths : List ℕ) (level : ℕ) :
    (prepareLayer inputCount gates depths level).length = inputCount + 3 * gates.length := by
  simp only [prepareLayer, List.length_append, List.length_map, List.length_range]
  omega

/-- Every finishing layer has width `inputCount + 3 * gates.length`. -/
@[simp] theorem length_finishLayer (inputCount : ℕ) (gates : List (Op × List ℕ))
    (depths : List ℕ) (level : ℕ) :
    (finishLayer inputCount gates depths level).length = inputCount + 3 * gates.length := by
  simp only [finishLayer, List.length_append, List.length_map, List.length_range,
    List.length_replicate]
  omega

/-- At depth zero, the compiled schedule is empty. -/
@[simp] theorem schedule_zero (inputCount : ℕ) (gates : List (Op × List ℕ)) (depths : List ℕ) :
    schedule inputCount gates depths 0 = [] := rfl

/-- Scheduling `depth + 1` levels appends the preparation and finishing layers for level
`depth + 1`. -/
theorem schedule_succ (inputCount : ℕ) (gates : List (Op × List ℕ)) (depths : List ℕ)
    (depth : ℕ) :
    schedule inputCount gates depths (depth + 1) = schedule inputCount gates depths depth ++
      [prepareLayer inputCount gates depths (depth + 1),
        finishLayer inputCount gates depths (depth + 1)] := by
  simp [schedule, List.range_succ]

/-- The schedule uses two layers per source depth, irrespective of the number of stored gates. -/
@[simp] theorem length_schedule (inputCount : ℕ) (gates : List (Op × List ℕ))
    (depths : List ℕ) (depth : ℕ) :
    (schedule inputCount gates depths depth).length = 2 * depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [schedule_succ, ih, Nat.mul_add]

/-- Every scheduled layer has the same working width. The empty schedule still has input width. -/
theorem length_of_mem_schedule (inputCount : ℕ) (gates : List (Op × List ℕ))
    (depths : List ℕ) (depth : ℕ) {layer : List Node}
    (h : layer ∈ schedule inputCount gates depths depth) :
    layer.length = inputCount + 3 * gates.length := by
  obtain ⟨k, _, h⟩ := List.mem_flatMap.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> simp

/-- The preparation layer carries exactly the completed main slots. -/
theorem getD_eval_prepareLayer_main (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (level : ℕ) {i : ℕ}
    (hi : i < inputCount + gates.length) :
    (evalLayer inputs (prepareLayer inputCount gates depths level)).getD i false =
      (carry depths level i).eval inputs := by
  simp only [evalLayer, prepareLayer, List.map_append, List.map_map, List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  exact List.getD_map_range _ _ hi

/-- The first scratch block stores the first intermediate for an active gate. -/
theorem getD_eval_prepareLayer_first (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (level : ℕ) {j : ℕ}
    (hj : j < gates.length) (hlevel : depths.getD (inputCount + j) 0 = level) :
    (evalLayer inputs (prepareLayer inputCount gates depths level)).getD
      (inputCount + gates.length + j) false =
      (prepareFirst (gates.getD j (.const false, []))).eval inputs := by
  simp only [evalLayer, prepareLayer, List.map_append, List.map_map, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_map_range _ _ hj]
  simp only [Function.comp_apply, ite_eq_left hlevel]

/-- The second scratch block stores OR's second negated operand. -/
theorem getD_eval_prepareLayer_second (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (level : ℕ) {j : ℕ}
    (hj : j < gates.length) (hlevel : depths.getD (inputCount + j) 0 = level) :
    (evalLayer inputs (prepareLayer inputCount gates depths level)).getD
      (inputCount + 2 * gates.length + j) false =
      (prepareSecond (gates.getD j (.const false, []))).eval inputs := by
  simp only [evalLayer, prepareLayer, List.map_append, List.map_map]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_map, List.length_range]
  have hindex : inputCount + 2 * gates.length + j -
      (inputCount + gates.length + gates.length) = j := by omega
  rw [hindex, List.getD_map_range _ _ hj]
  simp only [Function.comp_apply, ite_eq_left hlevel]

/-- Input wires are copied through the finishing layer. -/
theorem getD_eval_finishLayer_input (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (level : ℕ) {i : ℕ}
    (hi : i < inputCount) :
    (evalLayer inputs (finishLayer inputCount gates depths level)).getD i false =
      inputs.getD i false := by
  simp only [evalLayer, finishLayer, List.map_append, List.map_map, List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_map_range _ _ hi]
  rfl

/-- A main gate slot is either finished at this level or carried from an earlier one. -/
theorem getD_eval_finishLayer_gate (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (level : ℕ) {j : ℕ}
    (hj : j < gates.length) :
    (evalLayer inputs (finishLayer inputCount gates depths level)).getD (inputCount + j) false =
      (if depths.getD (inputCount + j) 0 = level then
        finish inputCount gates.length j (gates.getD j (.const false, [])).1
      else carry depths level (inputCount + j)).eval inputs := by
  simp only [evalLayer, finishLayer, List.map_append, List.map_map, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  exact List.getD_map_range _ _ hj

/-- The two microlevels compute one De Morgan operation from its original wire values. -/
theorem finish_prepare_eq {n g : ℕ} (inputs : List Bool) (gates : List (Op × List ℕ))
    (depths : List ℕ) (level : ℕ) {j : ℕ} (hj : j < gates.length)
    (line : Line signature n g) (hgate : gates.getD j (.const false, []) = line.code)
    (hlevel : depths.getD (n + j) 0 = level) :
    (finish n gates.length j line.op).eval (evalLayer inputs (prepareLayer n gates depths level)) =
      interpretation line.op (fun a => inputs.getD (line.wires a).toNat false) := by
  have hfirst := getD_eval_prepareLayer_first inputs n gates depths level hj hlevel
  have hsecond := getD_eval_prepareLayer_second inputs n gates depths level hj hlevel
  rw [hgate] at hfirst hsecond
  rcases line with ⟨op, wires⟩
  cases op <;> simp only [finish, Node.eval]
  · rw [hfirst]
    rfl
  · rw [hfirst]
    simp [prepareFirst, Line.code, Node.eval, interpretation]
  · rw [hfirst]
    simp [prepareFirst, Line.code, Node.eval, interpretation]
  · rw [hfirst, hsecond]
    simp [prepareFirst, prepareSecond, Line.code, Node.eval, interpretation, Bool.not_and]

/-- Compiling a typed circuit uses exactly twice its designated-output depth. Dead gates do not
extend the schedule. -/
@[simp] theorem length_compile {n m : ℕ} (c : Circuit signature n m) :
    (compile n c.code).1.length = 2 * c.depth := by
  simp only [compile, length_schedule, depthCode_code]

end Cslib.Circuits.Boolean.Layered
