/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered

/-!
# Padding layered Boolean circuits with copies

An identity layer copies every wire in order. Appending such layers extends a schedule to a
chosen layer count without changing its value or output width. Schedules already longer than
the target are unchanged. The construction also covers zero-width rows and empty schedules.

## Main definitions

* `Cslib.Circuits.Boolean.Layered.identityLayer`: one copy node per input wire.
* `Cslib.Circuits.Boolean.Layered.padTo`: append copies up to a target layer count.

## Main results

* `Cslib.Circuits.Boolean.Layered.eval_padTo`: padding preserves evaluation on actual inputs.
* `Cslib.Circuits.Boolean.Layered.outputWidth_padTo`: padding preserves the final width.
* `Cslib.Circuits.Boolean.Layered.WellFormed.padTo`: padding preserves valid references.
* `Cslib.Circuits.Boolean.Layered.length_padTo`: the resulting length is the larger of the
  original length and the target.

## References

Copy gates between consecutive layers are used in [Gentry, Section 2][Gentry2009].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

/-- Copy every wire in order, including the empty row when `width = 0`. -/
def identityLayer (width : ℕ) : List Node := (List.range width).map Node.copy

@[simp] theorem length_identityLayer (width : ℕ) : (identityLayer width).length = width := by
  simp [identityLayer]

private theorem valid_identityLayer (width : ℕ) :
    ∀ node ∈ identityLayer width, node.Valid width := by
  intro node hnode
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hnode
  exact List.mem_range.mp hi

@[simp] theorem evalLayer_identityLayer (inputs : List Bool) :
    evalLayer inputs (identityLayer inputs.length) = inputs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [evalLayer, identityLayer, Node.eval, hi']

@[simp] theorem eval_replicate_identityLayer (inputs : List Bool) (count : ℕ) :
    eval inputs (List.replicate count (identityLayer inputs.length)) = inputs := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [List.replicate_succ, eval_cons, evalLayer_identityLayer, ih]

@[simp] theorem outputWidth_replicate_identityLayer (width count : ℕ) :
    outputWidth width (List.replicate count (identityLayer width)) = width := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, outputWidth_cons, length_identityLayer, ih]

private theorem wellFormed_replicate_identityLayer (width count : ℕ) :
    WellFormed width (List.replicate count (identityLayer width)) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    simpa only [List.replicate_succ, wellFormed_cons, length_identityLayer] using
      And.intro (valid_identityLayer width) ih

/-- Extend a schedule to `target` layers by copying its final row. Longer schedules are retained. -/
def padTo (inputCount target : ℕ) (layers : List (List Node)) : List (List Node) :=
  layers ++ List.replicate (target - layers.length) (identityLayer (outputWidth inputCount layers))

@[simp] theorem length_padTo (inputCount target : ℕ) (layers : List (List Node)) :
    (padTo inputCount target layers).length = max layers.length target := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

theorem length_padTo_of_le (inputCount target : ℕ) (layers : List (List Node))
    (h : layers.length ≤ target) : (padTo inputCount target layers).length = target := by
  rw [length_padTo, max_eq_right h]

@[simp] theorem padTo_eq_self (inputCount target : ℕ) (layers : List (List Node))
    (h : target ≤ layers.length) : padTo inputCount target layers = layers := by
  simp [padTo, Nat.sub_eq_zero_of_le h]

/-- The input count must describe the actual input row; reference validity is unnecessary. -/
@[simp] theorem eval_padTo (inputs : List Bool) (target : ℕ) (layers : List (List Node)) :
    eval inputs (padTo inputs.length target layers) = eval inputs layers := by
  rw [padTo, eval_append, ← length_eval, eval_replicate_identityLayer]

@[simp] theorem outputWidth_padTo (inputCount target : ℕ) (layers : List (List Node)) :
    outputWidth inputCount (padTo inputCount target layers) = outputWidth inputCount layers := by
  rw [padTo, outputWidth_append, outputWidth_replicate_identityLayer]

theorem WellFormed.padTo {inputCount : ℕ} {layers : List (List Node)}
    (h : WellFormed inputCount layers) (target : ℕ) :
    WellFormed inputCount (padTo inputCount target layers) :=
  (wellFormed_append ..).mpr ⟨h, wellFormed_replicate_identityLayer ..⟩

end Cslib.Circuits.Boolean.Layered
