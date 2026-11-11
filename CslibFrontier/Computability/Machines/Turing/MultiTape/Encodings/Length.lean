/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Lengths of encoded lists

The framed encoding of a list (`Turing.MultiTapeTM.encList`) spends `2 * |enc a| + 1` symbols on
each element `a`. In particular the sum of the lengths of its encoded elements is no longer than
the encoding, as is the list itself (`Turing.MultiTapeTM.length_le_length_encList`). Such bounds
are what a reduction needs to bound the size of its output, or a verifier the length of a
certificate, in terms of the input.

## Main results

* `Turing.MultiTapeTM.length_encList`: the exact length.
* `Turing.MultiTapeTM.sum_length_le_length_encList`: the encoded elements are no longer, in total,
  than the encoded list.
* `Turing.MultiTapeTM.length_encList_set_le`: bound on the encoded length after replacing a list
  element.
* `Turing.MultiTapeTM.length_unframe_add_dropFrame_le`: the unframed prefix and remaining suffix
  of any bit list satisfy `2 * (unframe v).length + (dropFrame v).length ≤ v.length`.
-/

public section

namespace Turing.MultiTapeTM

variable {α : Type*} (enc : α ↪ List Bool)

theorem length_encList (l : List α) :
    (encList enc l).length = (l.map fun a => 2 * (enc a).length + 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Reversing a list preserves the full encoded size, including each element's framing. -/
@[simp] theorem length_encList_reverse (l : List α) :
    (encList enc l.reverse).length = (encList enc l).length := by
  simp only [length_encList, List.map_reverse, List.sum_reverse]

/-- The encoded elements of a list are no longer, in total, than the encoded list. -/
theorem sum_length_le_length_encList (l : List α) :
    (l.map fun a => (enc a).length).sum ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Replacing an element of a list increases the encoded list length by at most
`2 * (enc x).length + 1`. -/
theorem length_encList_set_le (l : List α) (i : ℕ) (x : α) :
    (encList enc (l.set i x)).length ≤ (encList enc l).length + 2 * (enc x).length + 1 := by
  induction l generalizing i with
  | nil => simp only [List.set_nil]; omega
  | cons a l ih =>
    rcases i with _ | i
    · simp only [List.set_cons_zero, length_encList, List.map_cons, List.sum_cons]
      omega
    · simp only [List.set_cons_succ, length_encList, List.map_cons, List.sum_cons] at ih ⊢
      have := ih i
      omega

/-- The unframed prefix and remaining suffix of any bit list satisfy
`2 * (unframe v).length + (dropFrame v).length ≤ v.length`. -/
theorem length_unframe_add_dropFrame_le :
    ∀ v : List Bool, 2 * (unframe v).length + (dropFrame v).length ≤ v.length
  | [] | [true] => by simp [unframe, dropFrame]
  | false :: v => by simp [unframe, dropFrame]
  | true :: b :: v => by
    have ih := length_unframe_add_dropFrame_le v
    simp only [unframe, dropFrame, List.length_cons]
    omega

end Turing.MultiTapeTM
