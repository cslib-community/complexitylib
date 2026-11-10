/-
Copyright (c) 2026 Samuel Schlesinger, Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Logic.Function.Basic

/-!
# First indices under injective maps

Mapping a list through an injective function does not move the first occurrence of any element.

## Main results

* `List.idxOf_map_of_injective`: `(l.map f).idxOf (f a) = l.idxOf a` for injective `f`.
-/

public section

namespace List

/-- Mapping a list through an injective function preserves the first index of every element. -/
theorem idxOf_map_of_injective {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} (hf : Function.Injective f) (l : List α) (a : α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hbeq : (f x == f a) = (x == a) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, hf.eq_iff]
    simp only [map_cons, idxOf_cons, ih, hbeq]

end List
