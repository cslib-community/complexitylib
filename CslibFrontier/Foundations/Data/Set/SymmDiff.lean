/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Set/Card.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Set.Card
public import Mathlib.Order.SymmDiff

/-!
# Symmetric difference of a set with a singleton

Adding or removing one element changes the size of a finite set by one, so taking the symmetric
difference with a singleton flips the parity of `Set.ncard`. This is the `Set.ncard` counterpart
of `Finset.symmDiff_singleton_eq`.

## Main results

* `Set.even_ncard_symmDiff_singleton_iff`: toggling one element flips the parity of `ncard`.
-/

public section

namespace Set

variable {α : Type*}

/-- Adding or removing one element by symmetric difference changes the parity of the size of a
finite set. -/
theorem even_ncard_symmDiff_singleton_iff {s : Set α} (hs : s.Finite) (a : α) :
    Even (symmDiff s {a}).ncard ↔ ¬Even s.ncard := by
  by_cases ha : a ∈ s
  · have h : symmDiff s {a} = s \ {a} := by
      ext x
      by_cases hx : x = a
      · subst hx
        simp [mem_symmDiff, ha]
      · simp [mem_symmDiff, hx]
    rw [h, ← ncard_sdiff_singleton_add_one ha hs, Nat.even_add_one, not_not]
  · have h : symmDiff s {a} = insert a s := by
      ext x
      by_cases hx : x = a
      · subst hx
        simp [mem_symmDiff, ha]
      · simp [mem_symmDiff, hx]
    rw [h, ncard_insert_of_notMem ha hs, Nat.even_add_one]

end Set
