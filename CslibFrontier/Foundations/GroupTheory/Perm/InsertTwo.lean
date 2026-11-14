/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Option)

public import CslibFrontier.Foundations.GroupTheory.Perm.InsertAfter

/-!
# Deleting two inserted corners after an outgoing splice

Exchanging the outgoing successors of the inserted points and then deleting both points
exchanges the original two corner successors. The identity retains their directed order.
-/

public section

namespace Equiv.Perm.Insertion

open Equiv

/-- Removing the inserted point recovers the original literal permutation. -/
@[simp] theorem removeNone_insertAfter {α : Type} [DecidableEq α]
    (f : Perm α) (h : α) : removeNone (insertAfter f h) = f := by
  apply Equiv.ext
  intro a
  by_cases ha : a = h
  · subst a
    simp [Equiv.removeNone, Equiv.removeNoneAux, insertAfter]
  · simp [Equiv.removeNone, Equiv.removeNoneAux, insertAfter, swap_apply_def, ha]

/-- Deletion commutes with changing coordinates on the retained points. -/
theorem removeNone_permCongr_option {α β : Type*} (e : α ≃ β) (f : Perm (Option α)) :
    removeNone (e.optionCongr.permCongr f) = e.permCongr (removeNone f) := by
  apply Equiv.ext
  intro b
  cases hf : f (some (e.symm b)) with
  | some a => simp [Equiv.removeNone, Equiv.removeNoneAux, Equiv.permCongr_apply,
      Equiv.optionCongr, hf]
  | none =>
    cases hn : f none with
    | none => exact False.elim (Option.some_ne_none _ (f.injective (hf.trans hn.symm)))
    | some a => simp [Equiv.removeNone, Equiv.removeNoneAux, Equiv.permCongr_apply,
        Equiv.optionCongr, hf, hn]

/-- After inserting a point at each of two distinct corners, splicing the two new outgoing
successors and deleting the inserted points is the original outgoing corner splice. -/
theorem removeNone_twice_insertAfter_mul_swap {α : Type} [DecidableEq α]
    (f : Perm α) (h k : α) (hk : h ≠ k) :
    removeNone (removeNone (insertAfter (insertAfter f h) (some k) *
      swap (some none) none)) = f * swap h k := by
  apply Equiv.ext
  intro a
  by_cases ha : a = h
  · subst a
    simp [Equiv.removeNone, Equiv.removeNoneAux, insertAfter, swap_apply_def, hk, hk.symm]
  · by_cases hak : a = k
    · subst a
      simp [Equiv.removeNone, Equiv.removeNoneAux, insertAfter, swap_apply_def]
    · simp [Equiv.removeNone, Equiv.removeNoneAux, insertAfter, ha, hak,
        swap_apply_of_ne_of_ne]

end Equiv.Perm.Insertion
