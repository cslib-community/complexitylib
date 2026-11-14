/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/List)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.List

/-!
# Literal directed word equations for joining and splitting cycles

An outgoing successor swap concatenates two nonempty directed words at their last points.
The converse isolates an adjacent pair inside a word while retaining the remaining positive
cyclic order. These are equations of actual permutations, not only orbit counts or unordered
partitions. They support contiguous vertex splits without assuming that raw ranks are retained.
-/

public section

namespace List

open Equiv

variable {α : Type*} [DecidableEq α]

/-- Joining the outgoing successors of the last points concatenates the directed words.
Only the last left point must be absent from the right word; no ambient finiteness is needed. -/
theorem formPerm_append_of_last_notMem (left right : List α) (hl : left ≠ []) (hr : right ≠ [])
    (h : left.getLast hl ∉ right) :
    (left ++ right).formPerm = left.formPerm * right.formPerm *
      Equiv.swap (left.getLast hl) (right.getLast hr) := by
  rcases left with _ | ⟨a, left⟩
  · exact (hl rfl).elim
  rcases right with _ | ⟨b, right⟩
  · exact (hr rfl).elim
  induction left generalizing a with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.getLast_singleton,
      List.formPerm_singleton, one_mul] at h ⊢
    rw [Equiv.mul_swap_eq_swap_mul, List.formPerm_apply_of_notMem h,
      List.formPerm_apply_getLast]
    rfl
  | cons x left ih =>
    simp only [List.getLast_cons_cons] at h ⊢
    change Equiv.swap a x * ((x :: left) ++ (b :: right)).formPerm =
      (a :: x :: left).formPerm * (b :: right).formPerm *
        Equiv.swap ((x :: left).getLast (by simp)) ((b :: right).getLast hr)
    rw [ih x (by simp) h, List.formPerm_cons_cons]
    simp only [mul_assoc]

/-- Splitting an adjacent pair off a directed word is the inverse of joining its two-point
cycle to the remaining word at the literal predecessor corner. The remaining order is unchanged. -/
theorem formPerm_split_adjacent_pair (left right : List α) (a b : α) (hl : left ≠ [])
    (hn : ((left ++ [a, b]) ++ right).Nodup) :
    ((left ++ [a, b]) ++ right).formPerm =
      (left ++ right).formPerm * Equiv.swap a b * Equiv.swap (left.getLast hl) b := by
  have hrot : ((right ++ left) ++ [a, b]).Nodup := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := left ++ [a, b]) (l₂ := right)).nodup_iff.mp hn
  have hsplit := List.nodup_append'.mp hrot
  have hrest : right ++ left ≠ [] := by simp [hl]
  have hnot : (right ++ left).getLast hrest ∉ [a, b] := by
    intro hm
    exact List.disjoint_left.mp hsplit.2.2 (List.getLast_mem _) hm
  have hword : ((left ++ [a, b]) ++ right).formPerm =
      ((right ++ left) ++ [a, b]).formPerm := by
    simpa only [List.append_assoc] using
      List.formPerm_eq_of_isRotated hn (List.isRotated_append (l := left ++ [a, b]))
  rw [hword, formPerm_append_of_last_notMem _ _ hrest (by simp) hnot,
    List.formPerm_pair, List.getLast_append_of_ne_nil _ hl]
  have hrem := List.formPerm_eq_of_isRotated hsplit.1
    (List.isRotated_append (l := right) (l' := left))
  simp only [hrem, List.getLast_cons_cons, List.getLast_singleton]

end List
