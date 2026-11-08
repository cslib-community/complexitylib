/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem
public import Mathlib.GroupTheory.Perm.Option

/-!
# Inserting one dart at a specified corner

The new dart is inserted immediately after the specified old dart. The successor equations
fix the orientation, including when the old vertex cycle is a singleton. The orbit
correspondence includes fixed points; counting only nontrivial permutation factors would
lose unary faces. These are permutation ingredients for indexed rotation surgery, with no
geometric interpretation or genus-preservation assertion on their own.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem.DartInsertion

open Equiv

variable {α : Type} [DecidableEq α]

/-- Insert `none` after `h` in the cycle of `f`, preserving every other successor. -/
@[expose] def insertAfter (f : Perm α) (h : α) : Perm (Option α) :=
  f.optionCongr * swap (some h) none

/-- The chosen old dart leads to the inserted dart. -/
@[simp] theorem insertAfter_at (f : Perm α) (h : α) :
    insertAfter f h (some h) = none := by
  simp [insertAfter]

/-- The inserted dart leads to the old successor of its corner. -/
@[simp] theorem insertAfter_none (f : Perm α) (h : α) :
    insertAfter f h none = some (f h) := by
  simp [insertAfter]

/-- All other old successors remain literally unchanged. -/
theorem insertAfter_other (f : Perm α) (h a : α) (ha : a ≠ h) :
    insertAfter f h (some a) = some (f a) := by
  simp [insertAfter, swap_apply_of_ne_of_ne, ha]

/-- Collapse just the inserted dart to its preceding corner. -/
@[expose] def collapse (h : α) : Option α → α := Option.elim' h id

private theorem sameCycle_collapse_step (f : Perm α) (h : α) (x : Option α) :
    f.SameCycle (collapse h x) (collapse h (insertAfter f h x)) := by
  cases x with
  | none => simpa only [collapse, insertAfter_none, Option.elim'_none, Option.elim'_some,
      id_eq] using (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.rfl : f.SameCycle h h))
  | some a =>
    by_cases ha : a = h
    · subst a
      simp only [insertAfter_at, collapse, Option.elim'_some, Option.elim'_none, id_eq]
      exact .rfl
    · simpa only [insertAfter_other f h a ha, collapse, Option.elim'_some, id_eq] using
        (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.rfl : f.SameCycle a a))

private theorem sameCycle_some_step (f : Perm α) (h a : α) :
    (insertAfter f h).SameCycle (some a) (some (f a)) := by
  by_cases ha : a = h
  · subst a
    have h₁ : (insertAfter f h).SameCycle (some h) none := by
      rw [← insertAfter_at f h]
      exact Perm.sameCycle_apply_right.mpr .rfl
    have h₂ : (insertAfter f h).SameCycle none (some (f h)) := by
      rw [← insertAfter_none f h]
      exact Perm.sameCycle_apply_right.mpr .rfl
    exact h₁.trans h₂
  · rw [← insertAfter_other f h a ha]
    exact Perm.sameCycle_apply_right.mpr .rfl

/-- Insertion preserves exactly the old cycles, and places the new dart in the corner's cycle.
This includes singleton cycles and makes no distinct-vertex assumption. -/
theorem sameCycle_iff [Finite α] (f : Perm α) (h : α) (x y : Option α) :
    (insertAfter f h).SameCycle x y ↔ f.SameCycle (collapse h x) (collapse h y) := by
  constructor
  · intro hxy
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    have hi (n : ℕ) : f.SameCycle (collapse h x)
        (collapse h ((insertAfter f h)^[n] x)) := by
      induction n with
      | zero => exact .rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (sameCycle_collapse_step f h _)
    simpa only [Perm.iterate_eq_pow, hk] using hi k
  · intro hxy
    have lift {a b : α} (hab : f.SameCycle a b) :
        (insertAfter f h).SameCycle (some a) (some b) := by
      obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
      have hi (n : ℕ) : (insertAfter f h).SameCycle (some a) (some (f^[n] a)) := by
        induction n with
        | zero => exact .rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply']
          exact ih.trans (sameCycle_some_step f h _)
      simpa only [Perm.iterate_eq_pow, hk] using hi k
    have link (z : Option α) :
        (insertAfter f h).SameCycle z (some (collapse h z)) := by
      cases z with
      | none =>
        change (insertAfter f h).SameCycle none (some h)
        rw [← insertAfter_at f h]
        exact Perm.sameCycle_apply_left.mpr .rfl
      | some a => exact .rfl
    exact (link x).trans ((lift hxy).trans (link y).symm)

/-- Every cycle, including a fixed point, survives insertion exactly once. -/
noncomputable def orbitEquiv [Finite α] (f : Perm α) (h : α) :
    Quotient (Perm.SameCycle.setoid (insertAfter f h)) ≃
      Quotient (Perm.SameCycle.setoid f) where
  toFun := Quotient.map (collapse h) (fun _ _ => (sameCycle_iff f h _ _).mp)
  invFun := Quotient.map some (fun a b hab => (sameCycle_iff f h _ _).mpr hab)
  left_inv := by
    intro q
    refine Quotient.inductionOn q fun x => ?_
    apply Quotient.sound
    apply (sameCycle_iff f h _ _).mpr
    cases x <;> exact .rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q fun a => ?_
    rfl

/-- The number of all cycles is unchanged by inserting a dart in an existing cycle. -/
theorem card_orbits_insertAfter [Finite α] (f : Perm α) (h : α) :
    Nat.card (Quotient (Perm.SameCycle.setoid (insertAfter f h))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) :=
  Nat.card_congr (orbitEquiv f h)

/-- Deleting a non-singleton dart and reinserting it after its predecessor recovers the
literal permutation, including its orientation. `removeNone` is Mathlib's deletion. -/
theorem insertAfter_removeNone (f : Perm (Option α)) (h : α)
    (hh : f (some h) = none) : insertAfter (removeNone f) h = f := by
  apply Equiv.ext
  intro x
  cases x with
  | none =>
    rw [insertAfter_none]
    exact removeNone_none f hh
  | some a =>
    by_cases ha : a = h
    · subst a
      exact (insertAfter_at _ _).trans hh.symm
    · rw [insertAfter_other _ _ _ ha]
      have hn : f (some a) ≠ none := by
        intro he
        exact ha (Option.some.inj (f.injective (he.trans hh.symm)))
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hn
      exact removeNone_some f ⟨b, hb⟩

omit [DecidableEq α] in
/-- Removing a dart from a cycle of length at least two preserves all remaining orbit
identifications; the two adjacent successors are joined with their original direction. -/
theorem sameCycle_removeNone_iff [Finite α] (f : Perm (Option α))
    (hn : f none ≠ none) (a b : α) :
    Perm.SameCycle (removeNone f) a b ↔ f.SameCycle (some a) (some b) := by
  classical
  have hp : f.symm none ≠ none := by
    intro he
    exact hn (by simpa only [he] using f.apply_symm_apply none)
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hp
  have he : f (some h) = none := by rw [← hh, f.apply_symm_apply]
  conv_rhs => rw [← insertAfter_removeNone f h he]
  rw [sameCycle_iff]
  rfl

omit [DecidableEq α] in
/-- Deleting a non-singleton dart preserves the total number of faces or vertex cycles. -/
theorem card_orbits_removeNone [Finite α] (f : Perm (Option α)) (hn : f none ≠ none) :
    Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) := by
  classical
  have hp : f.symm none ≠ none := by
    intro he
    exact hn (by simpa only [he] using f.apply_symm_apply none)
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp hp
  have he : f (some h) = none := by rw [← hh, f.apply_symm_apply]
  conv_rhs => rw [← insertAfter_removeNone f h he]
  exact (card_orbits_insertAfter (removeNone f) h).symm

end Cslib.Complexity.Graph.RotationSystem.DartInsertion
