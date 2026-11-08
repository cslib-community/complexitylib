/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.Majority

/-! Nonvacuous examples of majority preservation, 2CNF definability and projection. -/

open Cslib Cslib.Logic Cslib.Logic.PL Cslib.BitString

-- Equality has two satisfying tuples and a width-two definition with both literal signs.
example : ∀ a : Fin 2 → Bool,
    a 0 = a 1 ↔ CNF.eval a
      ([[(0, false), (1, true)], [(0, true), (1, false)]] : CNF (Fin 2)) = true := by
  intro a
  cases h0 : a 0 <;> cases h1 : a 1 <;> simp [CNF.eval, Clause.eval, h0, h1]

private theorem equality_preserved :
    IsPolymorphism (majority 3) {a : Fin 2 → Bool | a 0 = a 1} := by
  rw [isPolymorphism_majority_iff]
  intro x hx y hy z hz
  change x 0 = x 1 at hx
  change y 0 = y 1 at hy
  change z 0 = z 1 at hz
  change median x y z 0 = median x y z 1
  simp only [median, hx, hy, hz]

example : IsPolymorphism (majority 3)
    {a : Unit → Bool | ∃ b ∈ {b : Fin 2 → Bool | b 0 = b 1},
      b ∘ (fun _ : Unit => (0 : Fin 2)) = a} :=
  equality_preserved.project (fun _ : Unit => (0 : Fin 2))

-- The projection of equality onto its first coordinate contains both Boolean values.
example (a : Unit → Bool) :
    a ∈ {a : Unit → Bool | ∃ b ∈ {b : Fin 2 → Bool | b 0 = b 1},
      b ∘ (fun _ : Unit => (0 : Fin 2)) = a} :=
  ⟨fun _ => a (), rfl, funext fun i => by cases i; rfl⟩

-- Three single-true tuples show that ternary disjunction is not majority-preserved.
private theorem orThree_not_polymorphism : ¬ IsPolymorphism (majority 3)
    {a : Fin 3 → Bool | (a 0 || a 1 || a 2) = true} := by
  intro h
  have hm := (isPolymorphism_majority_iff _).mp h
    ![true, false, false] (by decide) ![false, true, false] (by decide)
    ![false, false, true] (by decide)
  change (median _ _ _ 0 || median _ _ _ 1 || median _ _ _ 2) = true at hm
  norm_num [median] at hm

-- Thus the characterization rules out a definition on the same three variables by 2CNF.
example : ¬ ∃ φ : CNF (Fin 3), (∀ c ∈ φ, c.length ≤ 2) ∧
    ∀ a, (a 0 || a 1 || a 2) = true ↔ φ.eval a = true := by
  intro h
  exact orThree_not_polymorphism ((isPolymorphism_majority_iff_exists_twoCNF _).mpr h)

-- Both nullary relations occur: the empty formula is true, an empty clause is false.
example : IsPolymorphism (majority 3) (Set.univ : Set (Empty → Bool)) := by
  intro _ _
  trivial

example : IsPolymorphism (majority 3) (∅ : Set (Empty → Bool)) := by
  intro a ha
  exact (ha 0).elim

example : ∀ a : Empty → Bool, CNF.eval a ([] : CNF Empty) = true ∧
    CNF.eval a ([[]] : CNF Empty) = false := fun _ => ⟨rfl, rfl⟩

-- Nullary constant operations require the constant tuple even for an empty coordinate type.
example : ¬ IsPolymorphism (fun _ : Empty → Bool => false)
    (∅ : Set (Empty → Bool)) := by
  rw [isPolymorphism_const_iff]
  simp
