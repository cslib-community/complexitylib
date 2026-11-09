/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import CslibFrontier.Computability.Complexity.Problems.HornSAT
import Mathlib.Tactic.FinCases

/-! Regression cases for Horn closure, least models, sparse binary labels and duality. -/

open Cslib.Logic Cslib.Logic.PL Cslib.Complexity

example : HornSAT.solve ([] : CNF ℕ) = true := by decide
example : HornSAT.solve ([[]] : CNF ℕ) = false := by decide
example : HornSAT.solve ([[(0, false)]] : CNF ℕ) = true := by decide
example : HornSAT.solve ([[(0, true)], [(0, false)]] : CNF ℕ) = false := by decide

-- Reverse order requires successive simultaneous passes, ending in a negative-only conflict.
example : HornSAT.solve ([[(2, false)], [(1, false), (2, true)],
  [(0, false), (1, true)], [(0, true)]] : CNF ℕ) = false := by decide

-- Negative repetitions and tautologies are allowed; repeated positive occurrences are counted.
example : HornSAT.solve ([[(0, false), (0, false), (1, true)],
  [(1, false), (1, true)], [(0, true)]] : CNF ℕ) = true := by decide
example : HornSAT.solve ([[(0, true), (0, true)]] : CNF ℕ) = false := by decide
example : HornSAT.solve ([[(0, true), (1, true)]] : CNF ℕ) = false := by decide

-- Resource bounds depend on occurrences and bit lengths, not on the largest label's value.
example : HornSAT.solve ([[(2 ^ 100, true)], [(2 ^ 100, false), (7, true)],
  [(7, false)]] : CNF ℕ) = false := by decide
example : (HornSAT.forced ([[(2 ^ 100, true)]] : CNF ℕ) 2).length = 1 := by decide

example : DualHornSAT.solve ([[(0, true), (1, true)], [(0, false)]] : CNF ℕ) = true := by decide
example : DualHornSAT.solve ([[(0, true)], [(0, false)]] : CNF ℕ) = false := by decide
example : DualHornSAT.solve ([[]] : CNF ℕ) = false := by decide

example : ∃ φ : CNF (Fin 0), φ.IsHorn ∧
    ∀ a, a ∈ (∅ : Set (Fin 0 → Bool)) ↔ φ.eval a = true :=
  (isPolymorphism_and_iff_exists_hornCNF _).mp (by
    intro a ha
    exact (ha 0).elim)

example : ∃ φ : CNF (Fin 0), φ.IsDualHorn ∧
    ∀ a, a ∈ (Set.univ : Set (Fin 0 → Bool)) ↔ φ.eval a = true :=
  (isPolymorphism_or_iff_exists_dualHornCNF _).mp (by intro a ha; trivial)

-- The implication relation is intersection-closed, hence has a Horn definition.
example : ∃ φ : CNF (Fin 2), φ.IsHorn ∧
    ∀ a, (a 0 = true → a 1 = true) ↔ φ.eval a = true := by
  refine (isPolymorphism_and_iff_exists_hornCNF
    {a : Fin 2 → Bool | a 0 = true → a 1 = true}).mp ?_
  rw [isPolymorphism_and_iff]
  intro x hx y hy h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨hx h.1, hy h.2⟩

-- A positive binary clause is not Horn-definable without auxiliaries.
example : ¬ ∃ φ : CNF (Fin 2), φ.IsHorn ∧
    ∀ a, (a 0 || a 1) = true ↔ φ.eval a = true := by
  intro hdef
  have h := (isPolymorphism_and_iff_exists_hornCNF
    {a : Fin 2 → Bool | (a 0 || a 1) = true}).mpr hdef
  rw [isPolymorphism_and_iff] at h
  have ht := h (fun i => i == 0) (by decide) (fun i => i == 1) (by decide)
  have hf : (fun i : Fin 2 => (i == 0) && (i == 1)) = fun _ => false := by
    funext i
    fin_cases i <;> rfl
  simp [hf] at ht
