/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Logics.Propositional.CNF.WeightedRow

/-! # Nontrivial weighted signed row clients -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow

namespace WeightedRowTests

/-- Weights 2 and 1, with opposite polarities and demand 2. -/
def mixed : Row Bool 2 where
  support := {false, true}
  sign := id
  weight := fun i => if i then 1 else 2
  demand := 2
  positive := by intro i hi; cases i <;> decide
  bounded := by decide
  capped := by intro i hi; cases i <;> decide

example : mixed.value (fun _ => false) = 2 := by
  simp [Row.value, Row.active, mixed, Finset.sum_filter]

example : mixed.upper.eval (fun _ => false) = true ∧
    mixed.attainment.eval (fun _ => false) = true := by
  apply (row_eval _ _).mpr
  simp [Row.value, Row.active, mixed, Finset.sum_filter]

example : mixed.upper.eval (fun i => i) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have := (upper_eval mixed (fun i => i)).mp h
  simp [Row.value, Row.active, mixed] at this

example : mixed.upper.eval (fun _ => true) = true ∧
    mixed.attainment.eval (fun _ => true) = false := by
  have hv : mixed.value (fun _ => true) = 1 := by
    simp [Row.value, Row.active, mixed, Finset.sum_filter]
  constructor
  · rw [upper_eval, hv]; decide
  · apply Bool.eq_false_iff.mpr
    intro h
    have := (attainment_eval mixed (fun _ => true) (by rw [hv]; decide)).mp h
    rw [hv] at this
    contradiction

/-- Zero demand forces all literals false; its attainment term is empty. -/
def zero : Row Bool 0 where
  support := {false, true}
  sign := id
  weight := fun _ => 1
  demand := 0
  positive := by intros; decide
  bounded := by decide
  capped := by intros; decide

example : [] ∈ zero.attainment := empty_mem_attainment _ rfl

example : zero.upper.eval Bool.not = true ∧ zero.attainment.eval Bool.not = true := by
  apply (row_eval _ _).mpr
  simp [Row.value, Row.active, zero]

/-- Weight 2 cannot attain demand 1, while respecting the cap b+1. -/
def unattainable : Row Bool 1 where
  support := {false}
  sign := fun _ => true
  weight := fun _ => 2
  demand := 1
  positive := by intros; decide
  bounded := by decide
  capped := by intros; decide

example : unattainable.attainment = [] := by
  apply attainment_eq_nil
  intro s hs
  have h : s = ∅ ∨ s = {false} := Finset.subset_singleton_iff.mp hs
  rcases h with rfl | rfl <;> simp [unattainable]

example : Fintype.card {σ : Bool → Bool // mixed.value σ = mixed.demand} =
    Fintype.card {σ : Bool ⊕ Fin 0 → Bool //
      (query (fun _ : Fin 1 => mixed) false).eval σ = true} -
    Fintype.card {σ : Bool ⊕ Fin 0 → Bool //
      (query (fun _ : Fin 1 => mixed) true).eval σ = true} := by
  simpa using counting_identity (fun _ : Fin 1 => mixed)

end WeightedRowTests
