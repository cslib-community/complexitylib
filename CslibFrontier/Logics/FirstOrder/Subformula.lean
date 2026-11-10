/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.ModelTheory.Syntax
public import Mathlib.Data.Set.Finite.Basic

/-!
# Subformulas

The subformulas of a bounded formula of Mathlib's first-order logic, each with its number of bound
variables (`Cslib.Logic.FO.subformulas`). They form a finite set, closed under taking
subformulas: the operands of an implication and the body of a universal quantification of a
subformula are subformulas.

## Main definitions

* `Cslib.Logic.FO.subformulas`: the subformulas of a bounded formula.

## Main results

* `Cslib.Logic.FO.self_mem_subformulas`, `Cslib.Logic.FO.finite_subformulas`: a formula is one of
  its finitely many subformulas.
* `Cslib.Logic.FO.subformulas_subset`: the subformulas of a subformula are subformulas.
* `Cslib.Logic.FO.mem_subformulas_of_imp_left`, `Cslib.Logic.FO.mem_subformulas_of_imp_right`,
  `Cslib.Logic.FO.mem_subformulas_of_all`: closure under taking operands.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {α : Type*}

/-- The subformulas of a bounded formula, each with its number of bound variables. -/
def subformulas : ∀ {n : ℕ}, L.BoundedFormula α n → Set (Σ k, L.BoundedFormula α k)
  | n, .falsum => {⟨n, .falsum⟩}
  | n, .equal t₁ t₂ => {⟨n, .equal t₁ t₂⟩}
  | n, .rel R ts => {⟨n, .rel R ts⟩}
  | n, .imp φ ψ => insert ⟨n, .imp φ ψ⟩ (subformulas φ ∪ subformulas ψ)
  | n, .all φ => insert ⟨n, .all φ⟩ (subformulas φ)

/-- A formula is one of its own subformulas. -/
theorem self_mem_subformulas {n : ℕ} (φ : L.BoundedFormula α n) : ⟨n, φ⟩ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

/-- A formula has finitely many subformulas. -/
theorem finite_subformulas {n : ℕ} (φ : L.BoundedFormula α n) : (subformulas φ).Finite := by
  induction φ with
  | falsum => exact Set.finite_singleton _
  | equal => exact Set.finite_singleton _
  | rel => exact Set.finite_singleton _
  | imp _ _ ih₁ ih₂ => exact (ih₁.union ih₂).insert _
  | all _ ih => exact ih.insert _

/-- The subformulas of a subformula are subformulas. -/
theorem subformulas_subset {n k : ℕ} {φ : L.BoundedFormula α n} {ψ : L.BoundedFormula α k}
    (h : ⟨k, ψ⟩ ∈ subformulas φ) : subformulas ψ ⊆ subformulas φ := by
  induction φ with
  | falsum | equal | rel =>
    cases Set.mem_singleton_iff.1 h
    exact subset_rfl
  | imp φ₁ φ₂ ih₁ ih₂ =>
    rcases h with h | h | h
    · cases h
      exact subset_rfl
    · exact (ih₁ h).trans (Set.subset_union_left.trans (Set.subset_insert _ _))
    · exact (ih₂ h).trans (Set.subset_union_right.trans (Set.subset_insert _ _))
  | all φ₁ ih =>
    rcases h with h | h
    · cases h
      exact subset_rfl
    · exact (ih h).trans (Set.subset_insert _ _)

variable {n k : ℕ} {φ : L.BoundedFormula α n}

/-- The antecedent of an implication among the subformulas is a subformula. -/
theorem mem_subformulas_of_imp_left {ψ χ : L.BoundedFormula α k}
    (h : ⟨k, ψ.imp χ⟩ ∈ subformulas φ) : ⟨k, ψ⟩ ∈ subformulas φ :=
  subformulas_subset h (Set.mem_insert_of_mem _ (.inl (self_mem_subformulas ψ)))

/-- The consequent of an implication among the subformulas is a subformula. -/
theorem mem_subformulas_of_imp_right {ψ χ : L.BoundedFormula α k}
    (h : ⟨k, ψ.imp χ⟩ ∈ subformulas φ) : ⟨k, χ⟩ ∈ subformulas φ :=
  subformulas_subset h (Set.mem_insert_of_mem _ (.inr (self_mem_subformulas χ)))

/-- The body of a universal quantification among the subformulas is a subformula. -/
theorem mem_subformulas_of_all {ψ : L.BoundedFormula α (k + 1)}
    (h : ⟨k, ψ.all⟩ ∈ subformulas φ) : ⟨k + 1, ψ⟩ ∈ subformulas φ :=
  subformulas_subset h (Set.mem_insert_of_mem _ (self_mem_subformulas ψ))

end Cslib.Logic.FO
