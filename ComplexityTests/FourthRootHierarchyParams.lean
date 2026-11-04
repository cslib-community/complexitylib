/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.FourthRootHierarchyParams
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the regular fourth-moment hierarchy witness

The examples use the concrete existence construction at `q = 2`, derive nonzero ramp and exact
plateau values, use complementary root regularity at a closed row gate, and pass the strengthened
parameters into the existing stage API on a nonzero two-vertex transition matrix.
-/

namespace ComplexityTests.FourthRootHierarchyParams

open Matrix
open scoped NNReal

-- The actual witness has zero correction below its threshold, unbounded correction above it,
-- and the prescribed copy/row plateaus. These values use no extra cutoff assumptions.
example : ∃ P : FourthRootHierarchyParams 2 1 1 1 0,
    P.Q 0 = 0 ∧ 1 ≤ P.Q (P.θ₂ + 1) ∧ P.χ (1 / 16) = 0 ∧ P.χ (1 / 8) = 1 ∧
      P.ρ P.η₂ = 0 ∧ P.κ (1 / 2) = 1 := by
  obtain ⟨P⟩ := FourthRootHierarchyParams.nonempty (q := 2) (cπ := 1) (Cπ := 1)
    (Cpair := 1) (Cvar := 0) (by norm_num) (by norm_num)
  refine ⟨P, ?_, ?_, ?_, ?_, P.ρ_zero _ le_rfl, P.κ_one_ge _ le_rfl⟩
  · apply le_antisymm _ (P.Q_nonneg 0)
    simpa only [max_eq_right (by linarith [P.θ_pos] : (0 : ℝ) - P.θ ≤ 0)] using P.Q_le 0
  · have h := P.le_Q (P.θ₂ + 1)
    linarith
  · apply P.χ_zero
    rw [P.τ₀_eq]
    norm_num
  · apply P.χ_one
    rw [P.τ₁_eq]
    norm_num

-- The row gate closes strictly before the detector entry factor can become nonzero.
example (P : FourthRootHierarchyParams 2 1 1 1 0) :
    3 * P.η₂ < P.δ₀ ∧ P.ϕ (3 * P.η₂) = 0 := by
  have h : 3 * P.η₂ < P.δ₀ := by linarith [P.η₂_lt]
  exact ⟨h, P.ϕ_zero _ h.le⟩

-- Root regularity gives a perturbation bound at the closed endpoint of the actual row gate.
example (P : FourthRootHierarchyParams 2 1 1 1 0) :
    ∃ K : ℝ≥0, ∀ t : ℝ, |P.ρ t ^ (4⁻¹ : ℝ)| ≤ K * |t - P.η₂| := by
  obtain ⟨K, hK⟩ := (P.cutoff_roots P.ρ (by simp)).1
  refine ⟨K, fun t => ?_⟩
  have h := hK.dist_le_mul t P.η₂
  rw [P.ρ_zero _ le_rfl, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0)] at h
  simpa only [Real.dist_eq, sub_zero] using h

/-- One edge of weight `1/2` on two vertices. -/
private noncomputable def C : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 2; 0, 0]

-- Existing stage theorems consume the parent interface directly: the constructed cutoffs give
-- a nonnegative and substochastic next transition on the copied vertices of this nonzero input.
example : ∃ P : FourthRootHierarchyParams 2 1 1 1 0,
    let X : Unit → Fin 2 → Prop := fun _ _ => True
    let A := P.toHierarchyParams.next X X 1 C
    (∀ x y, 0 ≤ A x y) ∧ A *ᵥ 1 ≤ 1 := by
  obtain ⟨P⟩ := FourthRootHierarchyParams.nonempty (q := 2) (cπ := 1) (Cπ := 1)
    (Cpair := 1) (Cvar := 0) (by norm_num) (by norm_num)
  have hC : ∀ x y, 0 ≤ C x y := by intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]
  have hC1 : C *ᵥ 1 ≤ 1 := by intro x; fin_cases x <;> norm_num [C, mulVec, dotProduct]
  refine ⟨P, ?_, ?_⟩
  · exact P.toHierarchyParams.next_nonneg (by norm_num) hC
  · exact P.toHierarchyParams.next_mulVec_one_le (by norm_num) hC hC1

end ComplexityTests.FourthRootHierarchyParams
