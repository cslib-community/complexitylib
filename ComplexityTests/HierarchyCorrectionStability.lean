/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual correction maximum sensitivity)
import Complexity.Foundations.Probability.HierarchyCorrectionStability

/-! A nonzero actual incoming-normalized request responds to its pilot multiplier. -/
set_option linter.privateModule false
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace CorrectionMaximumRegression

private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 2) (ZMod 5) :=
  ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 1 0 [2, 3], gridChannel 1 0 [2, 3]⟩

private def value (HP : FourthRootHierarchyParams 16 1 16 32 8) (a : ℝ)
    (σ : Environment 5 2) : ℝ :=
  correctionRequest 1 (fun _ : Unit => 0) (request HP)
    (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
    HP.γ HP.K 2 (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => a) σ () ()

private lemma value_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a : ℝ) (σ : Environment 5 2) : value HP a σ = HP.Q 1 * HP.γ a := by
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  have hK : 1 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (1 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  have hcap := HP.toHierarchyParams.atomCutoff_eq (by norm_num : (0 : ℝ) ≤ 1)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)
  have hτ : HP.incomingCutoff 0 = 1 :=
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  unfold value correctionRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [CorrectionRowRecipe.normalized, coordinate, request, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  norm_num [rate, rowGate, incomingGate, kthLargest, Finset.univ_unique,
    not_le.mpr hK, CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hτ, hcap]

-- One actual nonzero child switches off when the completed maximum crosses the pilot cutoff.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    value HP 0 σ = HP.Q 1 ∧ value HP 1 σ = 0 ∧ 0 < value HP 0 σ := by
  have hQ := HP.le_Q 1
  have hθ := HP.θ₂_lt
  rw [value_eq, value_eq]
  simp only [HP.γ_one 0 (by norm_num), HP.γ_zero 1 (by norm_num), mul_one, mul_zero,
    true_and]
  norm_num at hθ
  linarith

-- The same actual request has no pilot error when both estimates lie on the one plateau.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    value HP 0 σ = value HP (1 / 4) σ := by
  rw [value_eq, value_eq, HP.γ_one 0 (by norm_num), HP.γ_one (1 / 4) (by norm_num)]

-- A dyadic improvement of the maximum estimate changes a nonzero request's actual output.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    value HP ((1 / 2 : ℝ) ^ 0) σ = 0 ∧
      value HP ((1 / 2 : ℝ) ^ 2) σ = HP.Q 1 := by
  rw [value_eq, value_eq]
  norm_num [HP.γ_zero 1 (by norm_num), HP.γ_one (1 / 4) (by norm_num)]

-- Empty vertex domains pay zero without a positivity or nonempty-source premise.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rootDistPow 4 5 1 (fun (_ : Environment 5 2) (_ : Fin 0) => True)
      (fun _ _ => True)
      (correctionRequest 1 Fin.elim0 (request HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K 2
        (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0))
      (correctionRequest 1 Fin.elim0 (request HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K 2
        (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 1)) = 0 := by
  simp [rootDistPow, rowNormPow]

end CorrectionMaximumRegression
