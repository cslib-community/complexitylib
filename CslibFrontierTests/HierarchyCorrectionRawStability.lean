/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of changing actual correction children)
import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyCorrectionRawStability

/-! Nonzero RAW/PREP perturbations of the actual correction, on one shared environment. -/
set_option linter.privateModule false
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace CorrectionChildrenRegression

private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 2) (ZMod 5) :=
  ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 0 [1],
    gridChannel 1 0 [2, 3], gridChannel 1 0 [2, 3]⟩

private def value (HP : FourthRootHierarchyParams 16 1 16 32 8) (a b : ℝ)
    (σ : Environment 5 2) : ℝ :=
  correctionRequest 1 (fun _ : Unit => 0) (request HP)
    (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
    HP.γ HP.K 2 (fun _ _ _ => a) (fun _ _ _ => b) (fun _ _ => 0) σ () ()

private lemma value_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (a b : ℝ) (σ : Environment 5 2) :
    value HP a b σ = HP.toHierarchyParams.atomCutoff a / max (1/2) (min 1 b) := by
  have hr : Admissible (request HP) := ⟨by change (0 : Fin 2) ≠ 1; decide, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  have hK : 1 < HP.K := by
    have hg := HP.gate
    have hn : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
    have hk : (1 : ℝ) < HP.K := by linarith
    exact_mod_cast hk
  have hτ : HP.incomingCutoff 0 = 1 :=
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  unfold value correctionRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [CorrectionRowRecipe.normalized, coordinate, request, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  norm_num [rate, rowGate, incomingGate, kthLargest, Finset.univ_unique,
    not_le.mpr hK, CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hτ,
    HP.γ_one 0 (by norm_num)]

-- RAW alone changes an actual positive output; PREP alone changes its actual denominator.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    0 < value HP (1/2) 1 σ ∧ value HP (1/2) 1 σ < value HP 1 1 σ ∧
      value HP 1 (1/2) σ = 2 * value HP 1 1 σ ∧
      value HP (1/2) (1/2) σ = 2 * value HP (1/2) 1 σ := by
  have hhalf := HP.toHierarchyParams.atomCutoff_eq (by norm_num : (0:ℝ) ≤ 1/2)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)
  have hone := HP.toHierarchyParams.atomCutoff_eq (by norm_num : (0:ℝ) ≤ 1)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)
  have hl := HP.le_Q (1/2)
  have hu := HP.Q_le (1/2)
  have hl1 := HP.le_Q 1
  have hθ := HP.θ₂_lt
  have hθ0 := HP.θ_pos
  have hθ2 := HP.θ_lt_θ₂
  have hh : 0 < (1/2:ℝ) - HP.θ := by norm_num at hθ; linarith
  rw [max_eq_left hh.le] at hu
  simp only [value_eq, hhalf, hone]
  norm_num
  norm_num at hθ
  refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> ring

-- Negative completed RAW and PREP children are allowed by the actual decoder.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    value HP (-7) (-11) σ = 0 ∧ value HP 1 (-11) σ = value HP 1 (1/2) σ := by
  simp only [value_eq, HP.toHierarchyParams.atomCutoff_eq_zero (by norm_num : (-7:ℝ) ≤ 0)]
  norm_num

-- Empty conditioning sets contribute zero; no fictitious independent seed is introduced.
example (prep prep' : Unit × Unit → Matrix Unit Unit ℝ) :
    CorrectionRowRecipe.normalizer (fun _ _ => False) (fun _ _ => True) prep () () = 0 ∧
    (𝔼 p ∈ ({_s : Unit | False} : Finset Unit) ×ˢ (univ : Finset Unit),
      |prep p () () - prep' p () ()|) = 0 := by
  simp [CorrectionRowRecipe.normalizer]

private lemma rank_empty {V : Type*} (k : ℕ) (h : V → ℝ) :
    kthLargest k ∅ h = 0 := by simp [kthLargest]

-- The actual row and column ranks both matter, independently, on the same finite sets.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let A : Matrix (Fin HP.K) (Fin HP.K) ℝ := fun _ _ => 1
    let x : Fin HP.K := ⟨0, FourthRootHierarchyParams.NormalizedRow.rank_pos HP⟩
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K 1 1 A
        (polynomialPrepCutoff4 HP.θ) HP.ρ ∅ ∅ x x = 1 ∧
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K 1 1 A
        (polynomialPrepCutoff4 HP.θ) HP.ρ ∅ univ x x = 0 ∧
    correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K 1 1 A
        (polynomialPrepCutoff4 HP.θ) HP.ρ univ ∅ x x = 0 := by
  have hK := FourthRootHierarchyParams.NormalizedRow.rank_pos HP
  have hk : kthLargest HP.K (univ : Finset (Fin HP.K)) (fun _ => (1:ℝ)) = 1 := by
    apply le_antisymm (kthLargest_le (by norm_num) (fun _ _ => le_rfl))
    apply (le_kthLargest_iff hK (by norm_num : (0:ℝ) < 1)).mpr
    simp only [le_refl, filter_true, card_univ, Fintype.card_fin]
  have hk1 : kthLargest 1 (univ : Finset (Fin HP.K)) (fun _ => (1:ℝ)) = 1 := by
    apply le_antisymm (kthLargest_le (by norm_num) (fun _ _ => le_rfl))
    apply (le_kthLargest_iff (by decide) (by norm_num : (0:ℝ) < 1)).mpr
    simpa only [le_refl, filter_true, card_univ, Fintype.card_fin] using Nat.succ_le_of_lt hK
  have hρ0 := HP.ρ_one 0 HP.η_pos.le
  have hρ1 : HP.ρ 1 = 0 := HP.ρ_zero 1 (by
    linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_lt_θ₂, HP.θ₂_lt])
  have hτ0 : HP.incomingCutoff 0 = 1 := HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  have hτ1 : HP.incomingCutoff 1 = 0 := HP.incomingCutoff_zero (by rw [HP.τ₁_eq]; norm_num)
  have hp : polynomialPrepCutoff4 HP.θ 1 = 1 := polynomialPrepCutoff4_eq_one HP.θ_pos
    (by linarith [HP.θ_lt_θ₂, HP.θ₂_lt])
  have hi : polynomialAuxCutoff4 HP.θ 1 0 = 1 := polynomialAuxCutoff4_eq_one HP.θ_pos
    (by linarith [HP.θ_lt_θ₂, HP.θ₂_lt]) (by linarith [HP.θ_pos])
  dsimp only
  simp only [correctionPrep, rowGate, incomingGate, auxScore, div_one, rank_empty,
    hk, hk1, hp, hi, hρ0, hρ1, hτ0, hτ1, mul_one, mul_zero,
    and_self]

-- Different negative RAW/PREP children leave the zero output unchanged.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 2) :
    value HP (-7) (-11) σ = value HP (-9) 1 σ := by
  simp only [value_eq, HP.toHierarchyParams.atomCutoff_eq_zero (by norm_num : (-7:ℝ) ≤ 0),
    HP.toHierarchyParams.atomCutoff_eq_zero (by norm_num : (-9:ℝ) ≤ 0), zero_div]

-- Empty vertex domains contribute exactly zero even when every child family changes.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rootDistPow 4 5 1 (fun (_ : Environment 5 2) (_ : Fin 0) => True)
      (fun _ _ => True)
      (correctionRequest 1 Fin.elim0 (request HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K 2
        (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0))
      (correctionRequest 1 Fin.elim0 (request HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K 2
        (fun _ _ _ => -3) (fun _ _ _ => -2) (fun _ _ => 1)) = 0 := by
  simp [rootDistPow, rowNormPow]

end CorrectionChildrenRegression
