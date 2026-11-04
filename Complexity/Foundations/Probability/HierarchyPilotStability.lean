/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyCorrectionRawStability
public import Complexity.Foundations.Probability.PilotRowStability

/-!
# Paying actual correction error from running-maximum children

This original local client composes correction stability with the actual clipped
running-maximum recipe. It pays the previous maximum and current detector children,
rather than assuming a final pilot error. RAW and PREP remain on their original masks,
with the existing width and rate costs. Child functions may share every environment
coordinate. Iterating these contracts with allocated accuracies is still open.

## Main results

* `Matrix.HierarchyParams.H4RankEnvironment.correctionRequest_pilot_children_root_moment`:
  actual correction root error paid from four changing child classes.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Cslib

/-- The actual correction consumes the completed running maximum of two supplied
children. Both are paid by their ordinary fourth moments on the same original pairs.
The current detector may be paid using `PilotRowRecipe.detector_row_moment`.
Constants are selected before prime, width, structural request, rates or child functions. -/
theorem correctionRequest_pilot_children_root_moment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Cr Cp Cm : ℝ, 0 ≤ Cr ∧ 0 ≤ Cp ∧ 0 ≤ Cm ∧
    ∀ (P J : ℕ) [Fact P.Prime] (V : Type*) [Fintype V] (k : ℕ)
      (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)) (_hr : Admissible r),
    0 < r.terminal.rate → ∀ (Kc : ℕ), 0 < Kc →
    ∀ (raw raw' prep prep' : Environment P J → Matrix V V ℝ)
      (previous current previous' current' : Environment P J → V → ℝ) (N u : ℝ),
    0 ≤ N * u →
    (∀ σ y, r.usage.retains (channels D) σ (ident y) →
      r.terminal.retains (channels D) σ (ident y)) →
    let X := fun σ x => r.source.retains (channels D) σ (ident x)
    let Y := fun σ y => r.terminal.retains (channels D) σ (ident y)
    let U := fun σ y => r.usage.retains (channels D) σ (ident y)
    rootDistPow 4 N u X Y
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw prep
        (fun σ => PilotRowRecipe.maximum (previous σ) (current σ)))
      (correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
        HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc raw' prep'
        (fun σ => PilotRowRecipe.maximum (previous' σ) (current' σ))) ≤
    64 * ((Cr / r.terminal.rate) ^ 4 * (Fintype.card V : ℝ) ^ 2 *
        rowNormPow 4 N u X Y (fun σ x y => raw σ x y - raw' σ x y) +
      Cp ^ 4 * rowNormPow 4 N u X U (fun σ x y => prep σ x y - prep' σ x y) +
      Cm ^ 4 * (rowNormPow 4 N u X Y (fun σ _ y => previous σ y - previous' σ y) +
        rowNormPow 4 N u X Y (fun σ _ y => current σ y - current' σ y))) := by
  obtain ⟨Cr, Cp, Cm, hCr, hCp, hCm, hc⟩ := correctionRequest_children_root_moment HP
  refine ⟨Cr, Cp, Cm, hCr, hCp, hCm, ?_⟩
  intro P J instP V instV k D ident r hr hf Kc hKc raw raw' prep prep'
    previous current previous' current' N u hNu hUY
  have h := hc P J V k D ident r hr hf Kc hKc raw raw' prep prep'
    (fun σ => PilotRowRecipe.maximum (previous σ) (current σ))
    (fun σ => PilotRowRecipe.maximum (previous' σ) (current' σ)) N u hNu hUY
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCm 4)
  exact PilotRowRecipe.maximum_row_moment _ _ previous current previous' current' hNu
end Matrix.HierarchyParams.H4RankEnvironment
