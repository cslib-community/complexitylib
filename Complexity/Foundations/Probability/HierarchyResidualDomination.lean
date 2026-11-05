/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTaskData

/-!
# Positive input domination by the signed hierarchy residual

The actual ramp removes at least `θ * f` whenever its correction is positive.
Consequently the positive input `C + E C` is dominated by the genuine signed
residual `C + E C - E`, with a structural constant independent of the field,
rate and source. This uses the actual recurrence and substochastic base, not
an accuracy assumption about the parent or a positivity assumption about a
signed grouping. These are original consequences of the hierarchy's ramp gap.
-/

public section
noncomputable section
open Finset
open scoped BigOperators
namespace Matrix.HierarchyParams
variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f : ℝ} {C : Matrix V V ℝ}

/-- A positive final correction leaves the actual ramp gap in the signed residual.
This holds without triangularity, including non-unit substochastic examples. -/
theorem theta_mul_le_residual_of_correction_pos (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) {x y : V}
    (he : 0 < P.correction X Y f C x y) :
    P.θ * f ≤ P.residual X Y f C x y := by
  cases hk : P.k with
  | zero =>
    simp only [correction_eq, hk, cutoffCorrectionIter] at he
    exact False.elim (lt_irrefl _ he)
  | succ j =>
    have hm (z : V) : P.correctionIter X Y f C j x z ≤
        P.correction X Y f C x z := by
      rw [← P.correctionIter_last X Y f C, hk]
      exact cutoffCorrectionIter_le_succ hC
        (fun y t => mul_nonneg (P.cutoff_nonneg hf t) (P.γ_nonneg (P.pilot X Y f C y)))
        (fun y => (P.cutoff_mono hf).mul_const (P.γ_nonneg (P.pilot X Y f C y))) j x z
    have hi : P.correctionInput X Y f C j x y ≤
        C x y + (P.correction X Y f C * C) x y := by
      simp only [correctionInput, Matrix.add_apply, Matrix.mul_apply]
      exact add_le_add le_rfl (sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_right (hm z) (hC z y))
    have heq : P.correction X Y f C x y =
        P.cutoff f (P.correctionInput X Y f C j x y) * P.γ (P.pilot X Y f C y) := by
      rw [← P.correctionIter_last X Y f C, hk, P.correctionIter_succ_apply]
      rw [P.cutoff_apply]
    have hb : P.correction X Y f C x y ≤
        max (P.correctionInput X Y f C j x y - P.θ * f) 0 := by
      rw [heq]
      exact (mul_le_of_le_one_right (P.cutoff_nonneg hf _) (P.γ_le_one _)).trans
        (P.cutoff_le hf _)
    have hp : 0 ≤ P.correctionInput X Y f C j x y - P.θ * f := by
      by_contra h
      rw [max_eq_right (le_of_not_ge h)] at hb
      linarith
    rw [max_eq_left hp] at hb
    rw [P.residual_eq, Matrix.add_apply, Matrix.sub_apply]
    linarith

/-- The legitimate positive input is dominated by the final signed residual.
The constant depends only on the fixed hierarchy parameters. Zero correction and
zero residual are included; no division by the residual is used. -/
theorem correctionInput_last_le_residual (hf : 0 < f)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) (x y : V) :
    P.correctionInput X Y f C P.k x y ≤
      max 1 (((P.k : ℝ) + 1) / P.θ) * P.residual X Y f C x y := by
  have hn := P.residual_nonneg (X := X) (Y := Y) hf hC x y
  have he := (P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC).nonneg P.k x y
  rw [P.correctionIter_last] at he
  by_cases hz : P.correction X Y f C x y = 0
  · have hid : P.correctionInput X Y f C P.k x y = P.residual X Y f C x y := by
      simp only [correctionInput, P.correctionIter_last, P.residual_eq,
        Matrix.add_apply, Matrix.sub_apply, hz, sub_zero]
    rw [hid]
    exact le_mul_of_one_le_left hn (le_max_left _ _)
  · have hg := P.theta_mul_le_residual_of_correction_pos X Y hf hC
      (lt_of_le_of_ne he (Ne.symm hz))
    have hb := (P.correctionInput_bounds (X := X) (Y := Y) hf hC hC1 hCf P.k).2.2 x y
    have hc : 0 ≤ ((P.k : ℝ) + 1) / P.θ := div_nonneg (by positivity) P.θ_pos.le
    calc
      _ ≤ ((P.k : ℝ) + 1) * f := hb
      _ = (((P.k : ℝ) + 1) / P.θ) * (P.θ * f) := by
        field_simp [P.θ_pos.ne']
      _ ≤ (((P.k : ℝ) + 1) / P.θ) * P.residual X Y f C x y :=
        mul_le_mul_of_nonneg_left hg hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hn

end Matrix.HierarchyParams
