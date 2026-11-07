/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialPreparation
public import Complexity.Foundations.Probability.NormalizedAtomRows.SupportedPreparation

/-!
# Supported preparation of executed initial histories

The actual second clipped mean consumes the first clipped mean and centered noise on
the full terminal rank mask. Saturated relative stability and the two preparation
supports pay the change before conditional Jensen on the usage mask. The original
preparation and usage walk are unchanged. This finite bound does not construct the
recursive children or establish simultaneous accuracy and availability.

## Main results

* `initialSecondSignal_relative_mean_moment`: actual second mean from first statistics.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The exact executed preparation mean is paid by full-rank first statistics.
The narrower usage mask never replaces the terminal rank in the input bounds. -/
theorem initialSecondSignal_relative_mean_moment (B : BudgetData HP P) (M bin ka ku : ℕ)
    (husage : ka ≤ ku)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (hG : ∀ x y, 0 ≤ B.base x y)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) {α β : ℝ}
    (hmean : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ
        (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        0 0 j x y) ≤ α)
    (hnoise : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base
        (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        0 0 j) ≤ β) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ
        (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        0 1 j x y) ≤
      8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4 * (α + β) := by
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Yu := retainedMask R.terminal (side P ku) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hm := hmean
  simp_rw [actualClippedMean_first_prefix_eq] at hm
  have hn := hnoise
  change rowNormPow 4 P r.source.rate Xs
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun σ x y => actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka B.base
      (firstSignalIncrement F ka
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
      0 0 j σ x y) ≤ β at hn
  simp_rw [actualNoiseEntry_first_prefix R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st F ka B.base
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) 0
    (by intros; rfl)] at hn
  have hden (x y : ZMod P) : rate ka * (1 + B.base x y / rate ka) =
      rate ka + B.base x y := by field_simp [(rate_pos ka).ne']
  simp_rw [hden] at hn
  have hb := selectedPreparation_relative_mean_moment HP
    (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) B.padding R ks ka ku husage
    ss st hLh hLρ hh hρ (F (j + 1)) B.base hG hNu ζ hm hn
  have he (x y : ZMod P) :
      actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base ζ
        (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        0 1 j x y =
      min 1 (|ζ| * |rowSliceMean Xs Yu
        (fun σ x y => selectedPreparation HP B.padding R st ka (F (j + 1)) σ x y -
          selectedPreparation HP B.padding R st ka (fun _ => B.base) σ x y) x y|) := by
    unfold actualClippedMean twoMaskMean
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
    unfold rowSliceMean
    have hp (σ : Environment P 3) :
        actualPrefix (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
          0 j σ x y 1 = ζ * W[j]?.getD 0 σ x y := by
      change actualPrefix _ (fun _ _ _ _ => 0) j σ x y 1 = _
      simpa only [Nat.add_sub_cancel] using actualPrefix_twoSignal_second F
        (fun i σ x y => W[i - 1]?.getD 0 σ x y) ka ζ j σ x y
    simp only [hp]
    rw [← mul_expect]
    change min 1 |ζ * rowSliceMean _ _ (W[j]?.getD 0) x y - ζ * _| = _
    rw [B.preparationWalks_mean M bin r R ks ku ss st hs hu F W hW j hj x y,
      B.binPreparation_eq_selected bin r R ka st ht haux, ← mul_sub, abs_mul]
    simp only [Xs, Yu, rowSliceMean, expect_sub_distrib, selectedPreparation,
      genuineMean, Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments.genuinePrep,
      DenseRowRecipe.preparation, retainedMask]
  simpa only [he] using hb

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
