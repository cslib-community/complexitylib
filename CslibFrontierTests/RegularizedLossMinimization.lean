/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.LossMinimization.Hinge
import CslibFrontierTests.LossMinimization

/-! Checks for replace-one stability and regularized loss minimization: the replace-one identity
and the failure of stability for a rule that memorizes its sample, the Soft-SVM bound for a
two-point problem with an existing Soft-SVM rule, and the convex-Lipschitz-bounded bound with
concrete numbers. -/

namespace CslibFrontierTests.RegularizedLossMinimization

open Cslib.MachineLearning MeasureTheory
open CslibFrontierTests.LossMinimization

/-! ### A rule that memorizes its sample is not stable -/

/-- The absolute loss of the prediction `w` against the label `1` on `true` and `0` on `false`. -/
noncomputable def bitAbsLoss (w : ℝ) (z : Bool) : ℝ := |w - if z then 1 else 0|

/-- The rule that predicts the label of its only example. -/
noncomputable def memorize (S : Fin 1 → Bool) : ℝ := if S 0 then 1 else 0

theorem trueRisk_bitAbsLoss_memorize (S : Fin 1 → Bool) :
    trueRisk bitAbsLoss uniformBool (memorize S) = 1 / 2 := by
  rw [trueRisk_def, integral_fintype Integrable.of_finite]
  simp only [uniformBool, measureReal_def, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, Fintype.sum_bool, bitAbsLoss, memorize, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]
  cases S 0 <;> norm_num

theorem empiricalRisk_bitAbsLoss_memorize (S : Fin 1 → Bool) :
    empiricalRisk bitAbsLoss S (memorize S) = 0 := by
  rw [empiricalRisk_eq_sum_div]
  cases h : S 0 <;> simp [bitAbsLoss, memorize, h]

/-- The memorizing rule has expected replace-one gap `1 / 2` under the uniform distribution. -/
theorem replaceOneGap_memorize : replaceOneGap bitAbsLoss uniformBool memorize = 1 / 2 := by
  rw [← integral_trueRisk_sub_empiricalRisk bitAbsLoss uniformBool one_pos memorize
    Integrable.of_finite fun _ => Integrable.of_finite]
  simp only [trueRisk_bitAbsLoss_memorize, empiricalRisk_bitAbsLoss_memorize, sub_zero,
    integral_const, probReal_univ, one_smul]

/-- So the memorizing rule is not replace-one stable at any rate below `1 / 2`. -/
example {ε : ℝ} (hε : ε < 1 / 2) : ¬IsReplaceOneStable bitAbsLoss memorize ε := fun h => by
  have := h uniformBool
  rw [replaceOneGap_memorize] at this
  linarith

/-- A rule that ignores its sample is stable at rate `0`. -/
example : IsReplaceOneStable bitAbsLoss (fun _ : Fin 1 → Bool => (1 / 2 : ℝ)) 0 :=
  isReplaceOneStable_of_forall_le le_rfl fun _ _ _ _ => by simp

/-! ### Soft-SVM on two points -/

/-- The feature `±1` of a point of `Bool`. -/
noncomputable def feature (z : Bool) : ℝ := if z then 1 else -1

/-- Each point is labelled by its own feature, so the predictor `1` has margin `1`. -/
theorem hingeLoss_one_feature (z : Bool) : hingeLoss (1 : ℝ) (feature z) (feature z) = 0 :=
  hingeLoss_eq_zero <| by cases z <;> norm_num [feature]

theorem abs_feature (z : Bool) : |feature z| = 1 := by cases z <;> norm_num [feature]

theorem norm_feature_le (z : Bool) : ‖feature z‖ ≤ ((1 : NNReal) : ℝ) := by
  rw [Real.norm_eq_abs, abs_feature, NNReal.coe_one]

/-- The hinge loss of the two-point problem is `1`-Lipschitz. -/
theorem lipschitzWith_hingeLoss_feature (z : Bool) :
    LipschitzWith 1 fun w : ℝ => hingeLoss w (feature z) (feature z) :=
  lipschitzWith_hingeLoss_of_le (norm_feature_le z) (abs_feature z).le

/-- A Soft-SVM rule with `r = 1 / 10` exists on samples of any size. -/
theorem exists_softSVM (m : ℕ) : ∃ A : (Fin m → Bool) → ℝ,
    IsRLM (fun w z => hingeLoss w (feature z) (feature z)) (fun w => 1 / 10 * ‖w‖ ^ 2)
      Set.univ A :=
  exists_isRLM_tikhonov isClosed_univ Set.univ_nonempty
    (fun z => (continuous_hingeLoss _ _).continuousOn)
    (fun w _ z => hingeLoss_nonneg w _ _) (by norm_num) m

/-- On `100` examples, every Soft-SVM rule with `r = 1 / 10` has expected hinge risk at most
`1 / 10 + 2 / 10 = 3 / 10` under every distribution. -/
example (D : Measure Bool) [IsProbabilityMeasure D] (A : (Fin 100 → Bool) → ℝ)
    (hA : IsRLM (fun w z => hingeLoss w (feature z) (feature z)) (fun w => 1 / 10 * ‖w‖ ^ 2)
      Set.univ A) :
    ∫ S, trueRisk (fun w z => hingeLoss w (feature z) (feature z)) D (A S)
      ∂(Measure.pi fun _ : Fin 100 => D) ≤ 3 / 10 := by
  have h := hA.integral_trueRisk_hingeLoss_le (ρ := 1) norm_feature_le
    (fun z => (abs_feature z).le) (by norm_num) D (by norm_num) Integrable.of_finite
    (fun _ => Integrable.of_finite) 1 Integrable.of_finite
  have h0 : trueRisk (fun w z => hingeLoss w (feature z) (feature z)) D 1 = 0 := by
    simp only [trueRisk_def, hingeLoss_one_feature, integral_zero]
  rw [h0] at h
  norm_num at h
  linarith

/-! ### A convex-Lipschitz-bounded problem -/

/-- On `800` examples with `ρ = B = 1`, Tikhonov RLM with `r = √(2 / 800) = 1 / 20` on the unit
ball has expected hinge risk within `√(8 / 800) = 1 / 10` of every predictor in the ball. -/
example (D : Measure Bool) [IsProbabilityMeasure D] (A : (Fin 800 → Bool) → ℝ)
    (hA : IsRLM (fun w z => hingeLoss w (feature z) (feature z)) (fun w => 1 / 20 * ‖w‖ ^ 2)
      (Metric.closedBall 0 1) A) {w : ℝ} (hw : w ∈ Metric.closedBall 0 1) :
    ∫ S, trueRisk (fun w z => hingeLoss w (feature z) (feature z)) D (A S)
      ∂(Measure.pi fun _ : Fin 800 => D) ≤
      trueRisk (fun w z => hingeLoss w (feature z) (feature z)) D w + 1 / 10 := by
  have hr : (1 / 20 : ℝ) = √(2 * (1 : NNReal) ^ 2 / (1 ^ 2 * (800 : ℕ))) := by
    rw [show (2 * ((1 : NNReal) : ℝ) ^ 2 / (1 ^ 2 * ((800 : ℕ) : ℝ))) = (1 / 20) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h := hA.integral_trueRisk_le_add_sqrt (convex_closedBall 0 1)
    (fun z => (convexOn_hingeLoss _ _).subset (Set.subset_univ _) (convex_closedBall 0 1))
    (fun z => (lipschitzWith_hingeLoss_feature z).lipschitzOnWith) (B := 1) (by norm_num)
    one_pos hr D (by norm_num) Integrable.of_finite (fun _ => Integrable.of_finite) hw
    (by simpa using hw) Integrable.of_finite
  have h8 : √(8 / ((800 : ℕ) : ℝ)) = 1 / 10 := by
    rw [show (8 / ((800 : ℕ) : ℝ)) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h8] at h
  simpa using h

/-- The unit ball admits Tikhonov RLM rules, so the bound above is not vacuous. -/
example : ∃ A : (Fin 800 → Bool) → ℝ,
    IsRLM (fun w z => hingeLoss w (feature z) (feature z)) (fun w => 1 / 20 * ‖w‖ ^ 2)
      (Metric.closedBall 0 1) A :=
  exists_isRLM (isCompact_closedBall 0 1) ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    (fun z => (continuous_hingeLoss _ _).continuousOn) (by fun_prop) 800

end CslibFrontierTests.RegularizedLossMinimization
