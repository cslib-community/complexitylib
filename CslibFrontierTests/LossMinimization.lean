/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.LossMinimization.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count

/-! Checks for true and empirical risk: the absolute loss `|w - z|` on a three-point sample, the
effect of replacing one example, convexity of the empirical risk, and, for the uniform distribution
on `Bool` with the loss `(w - [z])²`, the exact true risk and its unbiased estimate. -/

namespace CslibFrontierTests.LossMinimization

open Cslib.MachineLearning MeasureTheory
open scoped ENNReal

/-! ### The absolute loss on a sample -/

/-- The absolute loss of the prediction `w` on the real example `z`. -/
noncomputable def absLoss (w z : ℝ) : ℝ := |w - z|

example : empiricalRisk absLoss ![0, 1, 2] 1 = 2 / 3 := by
  rw [empiricalRisk_eq_sum_div]
  norm_num [absLoss, Fin.sum_univ_three]

/-- Replacing the example `0` by `1` lowers the empirical risk of `w = 1` by `1 / 3`. -/
example : empiricalRisk absLoss (Function.update ![0, 1, 2] 0 1) 1 = 1 / 3 := by
  rw [empiricalRisk_update]
  norm_num [empiricalRisk_eq_sum_div, absLoss, Fin.sum_univ_three]

/-- The empirical risk of the absolute loss is convex on `ℝ`. -/
example {m : ℕ} (S : Fin m → ℝ) : ConvexOn ℝ Set.univ (empiricalRisk absLoss S) :=
  convexOn_empiricalRisk convex_univ fun i => by
    simpa only [absLoss, Real.dist_eq] using convexOn_univ_dist (S i)

/-- The empirical risk of the absolute loss is continuous. -/
example {m : ℕ} (S : Fin m → ℝ) : ContinuousOn (empiricalRisk absLoss S) Set.univ :=
  continuousOn_empiricalRisk fun _ =>
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn

/-! ### The uniform distribution on `Bool` -/

/-- The uniform distribution on `Bool`. -/
noncomputable def uniformBool : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniformBool :=
  ⟨by
    rw [uniformBool, Measure.smul_apply, Measure.count_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_bool, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The squared loss of the prediction `w` against the label `1` on `true` and `0` on `false`. -/
noncomputable def bitLoss (w : ℝ) (z : Bool) : ℝ := (w - if z then 1 else 0) ^ 2

theorem trueRisk_bitLoss (w : ℝ) : trueRisk bitLoss uniformBool w = (w ^ 2 + (w - 1) ^ 2) / 2 := by
  rw [trueRisk_def, integral_fintype Integrable.of_finite]
  simp only [uniformBool, measureReal_def, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, Fintype.sum_bool, bitLoss, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num
  ring

/-- On `5` uniform bits, the expected empirical risk of `w = 1 / 2` is `1 / 4`. -/
example : ∫ S, empiricalRisk bitLoss S (1 / 2) ∂(Measure.pi fun _ : Fin 5 => uniformBool) =
    1 / 4 := by
  rw [integral_empiricalRisk bitLoss uniformBool (by norm_num) _ Integrable.of_finite,
    trueRisk_bitLoss]
  norm_num

end CslibFrontierTests.LossMinimization
