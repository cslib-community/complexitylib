/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.LossMinimization.StochasticGradientDescent

/-! Checks for stochastic gradient descent and the convex online-to-batch conversion on the
absolute loss `|w - z|` on `ℝ` (median estimation): the subgradient and Lipschitz hypotheses, a
concrete iterate, and the bound `𝔼 L_D(w̄) ≤ L_D(u) + 1 / 2` for four unconstrained steps from `0`
with step size `1 / 2`, for every distribution `D` with a first moment and every `|u| ≤ 1`. -/

namespace CslibFrontierTests.StochasticGradientDescent

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.OCO MeasureTheory
open scoped RealInnerProductSpace

/-- The absolute loss of the prediction `w` on the example `z`. -/
noncomputable def absLoss (w z : ℝ) : ℝ := |w - z|

/-- A subgradient of `absLoss · z` at `w`: `-1` for `w ≤ z` and `1` otherwise. -/
noncomputable def absGrad (w z : ℝ) : ℝ := if w ≤ z then -1 else 1

theorem absLoss_add_inner_le (z w y : ℝ) : absLoss w z + ⟪absGrad w z, y - w⟫ ≤ absLoss y z := by
  rw [Real.inner_apply]
  unfold absLoss absGrad
  split_ifs with h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [neg_abs_le (y - z)]
  · rw [abs_of_pos (sub_pos.mpr (not_le.mp h))]
    linarith [le_abs_self (y - z)]

theorem norm_absGrad_le (w z : ℝ) : ‖absGrad w z‖ ≤ 1 := by
  unfold absGrad
  split_ifs <;> simp

theorem measurable_absLoss : Measurable (Function.uncurry absLoss) :=
  show Measurable fun p : ℝ × ℝ => |p.1 - p.2| from
    (continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable

theorem measurable_absGrad : Measurable (Function.uncurry absGrad) :=
  show Measurable fun p : ℝ × ℝ => if p.1 ≤ p.2 then (-1 : ℝ) else 1 from
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const

/-- SGD follows the sample: from `0`, after the example `1` the iterate moves to `1 / 2`. -/
example : sgd id (fun _ => (1 : ℝ) / 2) absGrad 0 ![(1 : ℝ), -1] 1 = 1 / 2 := by
  rw [sgd_def, ogd_succ, ogd_zero]
  norm_num [absGrad]

/-- Four unconstrained steps of SGD from `0` with step size `1 / 2` on the absolute loss: for every
distribution `D` with a first moment and every comparator `|u| ≤ 1`, the average iterate has
expected true risk at most `L_D(u) + 1 / 2`. -/
example (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable id D) {u : ℝ} (hu : |u| ≤ 1) :
    ∫ S : Fin 4 → ℝ, trueRisk absLoss D
        ((4 : ℝ)⁻¹ • ∑ t : Fin 4, sgd id (fun _ => 1 / 2) absGrad 0 S t) ∂Measure.pi (fun _ => D) ≤
      trueRisk absLoss D u + 1 / 2 := by
  have hint : Integrable (absLoss 0) D := by
    have e : absLoss 0 = fun z => |id z| := funext fun z => by simp [absLoss]
    rw [e]
    exact hD.abs
  have h := integral_trueRisk_sgd_average_le (T := 4) (by norm_num) convex_univ
    isPythagoreanProjection_id measurable_id measurable_absLoss measurable_absGrad
    (fun z x _ y _ => absLoss_add_inner_le z x y) one_pos (fun z x _ => norm_absGrad_le x z)
    (Set.mem_univ 0) hint (Set.mem_univ u) one_pos (by simpa using hu)
  have hs : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simpa only [Nat.cast_ofNat, hs, one_mul, mul_one] using h

end CslibFrontierTests.StochasticGradientDescent
