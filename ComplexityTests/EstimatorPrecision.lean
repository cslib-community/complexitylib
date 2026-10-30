/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.EstimatorPrecision
import Mathlib.Tactic.NormNum

/-!
# Tests for the estimator's precision payment

The examples evaluate actual parent and child precisions at dyadic rates, exercise both signs of
the scale offset, and apply the child compensation theorem with a strict source-rate increase.
The correction-child example uses a rate smaller than the bin by a factor of four, so the fixed
rate-comparison constant is necessary. The zero-budget and second-moment boundary cases are
checked separately.
-/

namespace ComplexityTests.EstimatorPrecision

open Cslib.LogSpaceEstimation

private theorem logb_dyadic_div (x y : ℝ) :
    Real.logb 2 ((2 : ℝ) ^ x / (2 : ℝ) ^ y) = x - y := by
  rw [Real.logb_div (Real.rpow_pos_of_pos (by norm_num) x).ne'
    (Real.rpow_pos_of_pos (by norm_num) y).ne',
    Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_rpow (by norm_num) (by norm_num)]

-- The parent has budget 80, rank 5, endpoint rate 1/16 and source rate 1/4.
example : precision 8 1 80 5 ((2 : ℝ) ^ (-4 : ℝ)) ((2 : ℝ) ^ (-2 : ℝ)) = 2 := by
  rw [precision_dyadic_rates]
  norm_num

-- The child loses eight budget units, drops one rank, and broadens both rates.
example : precision 8 1 72 4 ((2 : ℝ) ^ (-2 : ℝ)) ((2 : ℝ) ^ (-1 : ℝ)) = 7 / 2 := by
  rw [precision_dyadic_rates]
  norm_num

-- The zero-budget task is inactive even when the rank is zero and both rates are one.
example : precision 8 1 0 0 1 1 ≤ 0 :=
  precision_zero_nonpos (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl 0

-- An actual positive rank makes the same inactive precision strictly negative.
example : precision 8 1 0 3 1 1 = -3 := by norm_num [precision]

-- Coarse scales: raw norm cost 2, accuracy factor 1/4, geometric margin 1/2.
example : binNormCost 4 4 * (2 : ℝ) ^ (-(4 : ℝ) / 2) = 1 / 2 := by
  rw [binNormCost_mul_accuracy (by norm_num)]
  norm_num

-- Fine scales: raw norm cost 1/8, accuracy factor 4, the same geometric margin 1/2.
example : binNormCost 4 (-4) * (2 : ℝ) ^ (-(-4 : ℝ) / 2) = 1 / 2 := by
  rw [binNormCost_mul_accuracy (by norm_num)]
  norm_num

-- The second moment has no geometric margin; the two supported routes have positive margins.
example : scaleMargin 2 = 0 ∧ scaleMargin 4 = 1 / 4 ∧ scaleMargin 8 = 3 / 8 := by
  norm_num [scaleMargin]

-- For the actual parent and child above, the theorem leaves a factor 2^(-1/2) for the bin,
-- while the broader source can only improve the bound.
example : binNormCost 4 2 * (2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-7 / 2 : ℝ) ≤
    (2 : ℝ) ^ (-5 / 2 : ℝ) := by
  have h := child_cost_mul_accuracy_le (s := 4) (K := 8) (A := 1)
    (a := (2 : ℝ) ^ (-4 : ℝ)) (a' := (2 : ℝ) ^ (-2 : ℝ))
    (u := (2 : ℝ) ^ (-2 : ℝ)) (u' := (2 : ℝ) ^ (-1 : ℝ))
    (by norm_num) (by norm_num) 80 72 5 4 (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  rw [logb_dyadic_div, logb_dyadic_div, precision_dyadic_rates, precision_dyadic_rates] at h
  norm_num at h
  calc
    _ ≤ 1 / 4 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by simpa only [neg_div] using h
    _ = (2 : ℝ) ^ (-5 / 2 : ℝ) := by
      rw [show (-5 / 2 : ℝ) = -2 + -(1 / 2) by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num

-- A correction child at rate 1/16 is four times narrower than the bin rate 1/4.
-- The rate-comparison theorem supplies the necessary factor 2.
example : binNormCost 4 2 * (2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-5 / 2 : ℝ) ≤
    (2 : ℝ) ^ (-3 / 2 : ℝ) := by
  have hrate : (2 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h := child_cost_mul_accuracy_le_of_rate_le (s := 4) (K := 8) (A := 1)
    (a := (2 : ℝ) ^ (-4 : ℝ)) (a' := (2 : ℝ) ^ (-4 : ℝ))
    (b := (2 : ℝ) ^ (-2 : ℝ)) (c := (2 : ℝ) ^ (-2 : ℝ))
    (u := (2 : ℝ) ^ (-2 : ℝ)) (u' := (2 : ℝ) ^ (-1 : ℝ))
    (by norm_num) (by norm_num) 80 72 5 4 (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by norm_num) _) hrate
    (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  rw [logb_dyadic_div, logb_dyadic_div,
    Real.logb_rpow (by norm_num) (by norm_num), precision_dyadic_rates,
    precision_dyadic_rates] at h
  norm_num at h
  calc
    _ ≤ 2 * (1 / 4 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by simpa only [neg_div] using h
    _ = 1 / 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    _ = (2 : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [show (-3 / 2 : ℝ) = -1 + -(1 / 2) by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num

end ComplexityTests.EstimatorPrecision
