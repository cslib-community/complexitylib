/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Quadratic bounds for `exp` and `log` near zero

Two second-order estimates used in the analysis of multiplicative weights [AroraHazanKale2012]:

* `Real.neg_sub_sq_le_log_one_sub`: `-y - y ^ 2 ≤ log (1 - y)` for `y ≤ 1 / 2`. For `0 ≤ y ≤ 1 / 2`
  this is the bound `-ln (1 - η) ≤ η + η ^ 2` of [AroraHazanKale2012, §1.1, proof of Theorem 1.1];
  for negative `y` it is the bound `ln (1 + η) ≥ η - η ^ 2` used in the proof of Theorem 2.1.
* `Real.exp_neg_le_one_sub_add_sq`: `exp (-y) ≤ 1 - y + y ^ 2` for `-1 ≤ y`, the estimate behind
  the Hedge bound [AroraHazanKale2012, §2.1, Theorem 2.3].

## Main results

* `Real.neg_sub_sq_le_log_one_sub`: `-y - y ^ 2 ≤ log (1 - y)` for `y ≤ 1 / 2`.
* `Real.exp_neg_le_one_sub_add_sq`: `exp (-y) ≤ 1 - y + y ^ 2` for `-1 ≤ y`.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
-/

public section

namespace Real

/-- `(1 - y) exp (y + y ^ 2) ≥ 1` for `y ≤ 1 / 2`: for `y ≥ 0` from `exp x ≥ 1 + x + x ^ 2 / 2`,
for `y < 0` from `exp x ≥ 1 + x`. -/
private theorem one_le_one_sub_mul_exp_add_sq {y : ℝ} (hy : y ≤ 1 / 2) :
    1 ≤ (1 - y) * exp (y + y ^ 2) := by
  have h1 : 0 ≤ 1 - y := by linarith
  rcases le_or_gt 0 y with h0 | h0
  · have hq := quadratic_le_exp_of_nonneg (add_nonneg h0 (sq_nonneg y))
    have hpoly : 1 ≤ (1 - y) * (1 + (y + y ^ 2) + (y + y ^ 2) ^ 2 / 2) := by
      have hy2 : y ^ 2 ≤ y / 2 := by nlinarith
      have hy3 : y ^ 3 ≤ y ^ 2 / 2 := by nlinarith
      nlinarith [sq_nonneg y, mul_nonneg (sq_nonneg y) h0, pow_nonneg h0 4, pow_nonneg h0 5]
    exact hpoly.trans (mul_le_mul_of_nonneg_left hq h1)
  · calc (1 : ℝ) ≤ (1 - y) * (y + y ^ 2 + 1) := by nlinarith [pow_two_nonneg y]
      _ ≤ (1 - y) * exp (y + y ^ 2) := mul_le_mul_of_nonneg_left (add_one_le_exp _) h1

/-- `-y - y ^ 2 ≤ log (1 - y)` for `y ≤ 1 / 2`. With `y = η ∈ [0, 1 / 2]` this is
`-ln (1 - η) ≤ η + η ^ 2` [AroraHazanKale2012, §1.1]. -/
theorem neg_sub_sq_le_log_one_sub {y : ℝ} (hy : y ≤ 1 / 2) : -y - y ^ 2 ≤ log (1 - y) := by
  have h1 : 0 < 1 - y := by linarith
  rw [le_log_iff_exp_le h1]
  have h := one_le_one_sub_mul_exp_add_sq hy
  have hinv : exp (-y - y ^ 2) = (exp (y + y ^ 2))⁻¹ := by
    rw [← exp_neg, neg_add']
  rw [hinv, inv_le_iff_one_le_mul₀ (exp_pos _)]
  linarith [mul_comm (1 - y) (exp (y + y ^ 2))]

/-- `exp (-y) ≤ 1 - y + y ^ 2` for `-1 ≤ y`: for `|y| ≤ 1` from the second-order bound
`Real.abs_exp_sub_one_sub_id_le`, and for `y > 1` because `exp (-y) ≤ 1 ≤ 1 - y + y ^ 2`. -/
theorem exp_neg_le_one_sub_add_sq {y : ℝ} (hy : -1 ≤ y) : exp (-y) ≤ 1 - y + y ^ 2 := by
  rcases le_or_gt y 1 with h1 | h1
  · have habs : |-y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h := (abs_le.mp (abs_exp_sub_one_sub_id_le habs)).2
    rw [neg_sq] at h
    linarith
  · have : exp (-y) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith

end Real
