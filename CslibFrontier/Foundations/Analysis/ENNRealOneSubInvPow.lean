/-
Copyright (c) 2026 Renfei Zhou, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.ENNReal.Inv
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Foundations.Data.Nat.Choose

/-!
# `(1 - 1 / k) ^ k ≤ 1 / 2` in `ℝ≥0∞`

Repeating a trial that succeeds with probability at least `1 / k` for `k` times fails with
probability at most `(1 - 1 / k) ^ k`, which is at most `e⁻¹`, hence at most `1 / 2`. This file
proves the bound `(1 - 1 / k) ^ k ≤ 1 / 2` in `ℝ≥0∞` without real analysis: after clearing
denominators it is `2 (k - 1) ^ k ≤ k ^ k` (`Nat.two_mul_pred_pow_le`), an instance of Bernoulli's
inequality.

## Main results

* `ENNReal.natCast_pred_div_pow_le_half`: `((k - 1) / k) ^ k ≤ 1 / 2` for every positive
  natural `k`.
* `ENNReal.one_sub_inv_pow_le_inv_two`: `(1 - k⁻¹) ^ k ≤ 2⁻¹` for every positive natural `k`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- **`((k - 1) / k) ^ k ≤ 1 / 2`** in `ℝ≥0∞` for every positive natural number `k`: the fraction
form of `one_sub_inv_pow_le_inv_two`. -/
theorem natCast_pred_div_pow_le_half {k : ℕ} (hk : k ≠ 0) :
    (((k - 1 : ℕ) : ℝ≥0∞) / k) ^ k ≤ 1 / 2 := by
  have h := (natCast_div_le_natCast_div_iff (a := (k - 1) ^ k) (c := 1) (pow_ne_zero k hk)
    two_ne_zero).mpr
      (by rw [mul_comm, one_mul]; exact Nat.two_mul_pred_pow_le (Nat.one_le_iff_ne_zero.mpr hk))
  rwa [Nat.cast_pow, Nat.cast_pow, Nat.cast_one, Nat.cast_two, ← ENNReal.div_pow] at h

/-- **`(1 - 1 / k) ^ k ≤ 1 / 2`** in `ℝ≥0∞` for every positive natural number `k`. -/
theorem one_sub_inv_pow_le_inv_two {k : ℕ} (hk : k ≠ 0) : (1 - (k : ℝ≥0∞)⁻¹) ^ k ≤ 2⁻¹ := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hsub : 1 - (k : ℝ≥0∞)⁻¹ = ((k - 1 : ℕ) : ℝ≥0∞) / k := by
    refine ENNReal.sub_eq_of_eq_add (ENNReal.inv_ne_top.mpr hk0) ?_
    rw [div_eq_mul_inv, ← add_one_mul, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega),
      ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k)]
  rw [hsub, ← one_div]
  exact natCast_pred_div_pow_le_half hk

end ENNReal
