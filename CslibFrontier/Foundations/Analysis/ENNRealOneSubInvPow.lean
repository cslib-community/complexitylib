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

* `ENNReal.one_sub_inv_pow_le_inv_two`: `(1 - k⁻¹) ^ k ≤ 2⁻¹` for every positive natural `k`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- **`(1 - 1 / k) ^ k ≤ 1 / 2`** in `ℝ≥0∞` for every positive natural number `k`. -/
theorem one_sub_inv_pow_le_inv_two {k : ℕ} (hk : k ≠ 0) : (1 - (k : ℝ≥0∞)⁻¹) ^ k ≤ 2⁻¹ := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hsub : 1 - (k : ℝ≥0∞)⁻¹ = ((k - 1 : ℕ) : ℝ≥0∞) / k := by
    refine ENNReal.sub_eq_of_eq_add (ENNReal.inv_ne_top.mpr hk0) ?_
    rw [div_eq_mul_inv, ← add_one_mul, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega),
      ENNReal.mul_inv_cancel hk0 (ENNReal.natCast_ne_top k)]
  have hfrac : (((k - 1) ^ k : ℕ) : ℝ≥0∞) / ((k ^ k : ℕ) : ℝ≥0∞) ≤
      ((1 : ℕ) : ℝ≥0∞) / ((2 : ℕ) : ℝ≥0∞) :=
    (natCast_div_le_natCast_div_iff (pow_ne_zero k hk) two_ne_zero).mpr
      (by rw [mul_comm, one_mul]; exact Nat.two_mul_pred_pow_le (Nat.one_le_iff_ne_zero.mpr hk))
  calc (1 - (k : ℝ≥0∞)⁻¹) ^ k = (((k - 1) ^ k : ℕ) : ℝ≥0∞) / ((k ^ k : ℕ) : ℝ≥0∞) := by
        rw [hsub, Nat.cast_pow, Nat.cast_pow, div_eq_mul_inv, div_eq_mul_inv, mul_pow,
          ENNReal.inv_pow]
    _ ≤ ((1 : ℕ) : ℝ≥0∞) / ((2 : ℕ) : ℝ≥0∞) := hfrac
    _ = 2⁻¹ := by rw [Nat.cast_one, Nat.cast_two, one_div]

end ENNReal
