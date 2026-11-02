/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.ENNReal.Inv

/-!
# Dyadic fractions in `ℝ≥0∞`

A count `c` out of `2 ^ n` equally likely strings is a probability `c / 2 ^ n`. Bounded-error
acceptance thresholds compare it with `2 / 3`; this file turns that comparison into one between
natural numbers.

## Main results

* `ENNReal.two_div_three_le_natCast_div_two_pow_iff`: `2 / 3 ≤ c / 2 ^ n ↔ 2 * 2 ^ n ≤ 3 * c`.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- A dyadic fraction `c / 2 ^ n` is at least two thirds exactly when `2 * 2 ^ n ≤ 3 * c`. -/
theorem two_div_three_le_natCast_div_two_pow_iff {c n : ℕ} :
    (2 / 3 : ℝ≥0∞) ≤ c / 2 ^ n ↔ 2 * 2 ^ n ≤ 3 * c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)]
  constructor
  · intro h
    have : ((2 * 2 ^ n : ℕ) : ℝ≥0∞) ≤ ((3 * c : ℕ) : ℝ≥0∞) := by
      push_cast
      rw [mul_comm (3 : ℝ≥0∞)]
      exact h
    exact_mod_cast this
  · intro h
    have : ((2 * 2 ^ n : ℕ) : ℝ≥0∞) ≤ ((3 * c : ℕ) : ℝ≥0∞) := by exact_mod_cast h
    push_cast at this
    rw [mul_comm (c : ℝ≥0∞)]
    exact this

end ENNReal
