/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Exponentiating sublinear bounds

If `e(n) = o(n)`, then every constant multiple of the ceiling of `C * 2 ^ e(n)` is eventually
at most `2 ^ (ε * n)` for every positive real `ε`. The estimate accounts for natural-number
rounding and is useful when converting asymptotic circuit or formula bounds into integer sizes.

## Main results

* `Asymptotics.IsLittleO.eventually_mul_natCeil_two_rpow_le`: absorb fixed factors and rounding
  into any positive exponential rate.
-/

public section

open Filter

namespace Asymptotics.IsLittleO

/-- If an exponent is little-o of the input, fixed factors and natural ceiling rounding can be
absorbed into every positive exponential rate. The exponent itself need not be nonnegative. -/
theorem eventually_mul_natCeil_two_rpow_le {e : ℕ → ℝ}
    (he : e =o[atTop] (fun n => (n : ℝ))) (C : ℝ) (hC : 0 ≤ C) (a : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((a * ⌈C * (2 : ℝ) ^ e n⌉₊ : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (ε * (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) ^ (ε / 2 * (n : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      ((tendsto_const_mul_atTop_of_pos (half_pos hε)).mpr tendsto_natCast_atTop_atTop)
  filter_upwards [he.bound (half_pos hε), ht.eventually_ge_atTop ((a : ℝ) * (C + 1))]
    with n hn ha
  have he' : e n ≤ ε / 2 * (n : ℝ) := by
    apply (le_abs_self (e n)).trans
    simpa only [Real.norm_eq_abs, Nat.abs_cast] using hn
  have hpow : (2 : ℝ) ^ e n ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he'
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc
    ((a * ⌈C * (2 : ℝ) ^ e n⌉₊ : ℕ) : ℝ)
        ≤ (a : ℝ) * (C * (2 : ℝ) ^ e n + 1) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (by positivity)).le
            (Nat.cast_nonneg a)
    _ ≤ (a : ℝ) * ((C + 1) * (2 : ℝ) ^ (ε / 2 * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg a)
        nlinarith [mul_le_mul_of_nonneg_left hpow hC]
    _ = ((a : ℝ) * (C + 1)) * (2 : ℝ) ^ (ε / 2 * (n : ℝ)) := by ring
    _ ≤ (2 : ℝ) ^ (ε / 2 * (n : ℝ)) * (2 : ℝ) ^ (ε / 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (ε * (n : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring

end Asymptotics.IsLittleO
