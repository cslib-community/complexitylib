/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log

/-!
# Powers at binary logarithms versus real powers

For `a ≥ 1`, the integer powers `a ^ ⌈log₂ n⌉` and `a ^ ⌊log₂ n⌋` are within a factor `a` of the
real power `n ^ log₂ a`: `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0`
(`Nat.pow_clog_two_le_mul_rpow_logb`) and `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋`
(`Nat.rpow_logb_le_mul_pow_log_two`). They convert the solutions of halving recurrences, such as
`Nat.add_mul_two_pow_clog_le_of_halving`, into bounds of the form `O(n ^ log₂ a)` and
`Ω(n ^ log₂ a)`.

## Main results

* `Nat.pow_clog_two_le_mul_rpow_logb`: `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0`.
* `Nat.rpow_logb_le_mul_pow_log_two`: `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋`, including `n = 0`.
-/

public section

namespace Nat

private theorem two_pow_rpow_logb {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ Real.logb 2 a = (a : ℝ) ^ j := by
  rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast ha),
    Real.rpow_natCast]

private theorem logb_two_nonneg {a : ℕ} (ha : 1 ≤ a) : 0 ≤ Real.logb 2 (a : ℝ) :=
  Real.logb_nonneg one_lt_two (by exact_mod_cast ha)

/-- `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0` and `a ≥ 1`. -/
theorem pow_clog_two_le_mul_rpow_logb {a n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) :
    ((a ^ Nat.clog 2 n : ℕ) : ℝ) ≤ a * (n : ℝ) ^ Real.logb 2 a := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [Nat.clog_one_right, pow_zero, Nat.cast_one, Real.one_rpow, mul_one]
    exact_mod_cast ha
  · set k := Nat.clog 2 n with hk
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.clog_pos one_lt_two h)
    have hlt : 2 ^ (k - 1) < n := by
      have := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < n)
      simpa [Nat.pred_eq_sub_one] using this
    have hmono : ((2 : ℝ) ^ (k - 1)) ^ Real.logb 2 a ≤ (n : ℝ) ^ Real.logb 2 a :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (logb_two_nonneg ha)
    have hsplit : k = (k - 1) + 1 := by omega
    calc ((a ^ k : ℕ) : ℝ) = (a : ℝ) * (a : ℝ) ^ (k - 1) := by
          rw [Nat.cast_pow, hsplit, pow_succ, Nat.add_sub_cancel, mul_comm]
      _ ≤ a * (n : ℝ) ^ Real.logb 2 a := by
          rw [← two_pow_rpow_logb ha]; gcongr

/-- `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋` for `a ≥ 1`, including `n = 0`. -/
theorem rpow_logb_le_mul_pow_log_two {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    (n : ℝ) ^ Real.logb 2 a ≤ a * (a : ℝ) ^ Nat.log 2 n := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, pow_zero, mul_one, Nat.cast_zero]
    exact (Real.zero_rpow_le_one _).trans ha'
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    calc (n : ℝ) ^ Real.logb 2 a ≤ ((2 : ℝ) ^ (Nat.log 2 n + 1)) ^ Real.logb 2 a :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (logb_two_nonneg ha)
      _ = a * (a : ℝ) ^ Nat.log 2 n := by rw [two_pow_rpow_logb ha, pow_succ, mul_comm]

end Nat
