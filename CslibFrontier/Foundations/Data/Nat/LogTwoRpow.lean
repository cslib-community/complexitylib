/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log

/-!
# Powers at logarithms versus real powers

For `b ≥ 2` and `a ≥ 1`, the integer powers `a ^ ⌈log_b n⌉` and `a ^ ⌊log_b n⌋` are within a
factor `a` of the real power `n ^ log_b a`:

* `a ^ ⌈log_b n⌉ ≤ a n ^ log_b a` for `n ≠ 0` (`Nat.pow_clog_le_mul_rpow_logb`);
* `n ^ log_b a ≤ a a ^ ⌊log_b n⌋` (`Nat.rpow_logb_le_mul_pow_log`).

The base-`2` cases are `Nat.pow_clog_two_le_mul_rpow_logb` and
`Nat.rpow_logb_le_mul_pow_log_two`. They turn the solutions of halving recurrences, such as
`Nat.add_mul_two_pow_clog_le_of_halving`, into `O(n ^ log₂ a)` and `Ω(n ^ log₂ a)` bounds. The
master theorem (`CslibFrontier.Foundations.Data.Nat.MasterTheoremAsymptotics`) uses the general
base,
together with `⌈log_b n⌉ ≤ 2 log_b n` for `n ≥ b` (`Nat.clog_le_two_mul_logb`).

## Main results

* `Nat.pow_clog_le_mul_rpow_logb`: `a ^ ⌈log_b n⌉ ≤ a n ^ log_b a` for `n ≠ 0`.
* `Nat.rpow_logb_le_mul_pow_log`: `n ^ log_b a ≤ a a ^ ⌊log_b n⌋`, including `n = 0`.
* `Nat.pow_clog_two_le_mul_rpow_logb`, `Nat.rpow_logb_le_mul_pow_log_two`: the base-`2` cases.
* `Nat.clog_le_two_mul_logb`: `⌈log_b n⌉ ≤ 2 log_b n` for `n ≥ b`.
-/

public section

namespace Nat

private theorem pow_rpow_logb {a b : ℕ} (hb : 1 < b) (ha : 1 ≤ a) (j : ℕ) :
    ((b : ℝ) ^ j) ^ Real.logb b a = (a : ℝ) ^ j := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (b : ℝ) ≠ 1 := by exact_mod_cast (by omega : b ≠ 1)
  rw [← Real.rpow_natCast (b : ℝ) j, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_logb hb0 hb1 (by exact_mod_cast (by omega : 0 < a)),
    Real.rpow_natCast]

private theorem logb_nonneg_of {a b : ℕ} (hb : 1 < b) (ha : 1 ≤ a) :
    0 ≤ Real.logb b (a : ℝ) :=
  Real.logb_nonneg (by exact_mod_cast hb) (by exact_mod_cast ha)

/-- `a ^ ⌈log_b n⌉ ≤ a n ^ log_b a` for `b ≥ 2`, `a ≥ 1` and `n ≠ 0`. -/
theorem pow_clog_le_mul_rpow_logb {a b n : ℕ} (hb : 1 < b) (ha : 1 ≤ a) (hn : n ≠ 0) :
    ((a ^ clog b n : ℕ) : ℝ) ≤ a * (n : ℝ) ^ Real.logb b a := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [clog_one_right, pow_zero, Nat.cast_one, Real.one_rpow, mul_one]
    exact_mod_cast ha
  · set k := clog b n
    have hlt : b ^ (k - 1) < n := pow_pred_clog_lt_self hb (by omega)
    have hk : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos (clog_pos hb h)).symm
    calc ((a ^ k : ℕ) : ℝ) = (a : ℝ) * ((b : ℝ) ^ (k - 1)) ^ Real.logb b a := by
          rw [pow_rpow_logb hb ha, Nat.cast_pow, hk, pow_succ, Nat.add_sub_cancel, mul_comm]
      _ ≤ a * (n : ℝ) ^ Real.logb b a := by
          have := logb_nonneg_of hb ha
          gcongr
          exact_mod_cast hlt.le

/-- `n ^ log_b a ≤ a a ^ ⌊log_b n⌋` for `b ≥ 2` and `a ≥ 1`, including `n = 0`. -/
theorem rpow_logb_le_mul_pow_log {a b : ℕ} (hb : 1 < b) (ha : 1 ≤ a) (n : ℕ) :
    (n : ℝ) ^ Real.logb b a ≤ a * (a : ℝ) ^ Nat.log b n := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, pow_zero, mul_one, Nat.cast_zero]
    exact (Real.zero_rpow_le_one _).trans ha'
  · have hlt : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb n
    calc (n : ℝ) ^ Real.logb b a ≤ ((b : ℝ) ^ (Nat.log b n + 1)) ^ Real.logb b a :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (logb_nonneg_of hb ha)
      _ = a * (a : ℝ) ^ Nat.log b n := by rw [pow_rpow_logb hb ha, pow_succ, mul_comm]

/-- `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0` and `a ≥ 1`. -/
theorem pow_clog_two_le_mul_rpow_logb {a n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) :
    ((a ^ Nat.clog 2 n : ℕ) : ℝ) ≤ a * (n : ℝ) ^ Real.logb 2 a := by
  exact_mod_cast pow_clog_le_mul_rpow_logb one_lt_two ha hn

/-- `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋` for `a ≥ 1`, including `n = 0`. -/
theorem rpow_logb_le_mul_pow_log_two {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    (n : ℝ) ^ Real.logb 2 a ≤ a * (a : ℝ) ^ Nat.log 2 n := by
  exact_mod_cast rpow_logb_le_mul_pow_log one_lt_two ha n

/-- `⌈log_b n⌉ ≤ 2 log_b n` for `b ≥ 2` and `n ≥ b`. -/
theorem clog_le_two_mul_logb {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) :
    (clog b n : ℝ) ≤ 2 * Real.logb b n := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have h1 : 1 ≤ Real.logb b n := by
    rw [← Real.logb_self_eq_one hb']
    exact Real.logb_le_logb_of_le hb' (by positivity) (by exact_mod_cast hn)
  have h2 : (clog b n : ℝ) < Real.logb b n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (by linarith)
  linarith

end Nat
