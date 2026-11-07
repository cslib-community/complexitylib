/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Nat.SqrtLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The scale `n / √⌊log₂ n⌋` of the counting simulations: concrete values, the agreement of the
natural scale with the real scale `n / √(log₂ n)` up to constant factors, which makes
`2 ^ O(n / √⌊log₂ n⌋)` the usual `2 ^ O(n / √(log n))`, and the exponent arithmetic on an
instance. -/

namespace ComplexityTests.SqrtLog

open Nat

/-! ### Concrete values -/

-- `⌊log₂ 16⌋ = 4`, so the divisor is `2` and the scale is `8`.
example : 16 / sqrt (log 2 16) = 8 := by
  have h1 : log 2 16 = 4 := by rw [show (16 : ℕ) = 2 ^ 4 by rfl, log_pow one_lt_two]
  have h2 : sqrt 4 = 2 := (eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  rw [h1, h2]

-- The divisor is `1` at `n = 2` and `n = 15`, and `0` at `n = 1`.
example : sqrt (log 2 15) = 1 ∧ sqrt (log 2 2) = 1 ∧ sqrt (log 2 1) = 0 := by
  have h15 : log 2 15 = 3 := by rw [log_eq_iff (by norm_num)]; norm_num
  have h2 : log 2 2 = 1 := by rw [log_eq_iff (by norm_num)]; norm_num
  refine ⟨?_, ?_, by simp⟩
  · rw [h15]
    exact (eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  · rw [h2]
    exact (eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

-- The scale is not monotone: it drops from `15` at `n = 15` to `8` at `n = 16`, where the divisor
-- jumps. It is monotone up to the constants of `div_sqrt_log_two_le_of_le`.
example : 16 / sqrt (log 2 16) < 15 / sqrt (log 2 15) ∧
    15 / sqrt (log 2 15) ≤ 2 * (16 / sqrt (log 2 16)) + 2 := by
  have h16 : log 2 16 = 4 := by rw [show (16 : ℕ) = 2 ^ 4 by rfl, log_pow one_lt_two]
  have h15 : log 2 15 = 3 := by rw [log_eq_iff (by norm_num)]; norm_num
  have h4 : sqrt 4 = 2 := (eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have h3 : sqrt 3 = 1 := (eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  rw [h16, h15, h4, h3]
  decide

-- `20` steps in blocks of length `⌈log₂ 22⌉` need at most `20 / 2 + 1 = 11` blocks.
example : 20 ⌈/⌉ clog 2 (20 + 2) ≤ 20 / sqrt (log 2 20) + 1 := ceilDiv_clog_two_le 20

/-! ### The natural scale is the real scale up to constants -/

/-- The natural scale is at least the real scale, up to one. -/
theorem div_sqrt_logb_le (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / √(Real.logb 2 n) ≤ ((n / sqrt (log 2 n) : ℕ) : ℝ) + 1 := by
  have hr := one_le_sqrt_log_two hn
  have hlogb : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ n))
  -- `√⌊log₂ n⌋ ≤ √(log₂ n)`
  have hle : (sqrt (log 2 n) : ℝ) ≤ √(Real.logb 2 n) := by
    rw [Real.le_sqrt (by positivity) hlogb]
    have h1 : ((sqrt (log 2 n) * sqrt (log 2 n) : ℕ) : ℝ) ≤ (log 2 n : ℕ) := by
      exact_mod_cast sqrt_le _
    have h2 := Real.natLog_le_logb n 2
    push_cast at h1 h2
    nlinarith
  have hdiv : (n : ℝ) / √(Real.logb 2 n) ≤ (n : ℝ) / sqrt (log 2 n) :=
    div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hr) hle
  refine hdiv.trans ?_
  rw [div_le_iff₀ (by exact_mod_cast hr)]
  have : (n : ℝ) ≤ ((n / sqrt (log 2 n) : ℕ) : ℝ) * sqrt (log 2 n) + sqrt (log 2 n) := by
    exact_mod_cast (lt_div_mul_add (a := n) hr).le
  nlinarith

/-- The natural scale is at most three times the real scale. -/
theorem div_sqrt_log_two_le (n : ℕ) (hn : 2 ≤ n) :
    ((n / sqrt (log 2 n) : ℕ) : ℝ) ≤ 3 * ((n : ℝ) / √(Real.logb 2 n)) := by
  set L := log 2 n
  set r := sqrt L
  have hr : 1 ≤ r := one_le_sqrt_log_two hn
  -- `log₂ n < L + 1 < (r + 1) ^ 2 + 1 ≤ 9 r ^ 2`
  have hlogb : Real.logb 2 n < L + 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
    have h : (n : ℝ) < (2 : ℝ) ^ (L + 1) := by
      exact_mod_cast lt_pow_succ_log_self one_lt_two n
    rw [← Real.rpow_natCast] at h
    exact_mod_cast h
  have hLr : L < (r + 1) * (r + 1) := lt_succ_sqrt L
  have hpos : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by exact_mod_cast hn)
  have hsq : √(Real.logb 2 n) ≤ 3 * r := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (L : ℝ) + 1 ≤ 9 * (r : ℝ) ^ 2 := by
      have h1 : (L : ℝ) < ((r : ℝ) + 1) * ((r : ℝ) + 1) := by exact_mod_cast hLr
      have h2 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    nlinarith
  calc ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / r := Nat.cast_div_le
    _ ≤ 3 * ((n : ℝ) / √(Real.logb 2 n)) := by
      rw [mul_div_assoc', le_div_iff₀ (Real.sqrt_pos.2 hpos), div_mul_eq_mul_div,
        div_le_iff₀ (by exact_mod_cast hr)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### Exponent arithmetic -/

-- Two heads, a clock `3 T`, a cubic polynomial and a contraction exponent `5`: one constant
-- bounds the cost for every `T ≥ 2`, and also absorbs a factor `7` and an addend `11`.
example : ∃ C, ∀ T, 2 ≤ T →
    7 * (3 ^ (2 * (3 * T ⌈/⌉ clog 2 (3 * T + 2))) * (3 * T + 1) ^ 3 *
        2 ^ (5 * (3 * T) / sqrt (log 2 (3 * T)))) + 11 ≤
      2 ^ (C * T / sqrt (log 2 T)) := by
  obtain ⟨C, hC⟩ := exists_three_pow_mul_le_two_pow_div_sqrt_log_two 2 3 3 5
  exact ⟨(7 + 11 + 1) * (C + 1), fun T hT =>
    (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (hC T hT)) 11).trans
      (mul_two_pow_div_sqrt_log_two_add_le hT)⟩

-- The space bound: `5 (T + 1) ^ 4 + 9 ≤ T ^ 22` from `T = 2` on.
example (T : ℕ) (hT : 2 ≤ T) : 5 * (T + 1) ^ 4 + 9 ≤ T ^ 22 :=
  mul_add_one_pow_add_le_pow hT

end ComplexityTests.SqrtLog
