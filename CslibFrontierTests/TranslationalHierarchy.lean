/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Translational

/-! Values of the iterated square root of the logarithm, and instances of the translational
hierarchy: `DTIME(n) ⊊ DTIME(n (log₂ n + 1))`, and the real-exponent form at `ε = 1`. -/

namespace CslibFrontierTests.TranslationalHierarchy

open Cslib.Complexity Turing.MultiTapeTM Filter

/-- `⌊log₂ 1024⌋ + 1 = 11`, then `⌊√11⌋ + 1 = 4`, then `⌊√4⌋ + 1 = 3`. -/
example : iterSqrtLog 0 1024 = 11 ∧ iterSqrtLog 1 1024 = 4 ∧ iterSqrtLog 2 1024 = 3 := by
  have h0 : iterSqrtLog 0 1024 = 11 := by
    rw [iterSqrtLog_zero, show 1024 = 2 ^ 10 by norm_num, Nat.log_pow (by norm_num)]
  have h1 : iterSqrtLog 1 1024 = 4 := by
    rw [iterSqrtLog_succ, h0, ← Nat.eq_sqrt.2 (show 3 * 3 ≤ 11 ∧ 11 < 4 * 4 by norm_num)]
  refine ⟨h0, h1, ?_⟩
  rw [iterSqrtLog_succ, h1, ← Nat.eq_sqrt.2 (show 2 * 2 ≤ 4 ∧ 4 < 3 * 3 by norm_num)]

/-- At `p = 0` the gap is `log₂ n + 1`: linear time is strictly inside time `n (log₂ n + 1)`. -/
example : DTIME encBits (fun n => n ^ 1) ⊂ DTIME encBits (fun n => n * (Nat.log 2 n + 1)) := by
  simpa [iterSqrtLog_zero] using DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow le_rfl 0

/-- The real-exponent form at `a = 2`, `ε = 1`: `ln n ≤ log₂ n + 1` gives
`DTIME(n²) ⊊ DTIME(n² (log₂ n + 1))`. -/
example : DTIME encBits (fun n => n ^ 2) ⊂ DTIME encBits (fun n => n ^ 2 * (Nat.log 2 n + 1)) :=
  DTIME_pow_ssubset_DTIME_of_log_rpow (by norm_num) one_pos <| by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.rpow_one]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
    have hlog := Real.log_lt_log hpos hlt
    rw [Real.log_pow] at hlog
    have h2 : Real.log 2 < 1 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
      linarith
    have h0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
    push_cast at hlog
    nlinarith

end CslibFrontierTests.TranslationalHierarchy
