/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Natural logarithms below powers of two

Parameter calculations that keep their quantities as powers of two need `log x ≤ k` once
`x ≤ 2 ^ k`: the natural logarithm of `2 ^ k` is `k log 2`, and `log 2 ≤ 1`.

## Main results

* `Real.log_le_of_le_two_pow`: `log x ≤ k` for `0 < x ≤ 2 ^ k`.
-/

public section

namespace Real

/-- The natural logarithm of a positive `x ≤ 2 ^ k` is at most `k`, since `log 2 ≤ 1`. -/
theorem log_le_of_le_two_pow {x : ℝ} {k : ℕ} (hx : 0 < x) (hxk : x ≤ (2 : ℝ) ^ k) :
    log x ≤ k := by
  have hlog2 : log 2 ≤ 1 := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc log x ≤ log ((2 : ℝ) ^ k) := log_le_log hx hxk
    _ = (k : ℝ) * log 2 := log_pow 2 k
    _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k)
    _ = k := mul_one _

end Real
