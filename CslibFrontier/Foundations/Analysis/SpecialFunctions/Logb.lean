/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (the `Real` lemmas to Mathlib, `Mathlib/Analysis/SpecialFunctions/Log/Base`;
-- `Cslib.BitString.logb_card` to cslib, beside `Cslib/Foundations/Data/BitString.lean`)

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogTwoPow

/-!
# Logarithms of powers of the base

Mathlib's `Real.logb_rpow` computes `logb b (b ^ x) = x` for a real exponent. Counting,
entropy and amplification arguments meet the natural-number power `b ^ k` instead, usually
with `b = 2`. This file states that case once, together with a base-two logarithmic gap bound
and a real-power bound used by the same calculations.

## Main results

* `Real.logb_self_pow`: `logb b (b ^ k) = k` for a natural-number exponent, with base-two case
  `Real.logb_two_pow`. `Cslib.BitString.logb_card` reads it as `n` bits in a string of `n`
  bits.
* `Real.two_rpow_le_half_pow`: `2 ^ x ≤ (1 / 2) ^ n` for real `x ≤ -n`, the real-power twin of
  `Real.exp_le_half_pow` in `SpecialFunctions/ExpBounds`. It lives here because it needs real
  powers, which `Log/Base` already imports and `ExpBounds` does not.
* `Real.sub_div_le_logb_sub`: `(b - a) / b ≤ log₂ b - log₂ a` for `0 < a ≤ b`. Since
  `log₂ (b / a) = -log₂ (1 - (b - a) / b)` and `log 2 ≤ 1`, this is the base-two form of
  `-log (1 - t) ≥ t`.

`Real.logb_self_pow` is not `@[simp]`: existing `simp` calls in clients would change normal form.
-/

public section

namespace Real

/-- `logb b (b ^ k) = k` for a natural-number exponent; the `ℕ`-power form of
`Real.logb_rpow`. -/
theorem logb_self_pow {b : ℝ} (b_pos : 0 < b) (b_ne_one : b ≠ 1) (k : ℕ) :
    logb b (b ^ k) = k := by
  rw [← rpow_natCast, logb_rpow b_pos b_ne_one]

/-- `log₂ (2 ^ k) = k`. -/
theorem logb_two_pow (k : ℕ) : logb 2 ((2 : ℝ) ^ k) = k :=
  logb_self_pow two_pos one_lt_two.ne' k

/-- `2 ^ x ≤ (1 / 2) ^ n` whenever the real exponent satisfies `x ≤ -n`. -/
theorem two_rpow_le_half_pow (n : ℕ) {x : ℝ} (hx : x ≤ -(n : ℝ)) :
    (2 : ℝ) ^ x ≤ (1 / 2 : ℝ) ^ n :=
  calc (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (-(n : ℝ)) := rpow_le_rpow_of_exponent_le (by norm_num) hx
    _ = ((2 : ℝ) ^ (n : ℝ))⁻¹ := rpow_neg (by norm_num) (n : ℝ)
    _ = (1 / 2 : ℝ) ^ n := by rw [rpow_natCast, one_div, inv_pow]

/-- The relative gap `(b - a) / b` is at most the base-two logarithmic gap `log₂ b - log₂ a` for
`0 < a ≤ b`. -/
theorem sub_div_le_logb_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ logb 2 b - logb 2 a := by
  have hb : 0 < b := ha.trans_le hab
  have hlog : (b - a) / b ≤ log b - log a := by
    have h := log_le_sub_one_of_pos (div_pos ha hb)
    rw [log_div ha.ne' hb.ne'] at h
    rw [sub_div, div_self hb.ne']
    linarith
  have ht : 0 ≤ (b - a) / b := div_nonneg (sub_nonneg.mpr hab) hb.le
  rw [logb, logb, ← sub_div, le_div_iff₀ (log_pos one_lt_two)]
  linarith [mul_le_mul_of_nonneg_left log_two_lt_one.le ht]

end Real

/-- A string of `n` bits carries `n` bits: `log₂ |BitString n| = n`. -/
theorem Cslib.BitString.logb_card (n : ℕ) :
    Real.logb 2 (Fintype.card (Cslib.BitString n)) = n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_two_pow]
