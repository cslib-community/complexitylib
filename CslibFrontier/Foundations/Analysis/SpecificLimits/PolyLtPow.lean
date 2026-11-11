/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecificLimits/Normed.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A polynomial is eventually below an exponential

For `r > 1`, every fixed multiple of `(n + 1) ^ k` is eventually below `r ^ n`. This is the
eventual form of `tendsto_pow_const_div_const_pow_of_one_lt`, in the shape that bounds of the form
"a polynomial size is below an exponential budget for large `n`" consume.

## Main results

* `eventually_mul_add_one_pow_lt_pow`: `K (n + 1) ^ k < r ^ n` for all large `n`.
-/

public section

open Filter

/-- **A polynomial is eventually below an exponential**: for `r > 1`, a fixed multiple of
`(n + 1) ^ k` is eventually below `r ^ n`. -/
theorem eventually_mul_add_one_pow_lt_pow (K : ℝ) (k : ℕ) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) + 1) ^ k < r ^ n := by
  have hr0 : 0 < r := by linarith
  have hK : 0 < |K| + 1 := by positivity
  have hδ : 0 < (r * (|K| + 1))⁻¹ := inv_pos.2 (mul_pos hr0 hK)
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt k hr).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hn
  have hrn : 0 < r ^ (n + 1) := pow_pos hr0 _
  rw [div_lt_iff₀ hrn, pow_succ] at hn
  have hpow : 0 ≤ ((n : ℝ) + 1) ^ k := by positivity
  have h1 : K * ((n : ℝ) + 1) ^ k ≤ (|K| + 1) * ((n : ℝ) + 1) ^ k :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hpow
  have h2 : (|K| + 1) * ((n : ℝ) + 1) ^ k < (|K| + 1) * ((r * (|K| + 1))⁻¹ * (r ^ n * r)) :=
    mul_lt_mul_of_pos_left hn hK
  have h3 : (|K| + 1) * ((r * (|K| + 1))⁻¹ * (r ^ n * r)) = r ^ n := by
    field_simp
  linarith
