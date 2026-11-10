/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Mathlib/Analysis/SpecificLimits/Normed.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A falling factorial against a geometric factor

For fixed `k` and `0 ≤ q < 1`, `n (n - 1) ⋯ (n - k + 1) · q ^ (n - k) → 0` as `n → ∞`. This is the
union bound of first-moment arguments over the `k`-tuples of distinct elements of an `n`-element
set: there are `n.descFactorial k` of them, and each one fails independently at each of the
`n - k` other elements with probability `q`.

## Main results

* `tendsto_descFactorial_mul_pow_sub`: the limit above.
-/

public section

open Filter

/-- `n (n - 1) ⋯ (n - k + 1) · q ^ (n - k) → 0` for fixed `k` and `0 ≤ q < 1`. -/
theorem tendsto_descFactorial_mul_pow_sub (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (n.descFactorial k : ℝ) * q ^ (n - k)) atTop (nhds 0) := by
  rcases hq0.eq_or_lt with rfl | hq0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop k] with n hn
    rw [zero_pow (Nat.sub_ne_zero_of_lt hn), mul_zero]
  -- `n ^ k q ^ n → 0`, and the falling factorial is at most `n ^ k`.
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (abs_lt.2 ⟨by linarith, hq1⟩)).const_mul (q ^ k)⁻¹
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _)) ?_ hlim
  filter_upwards [eventually_ge_atTop k] with n hn
  calc (n.descFactorial k : ℝ) * q ^ (n - k) ≤ (n : ℝ) ^ k * q ^ (n - k) := by
        gcongr
        exact_mod_cast Nat.descFactorial_le_pow n k
    _ = (q ^ k)⁻¹ * ((n : ℝ) ^ k * q ^ n) := by
        rw [← pow_sub_mul_pow q hn]
        field_simp
