/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/Complex/Exponential.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A lower bound for `(1 - a⁻¹) ^ d`

If `d + 1 ≤ a` then `e⁻¹ ≤ (1 - a⁻¹) ^ d` (`Real.exp_neg_one_le_one_sub_inv_pow`). Each factor
satisfies `1 - a⁻¹ ≥ e^{-1 / (a - 1)}`, which is `1 + 1 / (a - 1) ≤ e^{1 / (a - 1)}` inverted, and
`d / (a - 1) ≤ 1`. The case `a = d + 1` is `(d / (d + 1)) ^ d ≥ e⁻¹`, the bound behind the
symmetric Lovász Local Lemma, and the case `a = q - Δ` bounds the probability that `Δ` heat-bath
updates all avoid a given color in [LevinPeres2017], proof of Lemma 14.16. Mathlib's
`Real.one_sub_div_pow_le_exp_neg` is the matching upper bound.

## Main results

* `Real.exp_neg_one_le_one_sub_inv_pow`: `e⁻¹ ≤ (1 - a⁻¹) ^ d` for `d + 1 ≤ a`.

## References

* [LevinPeres2017], proof of Lemma 14.16.
-/

public section

namespace Real

/-- `e⁻¹ ≤ (1 - a⁻¹) ^ d` when `d + 1 ≤ a`. -/
theorem exp_neg_one_le_one_sub_inv_pow {a : ℝ} {d : ℕ} (ha : (d : ℝ) + 1 ≤ a) :
    exp (-1) ≤ (1 - a⁻¹) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, exp_le_one_iff]
    norm_num
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha0 : 0 < a - 1 := by linarith
  -- `e^{-1 / (a - 1)} ≤ 1 - a⁻¹`, from `1 + 1 / (a - 1) ≤ e^{1 / (a - 1)}`
  have h1 : exp (-(1 / (a - 1))) ≤ 1 - a⁻¹ := by
    have h := add_one_le_exp (1 / (a - 1))
    have hpos : 0 < 1 / (a - 1) + 1 := by positivity
    rw [exp_neg]
    calc (exp (1 / (a - 1)))⁻¹ ≤ (1 / (a - 1) + 1)⁻¹ := inv_anti₀ hpos h
      _ = 1 - a⁻¹ := by
          have : a - 1 ≠ 0 := ha0.ne'
          have : a ≠ 0 := by linarith
          field_simp
          ring
  calc exp (-1) ≤ exp (-(1 / (a - 1))) ^ d := by
        rw [← exp_nat_mul, exp_le_exp]
        have hd : (d : ℝ) / (a - 1) ≤ 1 := by
          rw [div_le_one ha0]
          linarith
        have : (d : ℝ) * -(1 / (a - 1)) = -((d : ℝ) / (a - 1)) := by ring
        rw [this]
        linarith
    _ ≤ (1 - a⁻¹) ^ d := pow_le_pow_left₀ (exp_pos _).le h1 d

end Real
