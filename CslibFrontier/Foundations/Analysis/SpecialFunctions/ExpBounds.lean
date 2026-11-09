/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Exponential.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Polynomial bounds on the real exponential

Two Taylor-type bounds on the real exponential for nonnegative arguments. They are the scalar
inequalities behind multiplicative Chernoff bounds and the Johnson–Lindenstrauss lemma.

* `exp (-x) ≤ 1 - x + x² / 2` (`Real.exp_neg_le_one_sub_add_sq_div_two`): multiply by
  `exp x ≥ 1 + x + x² / 2`.
* `1 + x ≤ exp (x - x² / 2 + x³ / 3)` (`Real.one_add_le_exp_sub_sq_div_two_add_cube_div_three`),
  equivalently `log (1 + x) ≤ x - x² / 2 + x³ / 3`. The exponent `v` is nonnegative. The degree-four
  Taylor polynomial `1 + v + v² / 2 + v³ / 6 + v⁴ / 24` is at most `exp v` and already dominates
  `1 + x`, by an explicit sum of nonnegative terms.

`CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic` has the weaker
`Real.exp_neg_le_one_sub_add_sq`, `exp (-y) ≤ 1 - y + y²`, valid for all `-1 ≤ y`.

## Main results

* `Real.exp_neg_le_one_sub_add_sq_div_two`: `exp (-x) ≤ 1 - x + x² / 2` for `0 ≤ x`.
* `Real.one_add_le_exp_sub_sq_div_two_add_cube_div_three`: `1 + x ≤ exp (x - x² / 2 + x³ / 3)` for
  `0 ≤ x`.
* `Real.exp_neg_two_le_one_third`: `exp (-2) ≤ 1 / 3`.
* `Real.one_sub_pow_le_exp`: `(1 - p) ^ R ≤ exp (-c)` for `p ≤ 1` and `c ≤ R p`.
* `Real.pow_le_one_third`: `p ^ k ≤ 1 / 3` for `0 ≤ p ≤ 1 - δ` and `2 ≤ δ k`.
-/

public section

namespace Real

/-- `exp (-x) ≤ 1 - x + x² / 2` for `0 ≤ x`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq := quadratic_le_exp_of_nonneg hx
  rw [exp_neg, inv_le_iff_one_le_mul₀ (exp_pos x)]
  nlinarith [sq_nonneg x, exp_pos x,
    mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 1 - x + x ^ 2 / 2 by nlinarith)]

/-- `1 + x ≤ exp (x - x² / 2 + x³ / 3)` for `0 ≤ x`; equivalently
`log (1 + x) ≤ x - x² / 2 + x³ / 3`. -/
theorem one_add_le_exp_sub_sq_div_two_add_cube_div_three {x : ℝ} (hx : 0 ≤ x) :
    1 + x ≤ exp (x - x ^ 2 / 2 + x ^ 3 / 3) := by
  have hv0 : 0 ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by nlinarith [sq_nonneg (x - 3 / 4), sq_nonneg x]
  have h := sum_le_exp_of_nonneg hv0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  refine le_trans ?_ h
  -- `1296 (v + v² / 2 + v³ / 6 + v⁴ / 24 - x)` is a sum of nonnegative terms of degree at most 12.
  have h1 : 0 ≤ x ^ 7 * (x - 9 / 4) ^ 2 := by positivity
  have h2 : 0 ≤ x ^ 5 * (x - 1) ^ 2 := by positivity
  have h3 : 0 ≤ x ^ 5 := by positivity
  have h4 : 0 ≤ x ^ 4 := by positivity
  linarith

/-- `exp (-2) ≤ 1 / 3`. -/
theorem exp_neg_two_le_one_third : exp (-2) ≤ 1 / 3 := by
  rw [exp_neg, inv_le_comm₀ (exp_pos 2) (by norm_num)]
  linarith [add_one_le_exp 2]

/-- `(1 - p) ^ R ≤ exp (-c)` once `c ≤ R p`. -/
theorem one_sub_pow_le_exp {p c : ℝ} {R : ℕ} (hp1 : p ≤ 1) (hc : c ≤ R * p) :
    (1 - p) ^ R ≤ exp (-c) := by
  calc (1 - p) ^ R ≤ exp (-p) ^ R :=
        pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) R
    _ = exp (-(R * p)) := by rw [← exp_nat_mul]; ring_nf
    _ ≤ exp (-c) := exp_le_exp.mpr (by linarith)

/-- Amplification bound: if `0 ≤ p ≤ 1 - δ` and `2 ≤ δ k`, then `p ^ k ≤ 1 / 3`. -/
theorem pow_le_one_third {p δ : ℝ} {k : ℕ} (hp : 0 ≤ p) (hpδ : p ≤ 1 - δ)
    (hk : 2 ≤ δ * k) : p ^ k ≤ 1 / 3 := by
  have hδ1 : δ ≤ 1 := by linarith
  have hpk : p ^ k ≤ (1 - δ) ^ k := pow_le_pow_left₀ hp hpδ k
  have hpow : (1 - δ) ^ k ≤ exp (-2) :=
    one_sub_pow_le_exp hδ1 (by linarith [mul_comm δ (k : ℝ)])
  exact hpk.trans (hpow.trans exp_neg_two_le_one_third)

end Real
