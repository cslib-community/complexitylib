/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Elementary bounds for hyperbolic functions

These are companions of Mathlib's `Real.cosh_le_exp_half_sq`, proved the same way by comparing
power series term by term.

## Main results

* `Real.sinh_le_mul_exp_half_sq`: `sinh x ≤ x · exp (x² / 2)` for `x ≥ 0`.
* `Real.cosh_add_mul_sinh_le_exp`: `cosh s + m · sinh s ≤ exp (m s + s² / 2)` for `m, s ≥ 0`.
* `Real.tanh_nonneg_iff`: `0 ≤ tanh x ↔ 0 ≤ x`.
* `Real.sinh_le_mul_cosh`, `Real.tanh_le_self`: `sinh x ≤ x · cosh x` and `tanh x ≤ x` for
  `x ≥ 0`.
* `Real.tanh_half_eq_exp_sub_one_div`: `tanh (x / 2) = (exp x - 1) / (exp x + 1)`.
* `Real.tanh_half_le_exp_sub_one`: `tanh (x / 2) ≤ exp x - 1` for `x ≥ 0`.
-/

public section

namespace Real

/-- `sinh x ≤ x · exp (x² / 2)` for `x ≥ 0`, the odd companion of `Real.cosh_le_exp_half_sq`. -/
theorem sinh_le_mul_exp_half_sq {x : ℝ} (hx : 0 ≤ x) : sinh x ≤ x * exp (x ^ 2 / 2) := by
  rw [sinh_eq_tsum, exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ, ← tsum_mul_left]
  refine x.hasSum_sinh.summable.tsum_le_tsum (fun i ↦ ?_)
    ((NormedSpace.expSeries_summable' (x ^ 2 / 2)).mul_left x)
  have hfac : ((2 ^ i * i.factorial : ℕ) : ℝ) ≤ ((2 * i + 1).factorial : ℕ) := by
    norm_cast
    calc 2 ^ i * i.factorial ≤ (2 * i).factorial :=
          Nat.two_pow_mul_factorial_le_factorial_two_mul _
      _ ≤ (2 * i + 1).factorial := Nat.factorial_le (Nat.le_succ _)
  have hpos : (0 : ℝ) < ((2 ^ i * i.factorial : ℕ) : ℝ) := by positivity
  simp only [smul_eq_mul, div_pow]
  rw [pow_succ, ← pow_mul]
  push_cast at hfac hpos ⊢
  rw [show x * ((i.factorial : ℝ)⁻¹ * (x ^ (2 * i) / 2 ^ i)) =
    x ^ (2 * i) * x / (2 ^ i * i.factorial) by field_simp]
  gcongr

/-- `cosh s + m · sinh s ≤ exp (m s + s² / 2)` for `m, s ≥ 0`. -/
theorem cosh_add_mul_sinh_le_exp {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    cosh s + m * sinh s ≤ exp (m * s + s ^ 2 / 2) := by
  calc cosh s + m * sinh s ≤ exp (s ^ 2 / 2) + m * (s * exp (s ^ 2 / 2)) := by
        gcongr
        · exact cosh_le_exp_half_sq s
        · exact sinh_le_mul_exp_half_sq hs
    _ = (1 + m * s) * exp (s ^ 2 / 2) := by ring
    _ ≤ exp (m * s) * exp (s ^ 2 / 2) := by
        gcongr
        linarith [add_one_le_exp (m * s)]
    _ = exp (m * s + s ^ 2 / 2) := (exp_add _ _).symm

/-- `sinh x ≤ x · cosh x` for `x ≥ 0`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : sinh x ≤ x * cosh x := by
  rw [sinh_eq_tsum, cosh_eq_tsum, ← tsum_mul_left]
  refine x.hasSum_sinh.summable.tsum_le_tsum (fun i ↦ ?_) (x.hasSum_cosh.summable.mul_left x)
  have hfac : ((2 * i).factorial : ℝ) ≤ ((2 * i + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hpos : (0 : ℝ) < ((2 * i).factorial : ℝ) := by positivity
  rw [pow_succ, mul_div_assoc', mul_comm x]
  gcongr

/-- `tanh x` is nonnegative exactly when `x` is. -/
theorem tanh_nonneg_iff {x : ℝ} : 0 ≤ tanh x ↔ 0 ≤ x := by
  rw [tanh_eq_sinh_div_cosh, le_div_iff₀ (cosh_pos x), zero_mul, sinh_eq, le_div_iff₀ two_pos,
    zero_mul, sub_nonneg, exp_le_exp]
  constructor <;> intro h <;> linarith

/-- `tanh x ≤ x` for `x ≥ 0`. -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  rw [tanh_eq_sinh_div_cosh, div_le_iff₀ (cosh_pos x)]
  exact sinh_le_mul_cosh hx

/-- `tanh (x / 2) = (exp x - 1) / (exp x + 1)`. -/
theorem tanh_half_eq_exp_sub_one_div (x : ℝ) : tanh (x / 2) = (exp x - 1) / (exp x + 1) := by
  have h : exp x = exp (x / 2) * exp (x / 2) := by
    rw [← exp_add]; ring_nf
  have h0 : 0 < exp (x / 2) := exp_pos _
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, h, exp_neg]
  field_simp

/-- `tanh (x / 2) ≤ exp x - 1` for `x ≥ 0`. -/
theorem tanh_half_le_exp_sub_one {x : ℝ} (hx : 0 ≤ x) : tanh (x / 2) ≤ exp x - 1 := by
  rw [tanh_half_eq_exp_sub_one_div]
  exact div_le_self (by linarith [one_le_exp hx]) (by linarith [exp_pos x])

end Real
