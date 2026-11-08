/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`)

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Degree-ten Taylor bounds and tangent lines for `sin` and `cos`

Mathlib's `Real.cos_bound` and `Real.sin_bound` approximate `cos x` and `sin x` on `[-1, 1]` by
their Taylor polynomials of degree `2` and `3`, with errors of order `x ^ 4` and `x ^ 5`. Some
numerical constants need more precision: the Goemans–Williamson constant, for instance, is
determined by a tangent line whose margin is about `10⁻⁵`. This module gives the Taylor polynomials
of degree `8` and `9`, both with error at most `|x| ^ 10 * (11 / 36288000)` (about `3 · 10⁻⁷` at
`|x| = 1`), from Mathlib's `Complex.exp_bound` at `x * I` with ten terms. It also states the
tangent-line bound of the concave function `cos` on `[-π/2, π/2]`.

## Main results

* `Real.cos_bound_ten`, `Real.sin_bound_ten`: degree-ten Taylor bounds for `cos` and `sin` on
  `[-1, 1]`.
* `Real.cos_le_cos_sub_sin_mul`: on `[-π/2, π/2]`, `cos` lies below its tangent lines.
-/

public section

open Set

namespace Real

/-- The first ten terms of the exponential series at `x * I`, split into the Taylor polynomials
of `cos` and `sin`. -/
private theorem sum_range_ten_ofReal_mul_I (x : ℝ) :
    ∑ m ∈ Finset.range 10, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 : ℝ) : ℂ) *
          Complex.I := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow]
  push_cast
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  set I := Complex.I
  linear_combination ((x : ℂ) ^ 2 / 2 + (x : ℂ) ^ 3 * I / 6 + (x : ℂ) ^ 6 / 720 +
    (x : ℂ) ^ 7 * I / 5040) * h2

/-- Both Taylor errors are bounded by the error of the exponential series at `x * I`. -/
private theorem cos_sin_bound_ten {x : ℝ} (hx : |x| ≤ 1) :
    |cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320)| ≤
      |x| ^ 10 * (11 / 36288000) ∧
    |sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)| ≤
      |x| ^ 10 * (11 / 36288000) := by
  have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I) (n := 10)
    (by simpa [Complex.norm_real] using hx) (by norm_num)
  rw [sum_range_ten_ofReal_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    at hb
  have key : ((cos x : ℝ) : ℂ) + ((sin x : ℝ) : ℂ) * Complex.I -
      (((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 : ℝ) : ℂ) * Complex.I) =
      ((cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) : ℝ) : ℂ) +
        ((sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    ring
  rw [key] at hb
  have hr : ‖(x : ℂ) * Complex.I‖ ^ 10 * (((Nat.succ 10 : ℕ) : ℝ) *
      (((Nat.factorial 10 : ℕ) : ℝ) * ((10 : ℕ) : ℝ))⁻¹) = |x| ^ 10 * (11 / 36288000) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      Nat.factorial]
    norm_num
  rw [hr] at hb
  generalize cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) = a at hb ⊢
  generalize sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) = b at hb ⊢
  constructor
  · simpa using (Complex.abs_re_le_norm _).trans hb
  · simpa using (Complex.abs_im_le_norm _).trans hb

/-- **Degree-eight Taylor bound for `cos`** on `[-1, 1]`, with the error term of ten terms of the
exponential series. -/
theorem cos_bound_ten {x : ℝ} (hx : |x| ≤ 1) :
    |cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320)| ≤
      |x| ^ 10 * (11 / 36288000) :=
  (cos_sin_bound_ten hx).1

/-- **Degree-nine Taylor bound for `sin`** on `[-1, 1]`, with the error term of ten terms of the
exponential series. -/
theorem sin_bound_ten {x : ℝ} (hx : |x| ≤ 1) :
    |sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)| ≤
      |x| ^ 10 * (11 / 36288000) :=
  (cos_sin_bound_ten hx).2

/-- **Tangent lines of `cos`.** On `[-π/2, π/2]`, where `cos` is concave, `cos` lies below its
tangent line at any point `x₀` of the interval. -/
theorem cos_le_cos_sub_sin_mul {x x₀ : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2))
    (hx₀ : x₀ ∈ Icc (-(π / 2)) (π / 2)) : cos x ≤ cos x₀ - sin x₀ * (x - x₀) := by
  have hconv : ConvexOn ℝ (Icc (-(π / 2)) (π / 2)) (-cos) :=
    strictConcaveOn_cos_Icc.concaveOn.neg
  have hd : HasDerivAt (-cos) (sin x₀) x₀ := by simpa using (hasDerivAt_cos x₀).neg
  rcases lt_trichotomy x x₀ with h | rfl | h
  · have := hconv.slope_le_of_hasDerivAt hx hx₀ h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    simp only [Pi.neg_apply] at this
    linarith
  · simp
  · have := hconv.le_slope_of_hasDerivAt hx₀ hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    simp only [Pi.neg_apply] at this
    linarith

end Real
