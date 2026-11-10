/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Cauchy–Schwarz for real integrals and integrability of moments

The **Cauchy–Schwarz inequality** `(∫ f g)² ≤ (∫ f²) (∫ g²)` for real functions whose squares and
product are integrable (`MeasureTheory.sq_integral_mul_le`). Unlike Mathlib's Hölder inequality
`integral_mul_le_Lp_mul_Lq_of_nonneg`, it needs no sign condition and is stated with natural squares
rather than real powers and roots. The proof is the discriminant argument: `t ↦ ∫ (t f - g)²` is a
nonnegative quadratic polynomial.

For a real random variable in `Lⁿ`, the moments `E[zʲ]` and absolute moments `E[|z|ʲ]` of order
`j ≤ n` are integrable under a finite measure (`MeasureTheory.integrable_pow_of_memLp`,
`MeasureTheory.integrable_abs_pow_of_memLp`).

## Main results

* `MeasureTheory.sq_integral_mul_le`: Cauchy–Schwarz, `(∫ f g)² ≤ (∫ f²) (∫ g²)`.
* `MeasureTheory.integrable_pow_of_memLp`: `z ∈ Lⁿ` and `j ≤ n` give `zʲ` integrable.
* `MeasureTheory.integrable_abs_pow_of_memLp`: `z ∈ Lⁿ` and `j ≤ n` give `|z|ʲ` integrable.
-/

public section

namespace MeasureTheory

/-- **Cauchy–Schwarz** for real integrals: `(∫ f g)² ≤ (∫ f²) (∫ g²)`. -/
theorem sq_integral_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun x => f x ^ 2) P) (hg : Integrable (fun x => g x ^ 2) P)
    (hfg : Integrable (fun x => f x * g x) P) :
    (∫ x, f x * g x ∂P) ^ 2 ≤ (∫ x, f x ^ 2 ∂P) * ∫ x, g x ^ 2 ∂P := by
  have h (t : ℝ) : 0 ≤ (∫ x, f x ^ 2 ∂P) * (t * t) + (-2 * ∫ x, f x * g x ∂P) * t +
      ∫ x, g x ^ 2 ∂P := by
    have h1 : ∫ x, (t * f x - g x) ^ 2 ∂P =
        ∫ x, ((t * t) * f x ^ 2 + (-2 * t) * (f x * g x) + g x ^ 2) ∂P := by
      congr 1 with x : 1; ring
    have h2 : ∫ x, (t * f x - g x) ^ 2 ∂P = (∫ x, f x ^ 2 ∂P) * (t * t) +
        (-2 * ∫ x, f x * g x ∂P) * t + ∫ x, g x ^ 2 ∂P := by
      rw [h1, integral_add (f := fun x => t * t * f x ^ 2 + -2 * t * (f x * g x))
        ((hf.const_mul _).add (hfg.const_mul _)) hg,
        integral_add (f := fun x => t * t * f x ^ 2) (g := fun x => -2 * t * (f x * g x))
        (hf.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← h2]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

/-- Moments of order at most `n` of a real random variable in `Lⁿ` are integrable. -/
theorem integrable_pow_of_memLp {μ : Measure ℝ} [IsFiniteMeasure μ] {n : ℕ} (h : MemLp id n μ)
    {j : ℕ} (hj : j ≤ n) : Integrable (fun s => s ^ j) μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have h' : MemLp id (j : ENNReal) μ := h.mono_exponent (by exact_mod_cast hj)
  refine (h'.integrable_norm_pow hj0.ne').mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  simp [norm_pow]

/-- Absolute moments of order at most `n` of a real random variable in `Lⁿ` are integrable. -/
theorem integrable_abs_pow_of_memLp {μ : Measure ℝ} [IsFiniteMeasure μ] {n : ℕ}
    (h : MemLp id n μ) {j : ℕ} (hj : j ≤ n) : Integrable (fun s => |s| ^ j) μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have h' : MemLp id (j : ENNReal) μ := h.mono_exponent (by exact_mod_cast hj)
  simpa using h'.integrable_norm_pow hj0.ne'

end MeasureTheory
