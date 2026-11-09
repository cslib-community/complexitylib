/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import CslibFrontier.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Low moments of the standard Gaussian

The moment generating function of the standard Gaussian is `t ↦ exp (t ^ 2 / 2)`
(`mgf_id_gaussianReal`), and the `n`th moment is its `n`th derivative at `0`
(`iteratedDeriv_mgf_zero`). Differentiating four times gives `E[z³] = 0` and `E[z⁴] = 3`, the
moments used by the Invariance Principle [O'Donnell, Section 11.6][ODonnell2014].

## Main results

* `ProbabilityTheory.integral_pow_gaussianReal_eq_iteratedDeriv`: the `n`th moment of the standard
  Gaussian is the `n`th derivative of `exp (t ^ 2 / 2)` at `0`.
* `ProbabilityTheory.integral_sq_gaussianReal`, `ProbabilityTheory.integral_pow_three_gaussianReal`,
  `ProbabilityTheory.integral_pow_four_gaussianReal`: `E[z²] = 1`, `E[z³] = 0`, `E[z⁴] = 3`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real

namespace ProbabilityTheory

/-- Differentiating `p t · exp (t ^ 2 / 2)`. -/
private theorem deriv_mul_exp_half_sq {p p' : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * exp (t ^ 2 / 2)) = fun t => (p' t + t * p t) * exp (t ^ 2 / 2) := by
  funext t
  have hE : HasDerivAt (fun t => exp (t ^ 2 / 2)) (exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1; push_cast; ring
  exact ((hp t).mul hE).deriv.trans (by ring)

private theorem iteratedDeriv_three_exp_half_sq :
    iteratedDeriv 3 (fun t => exp (t ^ 2 / 2)) = fun t => (3 * t + t ^ 3) * exp (t ^ 2 / 2) := by
  have h0 : (fun t => exp (t ^ 2 / 2)) = fun t => (fun _ => (1 : ℝ)) t * exp (t ^ 2 / 2) := by
    simp
  have h1 : iteratedDeriv 1 (fun t => exp (t ^ 2 / 2)) = fun t => t * exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_one, h0, deriv_mul_exp_half_sq (p' := fun _ => 0)
      fun t => hasDerivAt_const t 1]
    simp
  have h2 : iteratedDeriv 2 (fun t => exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h1, deriv_mul_exp_half_sq (p' := fun _ => 1) hasDerivAt_id']
    funext t; ring
  rw [iteratedDeriv_succ, h2, deriv_mul_exp_half_sq (p' := fun t => 2 * t)
    fun t => by simpa using ((hasDerivAt_pow 2 t).const_add 1)]
  funext t; ring

private theorem iteratedDeriv_four_exp_half_sq :
    iteratedDeriv 4 (fun t => exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * exp (t ^ 2 / 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_exp_half_sq,
    deriv_mul_exp_half_sq (p' := fun t => 3 + 3 * t ^ 2) fun t => by
      convert ((hasDerivAt_id' t).const_mul 3).add (hasDerivAt_pow 3 t) using 1; norm_num]
  funext t; ring

/-- The `n`th moment of the standard Gaussian is the `n`th derivative of its moment generating
function `t ↦ exp (t ^ 2 / 2)` at `0`. -/
theorem integral_pow_gaussianReal_eq_iteratedDeriv (n : ℕ) :
    ∫ x, x ^ n ∂gaussianReal 0 1 = iteratedDeriv n (fun t => exp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1)
    (by simp [integrableExpSet_id_gaussianReal]) n
  rw [mgf_id_gaussianReal] at h
  simpa using h.symm

/-- The second moment of the standard Gaussian is `1`. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero (memLp_id_gaussianReal 2).aemeasurable
    integral_id_gaussianReal] at h
  simpa using h

/-- The third moment of the standard Gaussian is `0`. -/
theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, iteratedDeriv_three_exp_half_sq]; simp

/-- The fourth moment of the standard Gaussian is `3`. -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, iteratedDeriv_four_exp_half_sq]; simp

end ProbabilityTheory
