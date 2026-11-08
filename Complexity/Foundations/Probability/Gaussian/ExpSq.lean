/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import Complexity.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential moments of the square of a centered Gaussian

For a centered real Gaussian `Z` of variance `v` and `c v < 1 / 2`, the function `exp (c Z²)` is
integrable and `𝔼 exp (c Z²) = 1 / √(1 - 2 c v)`. This is the moment generating function of the
chi-squared distribution with one degree of freedom, scaled by `v`. The nondegenerate case
combines the Gaussian density with `exp (c z²)` into one Gaussian integral. When `v = 0` the law is
the Dirac mass at `0`, and both sides are `1`.

## Main results

* `ProbabilityTheory.integrable_exp_mul_sq_gaussianReal`: `exp (c z²)` is integrable for
  `gaussianReal 0 v` when `c v < 1 / 2`.
* `ProbabilityTheory.integral_exp_mul_sq_gaussianReal`: its integral is `(√(1 - 2 c v))⁻¹`.
-/

public section

open MeasureTheory Real
open scoped NNReal

namespace ProbabilityTheory

/-- The centered Gaussian density times `exp (c z²)` is a multiple of `exp (-(1 / (2v) - c) z²)`. -/
private theorem gaussianPDFReal_zero_mul_exp {v : ℝ≥0} (hv : v ≠ 0) (c z : ℝ) :
    gaussianPDFReal 0 v z * exp (c * z ^ 2) =
      (√(2 * π * v))⁻¹ * exp (-(1 / (2 * v) - c) * z ^ 2) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  rw [gaussianPDFReal, sub_zero, mul_assoc, ← exp_add]
  congr 2
  field_simp
  ring

/-- For a centered Gaussian of variance `v` and `c v < 1 / 2`, `exp (c z²)` is integrable. -/
theorem integrable_exp_mul_sq_gaussianReal {v : ℝ≥0} {c : ℝ} (hc : c * v < 1 / 2) :
    Integrable (fun z => exp (c * z ^ 2)) (gaussianReal 0 v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    exact integrable_dirac enorm_lt_top
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (NNReal.coe_ne_zero.2 hv).symm
  have hpos : 0 < 1 / (2 * v) - c := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    linarith
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_zero_mul_exp hv]
  exact (integrable_exp_neg_mul_sq hpos).const_mul _

/-- **The moment generating function of the square of a centered Gaussian**: for variance `v` and
`c v < 1 / 2`, `𝔼 exp (c Z²) = 1 / √(1 - 2 c v)`. -/
theorem integral_exp_mul_sq_gaussianReal {v : ℝ≥0} {c : ℝ} (hc : c * v < 1 / 2) :
    ∫ z, exp (c * z ^ 2) ∂(gaussianReal 0 v) = (√(1 - 2 * (c * v)))⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, integral_dirac]
    simp
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (NNReal.coe_ne_zero.2 hv).symm
  have h1 : 0 < 1 - 2 * (c * v) := by linarith
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, gaussianPDFReal_zero_mul_exp hv]
  rw [integral_const_mul, integral_gaussian]
  rw [show π / (1 / (2 * v) - c) = (2 * π * v) / (1 - 2 * (c * v)) by
      field_simp, Real.sqrt_div' _ h1.le]
  have : 0 < √(2 * π * v) := by positivity
  field_simp

end ProbabilityTheory
