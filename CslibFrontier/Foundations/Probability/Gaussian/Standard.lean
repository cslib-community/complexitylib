/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Gaussian density and standard law)

public import CslibFrontier.Foundations.Probability.Gaussian.Measure
public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The normalized Gaussian density as a scaled standard Gaussian

## Main results

* `ProbabilityTheory.gaussianWeight_withDensity_eq_map_stdGaussian`: identifies the actual
  normalized density with a scaled standard Gaussian measure.
* `ProbabilityTheory.gaussianWeight_withDensity_map_inner`: computes its projection law,
  including the zero vector and dimension zero.

## References

The width convention is [Regev2009], equation (5), printed page 13 of the May 2, 2009
author version. The identification below is an original assembly of Gaussian Fourier
transformation and characteristic-function uniqueness. It is an identity of analytic
probability measures, without a sampling algorithm or a finite-precision claim.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem charFun_gaussianWeight (s : ℝ) (hs : 0 < s) (t : E) :
    charFun (volume.withDensity
      (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) t =
      (gaussianWeight (1 / s) (-(2 * Real.pi)⁻¹ • t) : ℂ) := by
  rw [charFun_eq_fourierIntegral', VectorFourier.fourierIntegral,
    integral_withDensity_eq_integral_toReal_smul (by unfold gaussianWeight; fun_prop)
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (gaussianWeight_pos s _).le
    (pow_pos hs _).le), Pi.one_apply, innerₗ_apply_apply, Circle.smul_def, smul_eq_mul, mul_one,
    RCLike.real_smul_eq_coe_mul]
  change (∫ x : E, ((gaussianWeight s x / s ^ finrank ℝ E : ℝ) : ℂ) *
    (Real.fourierChar (-⟪x, -(2 * Real.pi)⁻¹ • t⟫) : ℂ)) = _
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  have h : (∫ x : E, ((gaussianWeight s x : ℂ) / (s : ℂ) ^ finrank ℝ E) *
      (Real.fourierChar (-⟪x, -(2 * Real.pi)⁻¹ • t⟫) : ℂ)) =
      𝓕 (fun x : E ↦ (gaussianWeight s x : ℂ)) (-(2 * Real.pi)⁻¹ • t) /
        (s : ℂ) ^ finrank ℝ E := by
    rw [Real.fourier_eq, ← integral_div]
    congr 1
    funext x
    simp only [Circle.smul_def]
    ring
  rw [h, fourier_gaussianWeight s hs]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hs.ne'))

/-- The positive-width normalized Gaussian density is a scaled standard Gaussian measure. -/
theorem gaussianWeight_withDensity_eq_map_stdGaussian (s : ℝ) (hs : 0 < s) :
    volume.withDensity
        (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E)) =
      (stdGaussian E).map (fun x ↦ (s / Real.sqrt (2 * Real.pi)) • x) := by
  let := isProbabilityMeasure_gaussianWeight (E := E) s hs
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianWeight s hs, charFun_map_smul, charFun_stdGaussian]
  rw [gaussianWeight, Complex.ofReal_exp]
  have hexp : -Real.pi * ‖-(2 * Real.pi)⁻¹ • t‖ ^ 2 / (1 / s) ^ 2 =
      -‖(s / Real.sqrt (2 * Real.pi)) • t‖ ^ 2 / 2 := by
    rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, div_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    field_simp
  rw [hexp]
  push_cast
  rfl

/-- The projection of the actual normalized density has variance `(s ‖z‖)² / (2π)`.
The zero vector and dimension zero give the same statement, with variance zero. -/
theorem gaussianWeight_withDensity_map_inner (s : ℝ) (hs : 0 < s) (z : E) :
    (volume.withDensity
        (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))).map
        (fun x ↦ ⟪z, x⟫) =
      gaussianReal 0 (((s * ‖z‖) ^ 2 / (2 * Real.pi)).toNNReal) := by
  rw [gaussianWeight_withDensity_eq_map_stdGaussian s hs,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : (fun x : E ↦ ⟪z, (s / Real.sqrt (2 * Real.pi)) • x⟫) =
      (fun x ↦ ⟪(s / Real.sqrt (2 * Real.pi)) • z, x⟫) := by
    funext x
    rw [inner_smul_right, real_inner_smul_left]
  change (stdGaussian E).map (fun x ↦ ⟪z, (s / Real.sqrt (2 * Real.pi)) • x⟫) = _
  rw [hfun, stdGaussian_map_inner]
  congr 1
  apply NNReal.eq
  change ‖(s / Real.sqrt (2 * Real.pi)) • z‖ ^ 2 =
    (((s * ‖z‖) ^ 2 / (2 * Real.pi)).toNNReal : ℝ)
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  ring

end ProbabilityTheory
