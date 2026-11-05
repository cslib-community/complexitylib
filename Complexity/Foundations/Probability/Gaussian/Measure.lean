/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, normalization of Gaussian weights)

public import Complexity.Foundations.Probability.Gaussian.Fourier
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Normalization of the continuous Gaussian weight

## Main results

* `ProbabilityTheory.integral_gaussianWeight`: the integral of the weight is `s ^ dim`.
* `ProbabilityTheory.isProbabilityMeasure_gaussianWeight`: dividing by this factor gives an
  actual probability measure through the existing `Measure.withDensity` construction.

## References

The width and density conventions are [Regev2009], equations (4) and (5), printed page 13
of the May 2, 2009 author version. These are analytic probability measures, without a claim
about efficient sampling or finite-precision implementation.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped FourierTransform

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The positive-width real Gaussian weight is integrable for canonical ambient volume. -/
theorem integrable_gaussianWeight_real (s : ℝ) (hs : 0 < s) :
    Integrable (gaussianWeight s : E → ℝ) := by
  simpa using (integrable_gaussianWeight (E := E) s hs).re

/-- The Gaussian weight has integral `s ^ dim`, including dimension zero. -/
theorem integral_gaussianWeight (s : ℝ) (hs : 0 < s) :
    (∫ x : E, gaussianWeight s x) = s ^ finrank ℝ E := by
  have h := fourier_gaussianWeight s hs (0 : E)
  simp only [Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul,
    gaussianWeight, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div,
    Real.exp_zero, Complex.ofReal_one, mul_one, integral_complex_ofReal, ← Complex.ofReal_pow] at h
  simpa only [gaussianWeight] using Complex.ofReal_injective h

/-- The source's normalized continuous Gaussian is an actual probability measure. -/
theorem isProbabilityMeasure_gaussianWeight (s : ℝ) (hs : 0 < s) :
    IsProbabilityMeasure
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) := by
  rw [isProbabilityMeasure_iff, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_gaussianWeight_real s hs).div_const _) (Filter.Eventually.of_forall
        (fun x ↦ div_nonneg (gaussianWeight_pos s x).le (pow_pos hs _).le)),
    integral_div, integral_gaussianWeight s hs, div_self (pow_pos hs _).ne', ENNReal.ofReal_one]

end ProbabilityTheory
