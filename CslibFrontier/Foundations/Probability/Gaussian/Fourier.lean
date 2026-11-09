/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Fourier transform of lattice Gaussian weights)

public import CslibFrontier.Foundations.Probability.Gaussian.Discrete
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier transform of Gaussian weights

The existing weight of positive width `s` has Fourier transform equal to `s ^ dim` times
its reciprocal-width weight, for canonical volume in every finite-dimensional real inner
product space. These are analytic prerequisites for lattice Poisson summation; no Poisson
identity is assumed.

## Main results

* `ProbabilityTheory.integrable_gaussianWeight`: integrability of the complex-valued weight.
* `ProbabilityTheory.fourier_gaussianWeight`: its Fourier transform at every frequency.
* `ZLattice.summable_fourier_gaussianWeight`: summability on any discrete frequency lattice.

## References

The width convention and Gaussian Fourier identity are those in [Regev2009], printed page 18
immediately before Lemma 2.14. The proof specializes Mathlib's general Gaussian Fourier transform.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace ProbabilityTheory

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem gaussianWeight_eq_cexp (s : ℝ) (x : E) :
    (gaussianWeight s x : ℂ) =
      Complex.exp (-((Real.pi / s ^ 2 : ℝ) : ℂ) * ‖x‖ ^ 2) := by
  rw [gaussianWeight, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The positive-width Gaussian weight is integrable for canonical ambient volume. -/
theorem integrable_gaussianWeight (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : E => (gaussianWeight s x : ℂ)) := by
  have hb : 0 < ((Real.pi / s ^ 2 : ℝ) : ℂ).re := by
    simpa only [Complex.ofReal_re] using div_pos Real.pi_pos (sq_pos_of_pos hs)
  simpa only [gaussianWeight_eq_cexp, zero_mul, add_zero] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : E)

/-- Fourier transformation replaces the width by its reciprocal and contributes `s ^ dim`. -/
theorem fourier_gaussianWeight (s : ℝ) (hs : 0 < s) (w : E) :
    𝓕 (fun x : E => (gaussianWeight s x : ℂ)) w =
      (s : ℂ) ^ Module.finrank ℝ E * (gaussianWeight (1 / s) w : ℂ) := by
  have hb : 0 < ((Real.pi / s ^ 2 : ℝ) : ℂ).re := by
    simpa only [Complex.ofReal_re] using div_pos Real.pi_pos (sq_pos_of_pos hs)
  simp_rw [gaussianWeight_eq_cexp]
  rw [fourier_gaussian_innerProductSpace hb]
  have hp : (Real.pi : ℂ) / ((Real.pi / s ^ 2 : ℝ) : ℂ) = (s : ℂ) ^ 2 := by
    push_cast
    field_simp
  rw [hp]
  congr 1
  · rw [← Complex.cpow_nat_mul' (x := (s : ℂ)) (n := 2)]
    · rw [Nat.cast_ofNat, show (2 : ℂ) * (Module.finrank ℝ E / 2 : ℂ) = Module.finrank ℝ E by ring,
        Complex.cpow_natCast]
    · simp [Complex.arg_ofReal_of_nonneg hs.le, Real.pi_pos]
    · simp [Complex.arg_ofReal_of_nonneg hs.le, Real.pi_pos.le]
  · congr 1
    push_cast
    field_simp

end ProbabilityTheory

namespace ZLattice

/-- Gaussian Fourier samples are summable even when the discrete frequency lattice
is not full rank. -/
theorem summable_fourier_gaussianWeight (D : Submodule ℤ E) [DiscreteTopology D]
    (s : ℝ) (hs : 0 < s) :
    Summable (fun w : D => 𝓕 (fun x : E => (gaussianWeight s x : ℂ)) (w : E)) := by
  simp_rw [fourier_gaussianWeight s hs]
  apply Summable.mul_left
  apply Complex.summable_ofReal.mpr
  simpa only [sub_zero] using summable_gaussianWeight D (1 / s) (one_div_pos.mpr hs) (0 : E)

end ZLattice
