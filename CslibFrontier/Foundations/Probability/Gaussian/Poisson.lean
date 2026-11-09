/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside Analysis/Fourier/PoissonSummation)

public import CslibFrontier.Foundations.Analysis.Lattice.Poisson
public import CslibFrontier.Foundations.Probability.Gaussian.Fourier
public import CslibFrontier.Foundations.Probability.Gaussian.Periodization

/-!
# Poisson summation for shifted lattice Gaussian mass

## Main results

* `ZLattice.gaussianMass_eq_tsum_dual`: the shifted Gaussian mass equals its convergent
  dual-lattice Fourier series, with width and covolume factors explicit.

## References

The Gaussian Fourier identity and Poisson formula appear immediately before and in
[Regev2009], Lemma 2.14, printed page 18 of the May 2, 2009 author version. This theorem
uses canonical volume, the covolume form of Poisson summation, positive width, and an
arbitrary center. It proves all convergence hypotheses and includes dimension zero.
Dimension-uniform mass comparisons, smoothing, sampling and the quantum reduction are
separate results.
-/

public section

noncomputable section

open Module MeasureTheory ProbabilityTheory Asymptotics Filter
open scoped FourierTransform RealInnerProductSpace Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Poisson summation for the Gaussian mass at any center and positive width. The negative
phase comes from evaluating the periodization at `-c`. -/
theorem gaussianMass_eq_tsum_dual (s : ℝ) (hs : 0 < s) (c : E) :
    (gaussianMass L s c : ℂ) = (s : ℂ) ^ finrank ℝ E / (covolume L : ℂ) *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
        (gaussianWeight (1 / s) (w : E) : ℂ) * (Real.fourierChar (-⟪c, (w : E)⟫) : ℂ) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := discreteTopology_dualSubmodule L
  let f : C(E, ℂ) := ⟨fun x ↦ (gaussianWeight s x : ℂ),
    Complex.continuous_ofReal.comp (continuous_gaussianWeight s)⟩
  have hd : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-((finrank ℤ L : ℝ) + 1))) := by
    simpa only [f, ContinuousMap.coe_mk, Asymptotics.isBigO_iff, Complex.norm_real] using
      isBigO_gaussianWeight_cocompact (E := E) s hs (-((finrank ℤ L : ℝ) + 1))
  have h := tsum_eq_tsum_fourier_of_rpow_decay L f
    (r := (finrank ℤ L : ℝ) + 1) (by linarith) hd
    (integrable_gaussianWeight s hs) (summable_fourier_gaussianWeight D s hs) (-c)
  simp only [f, ContinuousMap.coe_mk, neg_add_eq_sub, inner_neg_left,
    fourier_gaussianWeight s hs] at h
  change (↑(∑' z : L, gaussianWeight s ((z : E) - c)) : ℂ) = _
  rw [Complex.ofReal_tsum, h]
  simp only [mul_assoc, tsum_mul_left]
  ring

end ZLattice
