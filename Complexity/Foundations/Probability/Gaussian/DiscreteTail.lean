/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, discrete Gaussian moments and tails)

public import Complexity.Foundations.Probability.Gaussian.Discrete

/-!
# Exponential moments and tails of discrete Gaussians

For widths `0 < s < t`, multiplying the Gaussian weight at width `s` by
`exp (π * (1 / s² - 1 / t²) * ‖x‖²)` gives the weight at width `t`. This proves an actual finite
exponential moment, and bounds the probability of leaving a ball by exponential decay times
the ratio of the two lattice normalizers.

## Main results

* `ZLattice.summable_discreteGaussian_mul_exp`: the real weighted exponential moment is summable.
* `ZLattice.tsum_toReal_discreteGaussian_mul_exp`: its exact value is a normalizer ratio.
* `ZLattice.discreteGaussian_norm_ge_le`: a tail estimate with that explicit ratio.

## References

These are original intermediate results in the conventions of [Regev2009], §2, equations (4),(6).
The intended consumer is the finite-radius truncation in Lemma 3.2's bootstrapping analysis
(printed p. 19 of the May 2, 2009 author version). The ratio is not bounded uniformly in lattice
dimension here. The centered mass-scaling and tail estimates of Lemmas 2.4–2.5 are proved in
`Gaussian.CenteredTail`, using the arbitrary-lattice Poisson theorem in `Gaussian.Poisson`.
The bootstrapping algorithm remains separate work. No sampling or resource bound follows
from this mathematical tail estimate alone.
-/

public section

noncomputable section

open ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Tilting by an exponential of squared norm changes the Gaussian width. -/
theorem gaussianWeight_mul_exp {E : Type*} [NormedAddCommGroup E] (s t : ℝ) (x : E) :
    gaussianWeight s x * Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖x‖ ^ 2) =
      gaussianWeight t x := by
  simp only [gaussianWeight, ← Real.exp_add]
  congr 1
  ring

end ProbabilityTheory

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The exponential norm-square moment is summable, not merely a formal infinite sum. -/
theorem summable_discreteGaussian_mul_exp (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s < t)
    (c : E) :
    Summable (fun z : L ↦ (discreteGaussian L s hs c z).toReal *
      Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖(z : E) - c‖ ^ 2)) := by
  simpa only [discreteGaussian_apply_toReal, div_mul_eq_mul_div, gaussianWeight_mul_exp] using
    (summable_gaussianWeight L t (hs.trans hst) c).div_const (gaussianMass L s c)

/-- The exponential norm-square moment equals the ratio of Gaussian normalizers. -/
theorem tsum_toReal_discreteGaussian_mul_exp (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s < t)
    (c : E) :
    (∑' z : L, (discreteGaussian L s hs c z).toReal *
      Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖(z : E) - c‖ ^ 2)) =
        gaussianMass L t c / gaussianMass L s c := by
  simp only [discreteGaussian_apply_toReal, div_mul_eq_mul_div, gaussianWeight_mul_exp]
  exact ((summable_gaussianWeight L t (hs.trans hst) c).hasSum.div_const
    (gaussianMass L s c)).tsum_eq

/-- The same finite exponential moment, in extended nonnegative probability units. -/
theorem tsum_discreteGaussian_mul_exp (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s < t)
    (c : E) :
    (∑' z : L, discreteGaussian L s hs c z *
      ENNReal.ofReal (Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖(z : E) - c‖ ^ 2))) =
        ENNReal.ofReal (gaussianMass L t c / gaussianMass L s c) := by
  calc
    _ = ∑' z : L, ENNReal.ofReal ((discreteGaussian L s hs c z).toReal *
        Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖(z : E) - c‖ ^ 2)) := by
      apply tsum_congr
      intro z
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    _ = ENNReal.ofReal (∑' z : L, (discreteGaussian L s hs c z).toReal *
        Real.exp (Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * ‖(z : E) - c‖ ^ 2)) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun z : L ↦ mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
        (summable_discreteGaussian_mul_exp L s hs t hst c)).symm
    _ = _ := by rw [tsum_toReal_discreteGaussian_mul_exp L s hs t hst c]

/-- A discrete Gaussian tail is bounded by exponential decay times the actual normalizer ratio.
There is no assumed mass-scaling or smoothing estimate. -/
theorem discreteGaussian_norm_ge_le (s : ℝ) (hs : 0 < s) (t : ℝ) (hst : s < t)
    (c : E) (R : ℝ) (hR : 0 ≤ R) :
    (discreteGaussian L s hs c).toOuterMeasure {z : L | R ≤ ‖(z : E) - c‖} ≤
      ENNReal.ofReal (Real.exp (-Real.pi * (1 / s ^ 2 - 1 / t ^ 2) * R ^ 2) *
        (gaussianMass L t c / gaussianMass L s c)) := by
  classical
  let κ := Real.pi * (1 / s ^ 2 - 1 / t ^ 2)
  have hk : 0 ≤ κ := by
    apply mul_nonneg Real.pi_pos.le
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (sq_pos_of_pos hs)
    nlinarith [hs.trans hst]
  have hpoint (z : L) :
      {z : L | R ≤ ‖(z : E) - c‖}.indicator (discreteGaussian L s hs c) z ≤
        ENNReal.ofReal (Real.exp (-κ * R ^ 2)) *
          (discreteGaussian L s hs c z * ENNReal.ofReal (Real.exp (κ * ‖(z : E) - c‖ ^ 2))) := by
    by_cases hz : R ≤ ‖(z : E) - c‖
    · rw [Set.indicator_of_mem hz]
      have hsq : R ^ 2 ≤ ‖(z : E) - c‖ ^ 2 := by nlinarith [norm_nonneg ((z : E) - c)]
      have hexp : 1 ≤ Real.exp (-κ * R ^ 2) * Real.exp (κ * ‖(z : E) - c‖ ^ 2) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        have := mul_le_mul_of_nonneg_left hsq hk
        linarith
      have he := ENNReal.ofReal_le_ofReal hexp
      rw [ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.exp_pos _).le] at he
      calc
        _ = discreteGaussian L s hs c z * 1 := (mul_one _).symm
        _ ≤ discreteGaussian L s hs c z *
            (ENNReal.ofReal (Real.exp (-κ * R ^ 2)) *
              ENNReal.ofReal (Real.exp (κ * ‖(z : E) - c‖ ^ 2))) := by gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  calc
    _ = ∑' z : L, {z : L | R ≤ ‖(z : E) - c‖}.indicator
        (discreteGaussian L s hs c) z := PMF.toOuterMeasure_apply _ _
    _ ≤ ∑' z : L, ENNReal.ofReal (Real.exp (-κ * R ^ 2)) *
        (discreteGaussian L s hs c z * ENNReal.ofReal (Real.exp (κ * ‖(z : E) - c‖ ^ 2))) :=
      tsum_le_tsum hpoint
    _ = ENNReal.ofReal (Real.exp (-κ * R ^ 2)) *
        ENNReal.ofReal (gaussianMass L t c / gaussianMass L s c) := by
      rw [ENNReal.tsum_mul_left, tsum_discreteGaussian_mul_exp L s hs t hst c]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      dsimp [κ]
      congr 2
      ring

end ZLattice
