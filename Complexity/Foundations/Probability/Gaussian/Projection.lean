/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.Gaussian.Convolution
public import Complexity.Foundations.Probability.Gaussian.Standard
public import Complexity.Foundations.MeasureTheory.Measure.TotalVariation.Map
public import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Projecting a coset discrete Gaussian with scalar Gaussian noise

## Main results

* `ZLattice.tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le`: the actual scalar
  experiment is within `4ε` of its predicted centered Gaussian law.
* `ZLattice.tvDist_conv_map_inner_discreteGaussian_le_of_gap`: a sufficient width criterion.
* `ZLattice.tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_dual_mass_le`: the
  corresponding bound for pushforwards to `UnitAddCircle` under the dual-mass premise.
* `ZLattice.tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_gap`: the corresponding
  bound for actual pushforwards to `UnitAddCircle` under the gap criterion.

## References

[Regev2009], Corollary 3.10, printed page 23 of the May 2, 2009 author version. Statistical
distance uses the full-L1 convention of printed page 13. The coset input is sampled by the
actual discrete Gaussian at center `-u`, followed by translation by `u`. The smoothing
hypothesis is expressed as the actual nonzero dual Gaussian mass, with a quantitative
sufficient gap criterion. No minimum smoothing parameter, efficient sampler, finite-precision
implementation or quantum reduction is claimed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The source's scalar Gaussian experiment, with the actual nonzero dual mass premise.
At `z = 0` the convolution simplifies directly to the scalar noise law without any smoothing
hypothesis, whereas this unified bound still takes `hdual`. -/
theorem tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le
    (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (u z : E)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
      (Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2)) 0 - 1 ≤ ε) :
    tvDist
      (Measure.conv
        (((discreteGaussian L r hr (-u)).toMeasure.map (fun v : L ↦ (v : E) + u)).map
          (fun x ↦ ⟪z, x⟫))
        (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal)))
      (gaussianReal 0 ((((r * ‖z‖) ^ 2 + α ^ 2) / (2 * Real.pi)).toNNReal)) ≤
      4 * ε := by
  by_cases hz : z = 0
  · subst z
    simpa using (show (0 : ℝ) ≤ 4 * ε by positivity)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let s := α / ‖z‖
  let t := Real.sqrt (r ^ 2 + s ^ 2)
  have hs : 0 < s := div_pos hα hn
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = r ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hsn : s * ‖z‖ = α := div_mul_cancel₀ _ hn.ne'
  have hh : r * s / t = 1 / Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2) := by
    have hden : 0 < 1 / r ^ 2 + (‖z‖ / α) ^ 2 := by positivity
    apply (sq_eq_sq₀ (div_pos (mul_pos hr hs) ht).le
      (one_div_pos.mpr (Real.sqrt_pos.mpr hden)).le).mp
    rw [div_pow, div_pow, ht2, Real.sq_sqrt hden.le]
    dsimp only [s]
    field_simp
    ring
  let μ := (discreteGaussian L r hr (-u)).toMeasure.map (fun v : L ↦ (v : E) + u)
  let ν (w : ℝ) := volume.withDensity
    (fun x : E ↦ ENNReal.ofReal (gaussianWeight w x / w ^ finrank ℝ E))
  have : IsProbabilityMeasure (ν s) := isProbabilityMeasure_gaussianWeight s hs
  have : IsProbabilityMeasure (ν t) := isProbabilityMeasure_gaussianWeight t ht
  have hbound := tvDist_conv_discreteGaussian_le_of_dual_mass_le L r s t hr hs ht ht2 u
    ε hε hεhalf (by simpa only [hh, one_div_one_div] using hdual)
  have hmap := tvDist_map_le (Measure.conv μ (ν s)) (ν t)
    (f := innerSL ℝ z) (by fun_prop)
  rw [Measure.map_conv_continuousLinearMap] at hmap
  have hi : (innerSL ℝ z : E → ℝ) = (fun x ↦ ⟪z, x⟫) := by
    ext x
    simp only [innerSL_apply_apply]
  simp_rw [hi] at hmap
  have hinput : (ν s).map (fun x ↦ ⟪z, x⟫) =
      gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal) := by
    simpa only [ν, hsn] using gaussianWeight_withDensity_map_inner s hs z
  have hvar : (t * ‖z‖) ^ 2 = (r * ‖z‖) ^ 2 + α ^ 2 := by
    rw [mul_pow, ht2, add_mul, ← mul_pow, ← mul_pow, hsn]
  have houtput : (ν t).map (fun x ↦ ⟪z, x⟫) =
      gaussianReal 0 ((((r * ‖z‖) ^ 2 + α ^ 2) / (2 * Real.pi)).toNNReal) := by
    simpa only [ν, hvar] using gaussianWeight_withDensity_map_inner t ht z
  rw [hinput, houtput] at hmap
  exact hmap.trans hbound

/-- The explicit dual-gap criterion discharges the scalar experiment's small-dual-mass premise. -/
theorem tvDist_conv_map_inner_discreteGaussian_le_of_gap
    (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (u z : E)
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
      w ≠ 0 → a ≤ ‖(w : E)‖)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hnum : 2 ^ finrank ℝ E * Real.exp
      (-3 * Real.pi * (1 / Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2)) ^ 2 * a ^ 2 / 4) ≤
      ε / (1 + ε)) :
    tvDist
      (Measure.conv
        (((discreteGaussian L r hr (-u)).toMeasure.map (fun v : L ↦ (v : E) + u)).map
          (fun x ↦ ⟪z, x⟫))
        (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal)))
      (gaussianReal 0 ((((r * ‖z‖) ^ 2 + α ^ 2) / (2 * Real.pi)).toNNReal)) ≤
      4 * ε := by
  apply tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le L r α hr hα u z
    ε hε.le hεhalf
  have hh : 0 < 1 / Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2) := by positivity
  simpa only [one_div_one_div] using gaussianMass_dual_sub_one_le_of_gap L
    (1 / Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2)) hh a ha hgap ε hε hnum

/-- The same full-L1 bound holds for the actual canonical pushforwards to `UnitAddCircle`.
The target is a mapped Gaussian probability measure, without a periodic-density-series premise. -/
theorem tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_dual_mass_le
    (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (u z : E)
    (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2)
    (hdual : gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L)
      (Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2)) 0 - 1 ≤ ε) :
    tvDist
      ((Measure.conv
        (((discreteGaussian L r hr (-u)).toMeasure.map (fun v : L ↦ (v : E) + u)).map
          (fun x ↦ ⟪z, x⟫))
        (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal))).map
          (fun x : ℝ ↦ (x : UnitAddCircle)))
      ((gaussianReal 0 ((((r * ‖z‖) ^ 2 + α ^ 2) / (2 * Real.pi)).toNNReal)).map
        (fun x : ℝ ↦ (x : UnitAddCircle))) ≤ 4 * ε :=
  (tvDist_map_le _ _ (by fun_prop)).trans
    (tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le L r α hr hα u z ε hε hεhalf hdual)

/-- A discharged quantitative gap criterion also gives the actual mod-one experiment bound. -/
theorem tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_gap
    (r α : ℝ) (hr : 0 < r) (hα : 0 < α) (u z : E)
    (a : ℝ) (ha : 0 < a)
    (hgap : ∀ w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
      w ≠ 0 → a ≤ ‖(w : E)‖)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hnum : 2 ^ finrank ℝ E * Real.exp
      (-3 * Real.pi * (1 / Real.sqrt (1 / r ^ 2 + (‖z‖ / α) ^ 2)) ^ 2 * a ^ 2 / 4) ≤
      ε / (1 + ε)) :
    tvDist
      ((Measure.conv
        (((discreteGaussian L r hr (-u)).toMeasure.map (fun v : L ↦ (v : E) + u)).map
          (fun x ↦ ⟪z, x⟫))
        (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal))).map
          (fun x : ℝ ↦ (x : UnitAddCircle)))
      ((gaussianReal 0 ((((r * ‖z‖) ^ 2 + α ^ 2) / (2 * Real.pi)).toNNReal)).map
        (fun x : ℝ ↦ (x : UnitAddCircle))) ≤ 4 * ε :=
  (tvDist_map_le _ _ (by fun_prop)).trans
    (tvDist_conv_map_inner_discreteGaussian_le_of_gap L r α hr hα u z a ha hgap ε hε hεhalf hnum)

end ZLattice
