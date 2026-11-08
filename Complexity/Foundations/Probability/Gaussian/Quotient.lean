/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Gaussian distributions on lattice quotients)

public import Complexity.Foundations.Analysis.Lattice.QuotientMeasure
public import Complexity.Foundations.MeasureTheory.Group.QuotientDensity
public import Complexity.Foundations.Probability.Gaussian.Measure
public import Complexity.Foundations.Probability.Gaussian.Smoothing
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Continuous Gaussian distributions modulo a lattice

The ambient Gaussian and the normalized fundamental-domain quotient measure are actual
probability measures. Their density identity and distance bound use canonical quotient
measurability and the existing nonzero dual Gaussian mass.

## Main results

* `ZLattice.automorphize_gaussianWeight_coe`: the representative-to-center convention.
* `ZLattice.map_gaussianWeight_eq_withDensity`: the density of the actual Gaussian pushforward.
* `ZLattice.tvDist_gaussian_quotient_le`: its full-L1 error is at most the actual nonzero dual mass.
* `ZLattice.eventually_tvDist_gaussian_quotient_le`: every positive error is eventually achieved.

## References

The Gaussian is the normalized density of [Regev2009], equation (5), printed page 13 of the
May 2, 2009 author version. The source's statistical distance on that page is full L1, with
range `[0, 2]`, matching Mathlib's `tvDist`. The quotient statement is a precise consequence
of Claim 3.8 (page 22) and its informal motivation (page 17), not a uniform probability on
all of real space, a minimum smoothing parameter, a sampler, or the quantum reduction.
-/

public section

noncomputable section

open MeasureTheory Module ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E]

/-- At a quotient representative, Gaussian periodization is lattice mass at the opposite center. -/
theorem automorphize_gaussianWeight_coe (L : Submodule ℤ E) (s : ℝ) (x : E) :
    QuotientAddGroup.automorphize (gaussianWeight s)
      (QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup) = gaussianMass L s (-x) := by
  change (∑' z : L.toAddSubgroup.op, gaussianWeight s (z +ᵥ x)) = _
  rw [← L.toAddSubgroup.equivOp.tsum_eq (fun z ↦ gaussianWeight s (z +ᵥ x))]
  change (∑' z : L, gaussianWeight s (x + z)) = ∑' z : L, gaussianWeight s ((z : E) - -x)
  simp only [sub_neg_eq_add, add_comm x]

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local instance : Countable L.toAddSubgroup := inferInstanceAs (Countable L)

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
private theorem automorphize_gaussianWeight_div (s : ℝ) (hs : 0 < s)
    (y : E ⧸ L.toAddSubgroup) :
    QuotientAddGroup.automorphize
      (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E)) y =
    ENNReal.ofReal (QuotientAddGroup.automorphize (gaussianWeight s) y / s ^ finrank ℝ E) := by
  induction y using Quotient.inductionOn with | _ x
  rw [automorphize_gaussianWeight_coe L s x]
  change (∑' z : L.toAddSubgroup.op,
    ENNReal.ofReal (gaussianWeight s (z +ᵥ x) / s ^ finrank ℝ E)) = _
  rw [← L.toAddSubgroup.equivOp.tsum_eq
    (fun z ↦ ENNReal.ofReal (gaussianWeight s (z +ᵥ x) / s ^ finrank ℝ E))]
  change (∑' z : L, ENNReal.ofReal (gaussianWeight s (x + z) / s ^ finrank ℝ E)) = _
  have hsum : Summable (fun z : L ↦ gaussianWeight s (x + z)) := by
    simpa only [sub_neg_eq_add, add_comm x] using summable_gaussianWeight L s hs (-x)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun z ↦ div_nonneg (gaussianWeight_pos _ _).le (pow_pos hs _).le)
    (hsum.div_const _), tsum_div_const]
  congr 2
  simp only [gaussianMass, sub_neg_eq_add, add_comm x]

/-- Folding the actual normalized Gaussian gives the normalized lattice Gaussian density on
the quotient. Both normalizing factors use the same canonical ambient volume. -/
theorem map_gaussianWeight_eq_withDensity (s : ℝ) (hs : 0 < s) {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume) :
    Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
      (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))) =
    ((ENNReal.ofReal (covolume L))⁻¹ •
      Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (volume.restrict F)).withDensity
        (fun y ↦ ENNReal.ofReal (covolume L / s ^ finrank ℝ E *
          QuotientAddGroup.automorphize (gaussianWeight s) y)) := by
  have hc := covolume_pos L volume
  have hf : Measurable (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E)) :=
    ((continuous_gaussianWeight s).div_const _).measurable.ennreal_ofReal
  rw [QuotientAddGroup.map_withDensity_eq_withDensity_automorphize hF hf,
    withDensity_smul_measure, ← withDensity_smul' _ _
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne')]
  apply congrArg (fun f : E ⧸ L.toAddSubgroup → ℝ≥0∞ ↦
    (Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
      (volume.restrict F)).withDensity f)
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [automorphize_gaussianWeight_div L s hs y, ← ENNReal.ofReal_inv_of_pos hc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  congr 1
  field_simp

/-- The full-L1 distance of the actual Gaussian quotient distribution from normalized quotient
Haar measure is bounded by the actual nonzero reciprocal-width dual Gaussian mass. -/
theorem tvDist_gaussian_quotient_le (s : ℝ) (hs : 0 < s) {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume) :
    tvDist
      (Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
        (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
      ((ENNReal.ofReal (covolume L))⁻¹ •
        Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (volume.restrict F)) ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 := by
  let q : E → E ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  let ν := volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))
  let U := (ENNReal.ofReal (covolume L))⁻¹ • Measure.map q (volume.restrict F)
  let A : E ⧸ L.toAddSubgroup → ℝ := fun y ↦ covolume L / s ^ finrank ℝ E *
    QuotientAddGroup.automorphize (gaussianWeight s) y
  let f : E ⧸ L.toAddSubgroup → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (A y)
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussianWeight s hs
  have : IsProbabilityMeasure U := isProbabilityMeasure_normalized_quotient L volume hF
  have hmap : Measure.map q ν = U.withDensity f := map_gaussianWeight_eq_withDensity L s hs hF
  have : IsProbabilityMeasure (U.withDensity f) := by rw [← hmap]; infer_instance
  have hA : Measurable A := by
    apply QuotientAddGroup.measurable_from_quotient.mpr
    change Measurable (fun x : E ↦ covolume L / s ^ finrank ℝ E *
      QuotientAddGroup.automorphize (gaussianWeight s)
        (QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup))
    simp only [automorphize_gaussianWeight_coe]
    exact (continuous_const.mul
      ((continuous_gaussianMass L s hs).comp continuous_neg)).measurable
  have hf : Measurable f := hA.ennreal_ofReal
  have hlin : ∫⁻ y, f y ∂U = 1 := by
    simpa only [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := U.withDensity f))
  have hfi : Integrable f U := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [enorm_eq_self, hlin] using (show (1 : ℝ≥0∞) < ∞ by simp)
  have hbound (y : E ⧸ L.toAddSubgroup) : |1 - (f y).toReal| ≤
      gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 := by
    induction y using Quotient.inductionOn with | _ x
    have hpos : 0 ≤ A (QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup) := by
      dsimp only [A]
      rw [automorphize_gaussianWeight_coe]
      exact mul_nonneg (div_pos (covolume_pos L volume) (pow_pos hs _)).le
        (gaussianMass_pos L s hs (-x)).le
    rw [show (f (QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup)).toReal =
      A (QuotientAddGroup.mk x : E ⧸ L.toAddSubgroup) from ENNReal.toReal_ofReal hpos,
      abs_sub_comm]
    simpa only [A, automorphize_gaussianWeight_coe] using
      abs_gaussianMass_normalized_sub_one_le L s hs (-x)
  change tvDist (Measure.map q ν) U ≤ _
  rw [hmap, tvDist_withDensity_self_eq_integral hfi]
  calc
    _ ≤ ∫ _ : E ⧸ L.toAddSubgroup,
        gaussianMass (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) (1 / s) 0 - 1 ∂U := by
      apply integral_mono
      · exact ((integrable_const (1 : ℝ)).sub
          (integrable_toReal_of_lintegral_ne_top hf.aemeasurable (by rw [hlin]; simp))).abs
      · exact integrable_const _
      · exact hbound
    _ = _ := by simp

/-- Every positive full-L1 error is achieved by all sufficiently large positive Gaussian widths. -/
theorem eventually_tvDist_gaussian_quotient_le {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in Filter.atTop, 0 < s ∧
      tvDist
        (Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
          (volume.withDensity (fun x : E ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
        ((ENNReal.ofReal (covolume L))⁻¹ •
          Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (volume.restrict F)) ≤ ε := by
  filter_upwards [eventually_gaussianMass_dual_sub_one_le L ε hε] with s hs
  exact ⟨hs.1, (tvDist_gaussian_quotient_le L s hs.1 hF).trans hs.2⟩

end ZLattice
