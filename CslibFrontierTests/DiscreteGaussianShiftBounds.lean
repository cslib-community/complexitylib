/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.MeasureTheory.Group.FundamentalDomain
import CslibFrontier.Foundations.Probability.Gaussian.Quotient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform mass at an off-lattice center of `2ℤ`, a genuine dual gap, and dimension zero. -/

open Module ProbabilityTheory MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace ComplexityTests.DiscreteGaussianShiftBounds

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ => (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L := Submodule.span ℤ (Set.range twoBasis)
private abbrev D := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L

private instance : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule L
private instance : IsZLattice ℝ D := ZLattice.isZLattice_dualSubmodule L

private theorem covolume_two : ZLattice.covolume L = 2 := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume (twoBasis.restrictScalars ℤ)
    (Basis.singleton Unit ℝ)]
  have hs : ZSpan.fundamentalDomain (Basis.singleton Unit ℝ) = Set.Ico (0 : ℝ) 1 := by
    ext x
    simp [ZSpan.fundamentalDomain, Basis.singleton_repr]
  rw [hs]
  norm_num [twoBasis, Basis.det_apply, Matrix.det_unique, Function.comp_def]

private theorem dual_gap (w : D) (hw : w ≠ 0) : (1 / 2 : ℝ) ≤ ‖(w : ℝ)‖ := by
  have hm := w.property (twoBasis ()) (Submodule.subset_span (Set.mem_range_self ()))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp hm
  have hk' : (k : ℝ) = (w : ℝ) * 2 := by
    simpa [twoBasis, Basis.isUnitSMul_apply, real_inner_comm, mul_comm] using hk
  have hkn : k ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    change (w : ℝ) = 0
    rw [h, Int.cast_zero] at hk'
    linarith
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hkn)
  rw [hk', abs_mul] at ha
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
  rw [Real.norm_eq_abs]
  linarith

/-- The dual gap is attained by a genuine nonzero frequency. -/
example : (1 / 2 : ℝ) ∈ D := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    exact ⟨1, by norm_num [twoBasis, Basis.isUnitSMul_apply]⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x hx hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

example : (1 : ℝ) ∉ L := by
  intro h
  obtain ⟨k, hk⟩ := (twoBasis.mem_span_iff_repr_mem ℤ 1).mp h ()
  have he : (k : ℝ) = 1 / 2 := by simpa [twoBasis, Basis.repr_isUnitSMul, Units.smul_def] using hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- The actual nonzero dual sum controls the off-lattice center; covolume and width cancel. -/
example : |ZLattice.gaussianMass L 2 1 - 1| ≤ ZLattice.gaussianMass D (1 / 2) 0 - 1 := by
  simpa [covolume_two] using ZLattice.abs_gaussianMass_normalized_sub_one_le L 2 (by norm_num) 1

example (s : ℝ) (hs : 0 < s) :
    ZLattice.gaussianMass D s 0 - 1 =
      ∑' w : ↥{w : D | w ≠ 0}, gaussianWeight s (w : ℝ) :=
  ZLattice.gaussianMass_zero_sub_one_eq_tsum D s hs

/-- A concrete sufficient-width inequality, with no assumed mass bound. -/
private theorem width_two_bound : (2 : ℝ) * Real.exp (-3 * Real.pi / 4) ≤ 1 / 3 := by
  have hpi : 4 * Real.log 2 < Real.pi := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have he := Real.exp_lt_exp.mpr (show -3 * Real.pi / 4 < -3 * Real.log 2 by linarith)
  have hr : Real.exp (-3 * Real.log 2) = (1 / 8 : ℝ) := by
    rw [show -3 * Real.log 2 = -((3 : ℕ) * Real.log 2) by ring, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hr] at he
  linarith

private theorem dual_small : ZLattice.gaussianMass D (1 / 2) 0 - 1 ≤ 1 / 2 := by
  apply ZLattice.gaussianMass_dual_sub_one_le_of_gap L 2 (by norm_num)
    (1 / 2) (by norm_num) dual_gap (1 / 2) (by norm_num)
  have he : -3 * Real.pi * (2 : ℝ) ^ 2 * (1 / 2) ^ 2 / 4 = -3 * Real.pi / 4 := by ring
  simpa only [finrank_self, pow_one, he,
    show (1 / 2 : ℝ) / (1 + 1 / 2) = 1 / 3 by norm_num] using width_two_bound

/-- The sufficient width criterion yields the actual off-center mass interval. -/
example : ZLattice.gaussianMass L 2 1 ∈ Set.Icc (1 / 2) (3 / 2) := by
  have h := ZLattice.gaussianMass_mem_Icc_of_dual_mass_le L 2 (by norm_num) (1 / 2) dual_small 1
  norm_num [covolume_two] at h ⊢
  exact h

example : |ZLattice.gaussianMass L 2 1 - 1| ≤ 1 / 2 := by
  have h := ZLattice.abs_gaussianMass_normalized_sub_one_le L 2 (by norm_num) 1
  simpa [covolume_two] using h.trans dual_small

/-- Every positive error is achievable uniformly over all centers of an arbitrary lattice. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℤ E) [DiscreteTopology M] [IsZLattice ℝ M] (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in Filter.atTop, 0 < s ∧ ∀ c : E,
      |ZLattice.covolume M / s ^ finrank ℝ E * ZLattice.gaussianMass M s c - 1| ≤ ε := by
  filter_upwards [ZLattice.eventually_gaussianMass_dual_sub_one_le M ε hε] with s hs
  exact ⟨hs.1, fun c ↦
    (ZLattice.abs_gaussianMass_normalized_sub_one_le M s hs.1 c).trans hs.2⟩

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointBasis := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice := Submodule.span ℤ (Set.range pointBasis)
private abbrev pointDual := LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice

private instance : DiscreteTopology pointDual :=
  ZLattice.discreteTopology_dualSubmodule pointLattice

private theorem point_dual_mass (s : ℝ) (hs : 0 < s) :
    ZLattice.gaussianMass pointDual s 0 - 1 = 0 := by
  rw [ZLattice.gaussianMass_zero_sub_one_eq_tsum pointDual s hs]
  have : IsEmpty ↥{w : pointDual | w ≠ 0} := ⟨fun w ↦ w.property (Subsingleton.elim _ _)⟩
  exact tsum_empty

/-- The uniform mass theorem gives exact normalized mass at every center in dimension zero. -/
example (s : ℝ) (hs : 0 < s) (c : Point) :
    ZLattice.covolume pointLattice / s ^ finrank ℝ Point *
      ZLattice.gaussianMass pointLattice s c = 1 := by
  have h := ZLattice.abs_gaussianMass_normalized_sub_one_le pointLattice s hs c
  rw [point_dual_mass (1 / s) (one_div_pos.mpr hs)] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- The same actual basis domains work with the canonical quotient's opposite action. -/
private theorem basis_domain_op {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Finite ι]
    (b : Basis ι ℝ E) :
    IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup.op
      (ZSpan.fundamentalDomain b) volume :=
  isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' b volume)

private abbrev lineDomain := ZSpan.fundamentalDomain twoBasis
private abbrev lineQuotient := ℝ ⧸ L.toAddSubgroup
private abbrev lineGaussian (s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianWeight s x / s))
private abbrev lineUniform : Measure lineQuotient :=
  (1 / 2 : ℝ≥0∞) • Measure.map QuotientAddGroup.mk (volume.restrict lineDomain)

/-- These are actual probability measures, before any real-valued distance is evaluated. -/
example (s : ℝ) (hs : 0 < s) : IsProbabilityMeasure (lineGaussian s) := by
  simpa using isProbabilityMeasure_gaussianWeight (E := ℝ) s hs

example : IsProbabilityMeasure lineUniform := by
  simpa [covolume_two, lineGaussian, lineUniform, lineDomain] using
    ZLattice.isProbabilityMeasure_normalized_quotient L volume (basis_domain_op twoBasis)

example : Measure.IsAddLeftInvariant lineUniform := by
  simpa [covolume_two, lineGaussian, lineUniform, lineDomain] using
    ZLattice.isAddLeftInvariant_normalized_quotient L volume (basis_domain_op twoBasis)

/-- Width and covolume both equal two, so the actual quotient density has coefficient one. -/
example : Measure.map (QuotientAddGroup.mk : ℝ → lineQuotient) (lineGaussian 2) =
    lineUniform.withDensity
      (fun y ↦ ENNReal.ofReal (QuotientAddGroup.automorphize (gaussianWeight 2) y)) := by
  simpa [covolume_two, lineGaussian, lineUniform, lineDomain] using
    ZLattice.map_gaussianWeight_eq_withDensity L 2 (by norm_num) (basis_domain_op twoBasis)

/-- This is the value of the density at an off-lattice representative, not a point probability. -/
example : QuotientAddGroup.automorphize (gaussianWeight 2)
    (QuotientAddGroup.mk (1 : ℝ) : lineQuotient) ∈ Set.Icc (1 / 2) (3 / 2) := by
  rw [ZLattice.automorphize_gaussianWeight_coe]
  have h := ZLattice.gaussianMass_mem_Icc_of_dual_mass_le L 2 (by norm_num)
    (1 / 2) dual_small (-1)
  norm_num [covolume_two] at h ⊢
  exact h

/-- A numerical width criterion gives a distance bound for the actual pushed-forward Gaussian. -/
example : tvDist (Measure.map (QuotientAddGroup.mk : ℝ → lineQuotient) (lineGaussian 2))
    lineUniform ≤ 1 / 2 := by
  have h := (ZLattice.tvDist_gaussian_quotient_le L 2 (by norm_num)
    (basis_domain_op twoBasis)).trans dual_small
  simpa [covolume_two, lineGaussian, lineUniform, lineDomain] using h

example (ε : ℝ) (hε : 0 < ε) : ∀ᶠ s : ℝ in Filter.atTop, 0 < s ∧
    tvDist (Measure.map (QuotientAddGroup.mk : ℝ → lineQuotient) (lineGaussian s))
      lineUniform ≤ ε := by
  simpa [covolume_two, lineGaussian, lineUniform, lineDomain] using
    ZLattice.eventually_tvDist_gaussian_quotient_le L (basis_domain_op twoBasis) ε hε

private abbrev pointQuotient := Point ⧸ pointLattice.toAddSubgroup
private abbrev pointGaussian (s : ℝ) : Measure Point :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ Point))
private abbrev pointUniform : Measure pointQuotient :=
  (ENNReal.ofReal (ZLattice.covolume pointLattice))⁻¹ •
    Measure.map QuotientAddGroup.mk (volume.restrict (ZSpan.fundamentalDomain pointBasis))

example (s : ℝ) (hs : 0 < s) : IsProbabilityMeasure (pointGaussian s) :=
  isProbabilityMeasure_gaussianWeight s hs

example : IsProbabilityMeasure pointUniform :=
  ZLattice.isProbabilityMeasure_normalized_quotient pointLattice volume (basis_domain_op pointBasis)

/-- The dimension-zero endpoint gives exactly zero distance, with positive width arbitrary. -/
private theorem point_tv_zero (s : ℝ) (hs : 0 < s) :
    tvDist (Measure.map (QuotientAddGroup.mk : Point → pointQuotient) (pointGaussian s))
      pointUniform = 0 := by
  apply le_antisymm _ tvDist_nonneg
  have h := ZLattice.tvDist_gaussian_quotient_le pointLattice s hs (basis_domain_op pointBasis)
  rwa [point_dual_mass (1 / s) (one_div_pos.mpr hs)] at h

/-- Actual probability normalization makes the zero distance an equality of measures. -/
example (s : ℝ) (hs : 0 < s) :
    Measure.map (QuotientAddGroup.mk : Point → pointQuotient) (pointGaussian s) =
      pointUniform := by
  have : IsProbabilityMeasure (pointGaussian s) := isProbabilityMeasure_gaussianWeight s hs
  have : IsProbabilityMeasure pointUniform :=
    ZLattice.isProbabilityMeasure_normalized_quotient pointLattice volume
      (basis_domain_op pointBasis)
  exact tvDist_eq_zero_iff.mp (point_tv_zero s hs)

/-- A fundamental domain for the opposite subgroup action has ambient measure equal to the
covolume. -/
example : volume lineDomain = 2 := by
  simpa [covolume_two] using
    ZLattice.measure_eq_ofReal_covolume_of_op L volume (basis_domain_op twoBasis)

/-- The reference probability does not depend on which actual fundamental domain is used. -/
example {F : Set ℝ} (hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume) :
    lineUniform = (1 / 2 : ℝ≥0∞) •
      Measure.map (QuotientAddGroup.mk : ℝ → lineQuotient) (volume.restrict F) := by
  simpa [covolume_two, lineUniform, lineDomain] using
    ZLattice.normalized_quotient_eq L volume (basis_domain_op twoBasis) hF

/-- Every positive target error admits an actual width on any full-rank lattice. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℤ E) [DiscreteTopology M] [IsZLattice ℝ M] {F : Set E}
    (hF : IsAddFundamentalDomain M.toAddSubgroup.op F volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧
      tvDist
        (Measure.map (QuotientAddGroup.mk : E → E ⧸ M.toAddSubgroup)
          (volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ E))))
        ((ENNReal.ofReal (ZLattice.covolume M))⁻¹ •
          Measure.map (QuotientAddGroup.mk : E → E ⧸ M.toAddSubgroup) (volume.restrict F)) ≤ ε :=
  (ZLattice.eventually_tvDist_gaussian_quotient_le M hF ε hε).exists

end ComplexityTests.DiscreteGaussianShiftBounds
