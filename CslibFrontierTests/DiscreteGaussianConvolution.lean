/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.Gaussian.Convolution
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Actual coset convolution at unequal widths on `2ℤ`, and dimension-zero exactness. -/

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace CslibFrontierTests.DiscreteGaussianConvolution

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


/-- The chosen coset is genuinely off the lattice. -/
example : (1 / 2 : ℝ) ∉ L := by
  intro h
  obtain ⟨k, hk⟩ := (twoBasis.mem_span_iff_repr_mem ℤ (1 / 2)).mp h ()
  have he : (k : ℝ) = 1 / 4 := by
    norm_num [twoBasis, Basis.repr_isUnitSMul, Units.smul_def] at hk
    exact hk
  have h0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have h1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
  omega

/-- Exact coset density: widths 3 and 4 give combined width 5 and harmonic width 12/5.
The output-dependent center is `(9/25)x - 1/2`, and the input center is `-1/2`. -/
example :
    Measure.conv
      ((ZLattice.discreteGaussian L 3 (by norm_num) (-(1 / 2))).toMeasure.map
        (fun z : L ↦ (z : ℝ) + 1 / 2))
      (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 4 x / 4))) =
    (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 5 x / 5))).withDensity
      (fun x ↦ ENNReal.ofReal
        ((5 / 6 * ZLattice.gaussianMass L (12 / 5) ((9 / 25 : ℝ) • x - 1 / 2)) /
          (2 / 3 * ZLattice.gaussianMass L 3 (-(1 / 2))))) := by
  convert ZLattice.conv_discreteGaussian_eq_withDensity L 3 4 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (1 / 2) using 1 <;>
    norm_num [finrank_self, covolume_two]

private theorem width_bound :
    (2 : ℝ) * Real.exp (-27 * Real.pi / 25) ≤ 1 / 8 := by
  have hpi : 4 * Real.log 2 < Real.pi := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have he := Real.exp_lt_exp.mpr
    (show -27 * Real.pi / 25 < -4 * Real.log 2 by linarith [Real.pi_pos])
  have hr : Real.exp (-4 * Real.log 2) = (1 / 16 : ℝ) := by
    rw [show -4 * Real.log 2 = -((4 : ℕ) * Real.log 2) by ring, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hr] at he
  linarith

/-- A fully discharged numerical full-L1 bound, rather than an assumed small dual mass. -/
example :
    tvDist
      (Measure.conv
        ((ZLattice.discreteGaussian L 3 (by norm_num) (-(1 / 2))).toMeasure.map
          (fun z : L ↦ (z : ℝ) + 1 / 2))
        (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 4 x / 4))))
      (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 5 x / 5))) ≤ 4 / 7 := by
  have h := ZLattice.tvDist_conv_discreteGaussian_le_of_gap L 3 4 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (1 / 2)
    (1 / 2) (by norm_num) dual_gap (1 / 7) (by norm_num) (by norm_num)
  have hnum : (2 : ℝ) ^ finrank ℝ ℝ *
      Real.exp (-3 * Real.pi * (3 * 4 / 5) ^ 2 * (1 / 2) ^ 2 / 4) ≤
        (1 / 7 : ℝ) / (1 + 1 / 7) := by
    convert width_bound using 1 <;> norm_num; ring
  simpa only [finrank_self, pow_one, show (4 : ℝ) * (1 / 7) = 4 / 7 by ring] using h hnum

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


/-- The actual two measures coincide in dimension zero, at all positive widths. -/
example (r s t : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (ht2 : t ^ 2 = r ^ 2 + s ^ 2) (u : Point) :
    Measure.conv
      ((ZLattice.discreteGaussian pointLattice r hr (-u)).toMeasure.map
        (fun z : pointLattice ↦ (z : Point) + u))
      (volume.withDensity
        (fun x : Point ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ Point))) =
    volume.withDensity
      (fun x : Point ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ Point)) := by
  have h := ZLattice.tvDist_conv_discreteGaussian_le pointLattice r s t hr hs ht ht2 u
  rw [point_dual_mass (1 / (r * s / t)) (one_div_pos.mpr (div_pos (mul_pos hr hs) ht)),
    point_dual_mass (1 / r) (one_div_pos.mpr hr), add_zero, zero_div] at h
  have : IsProbabilityMeasure
      (volume.withDensity
        (fun x : Point ↦ ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ Point))) :=
    isProbabilityMeasure_gaussianWeight s hs
  have : IsProbabilityMeasure
      (volume.withDensity
        (fun x : Point ↦ ENNReal.ofReal (gaussianWeight t x / t ^ finrank ℝ Point))) :=
    isProbabilityMeasure_gaussianWeight t ht
  exact tvDist_eq_zero_iff.mp (le_antisymm h tvDist_nonneg)

end CslibFrontierTests.DiscreteGaussianConvolution
