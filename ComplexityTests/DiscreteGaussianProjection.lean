/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Foundations.Probability.Gaussian.Projection
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Actual scalar and mod-one coset Gaussian experiments, with a numerical dual-gap witness.
The `2ℤ` fixture and exponential estimate reuse the convention of DiscreteGaussianConvolution.
-/

public section

open Module ProbabilityTheory MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace ComplexityTests.DiscreteGaussianProjection

def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ => (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

abbrev L := Submodule.span ℤ (Set.range twoBasis)
private abbrev D := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L

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

private theorem harmonic_width :
    1 / Real.sqrt (1 / (3 : ℝ) ^ 2 + (‖(2 : ℝ)‖ / 8) ^ 2) = 12 / 5 := by
  have h : Real.sqrt (1 / (3 : ℝ) ^ 2 + (‖(2 : ℝ)‖ / 8) ^ 2) = 5 / 12 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    norm_num
  rw [h]
  norm_num

private theorem numerical_criterion :
    (2 : ℝ) ^ finrank ℝ ℝ * Real.exp
      (-3 * Real.pi * (1 / Real.sqrt (1 / (3 : ℝ) ^ 2 + (‖(2 : ℝ)‖ / 8) ^ 2)) ^ 2 *
        (1 / 2) ^ 2 / 4) ≤ (1 / 7 : ℝ) / (1 + 1 / 7) := by
  rw [harmonic_width]
  convert width_bound using 1 <;> norm_num; ring

abbrev cosetLaw :=
  (ZLattice.discreteGaussian L 3 (by norm_num) (-(1 / 2))).toMeasure.map
    (fun v : L ↦ (v : ℝ) + 1 / 2)

abbrev scalarLaw := Measure.conv (cosetLaw.map (fun x ↦ 2 * x))
  (gaussianReal 0 ((32 / Real.pi).toNNReal))

abbrev targetLaw := gaussianReal 0 ((50 / Real.pi).toNNReal)

-- The experiment and its Gaussian comparison are actual probabilities.
example : IsProbabilityMeasure scalarLaw := by infer_instance
example : IsProbabilityMeasure targetLaw := by infer_instance

-- Neither smoothing nor the small dual mass is assumed in this numerical bound.
theorem scalar_bound : tvDist scalarLaw targetLaw ≤ 4 / 7 := by
  have h := ZLattice.tvDist_conv_map_inner_discreteGaussian_le_of_gap L 3 8
    (by norm_num) (by norm_num) (1 / 2) 2 (1 / 2) (by norm_num) dual_gap
    (1 / 7) (by norm_num) (by norm_num) numerical_criterion
  have hnoise : (8 : ℝ) ^ 2 / (2 * Real.pi) = 32 / Real.pi := by ring
  have htarget : (((3 : ℝ) * ‖(2 : ℝ)‖) ^ 2 + 8 ^ 2) / (2 * Real.pi) =
      50 / Real.pi := by norm_num; ring
  rw [hnoise, htarget] at h
  simpa only [scalarLaw, targetLaw, cosetLaw, Real.inner_apply, mul_comm,
    show (4 : ℝ) * (1 / 7) = 4 / 7 by ring] using h

example : tvDist scalarLaw targetLaw ≤ 4 / 7 := scalar_bound

-- The mod-one measures are canonical pushforwards of the actual real laws.
example :
    tvDist (scalarLaw.map (fun x : ℝ ↦ (x : UnitAddCircle)))
      (targetLaw.map (fun x : ℝ ↦ (x : UnitAddCircle))) ≤ 4 / 7 := by
  have h := ZLattice.tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_gap L 3 8
    (by norm_num) (by norm_num) (1 / 2) 2 (1 / 2) (by norm_num) dual_gap
    (1 / 7) (by norm_num) (by norm_num) numerical_criterion
  have hnoise : (8 : ℝ) ^ 2 / (2 * Real.pi) = 32 / Real.pi := by ring
  have htarget : (((3 : ℝ) * ‖(2 : ℝ)‖) ^ 2 + 8 ^ 2) / (2 * Real.pi) =
      50 / Real.pi := by norm_num; ring
  rw [hnoise, htarget] at h
  simpa only [scalarLaw, targetLaw, cosetLaw, Real.inner_apply, mul_comm,
    show (4 : ℝ) * (1 / 7) = 4 / 7 by ring] using h

-- The zero projection is exact, with no smoothing or width criterion.
example (α : ℝ) :
    Measure.conv (cosetLaw.map (fun x : ℝ ↦ ⟪(0 : ℝ), x⟫))
      (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal)) =
      gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal) := by
  simp

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointBasis := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice := Submodule.span ℤ (Set.range pointBasis)

-- Every projection in dimension zero is exact, for arbitrary shift and scalar noise.
example (r α : ℝ) (hr : 0 < r) (u z : Point) :
    Measure.conv
      (((ZLattice.discreteGaussian pointLattice r hr (-u)).toMeasure.map
        (fun v : pointLattice ↦ (v : Point) + u)).map (fun x ↦ ⟪z, x⟫))
      (gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal)) =
      gaussianReal 0 ((α ^ 2 / (2 * Real.pi)).toNNReal) := by
  have hz : z = 0 := Subsingleton.elim _ _
  simp [hz]

end ComplexityTests.DiscreteGaussianProjection
