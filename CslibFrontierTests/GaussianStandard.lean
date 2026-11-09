/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Probability.Gaussian.Standard

/-! Checked clients of the actual normalized Gaussian density and projection laws. -/

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace

-- The standard width recovers the standard Gaussian itself.
example :
    volume.withDensity (fun x : EuclideanSpace ℝ (Fin 2) ↦ ENNReal.ofReal
      (gaussianWeight (Real.sqrt (2 * Real.pi)) x /
        Real.sqrt (2 * Real.pi) ^ finrank ℝ (EuclideanSpace ℝ (Fin 2)))) =
      stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
  rw [gaussianWeight_withDensity_eq_map_stdGaussian _ (Real.sqrt_pos.mpr (by positivity)),
    div_self (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne']
  simp

-- A nonunit width and a nonunit projection detect the 2π normalization.
example :
    (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (gaussianWeight 4 x / 4))).map
        (fun x ↦ 2 * x) = gaussianReal 0 ((32 / Real.pi).toNNReal) := by
  have h := gaussianWeight_withDensity_map_inner (E := ℝ) 4 (by norm_num) 2
  have hvar : ((4 : ℝ) * ‖(2 : ℝ)‖) ^ 2 / (2 * Real.pi) = 32 / Real.pi := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [finrank_self, pow_one, hvar] at h
  simpa only [Real.inner_apply, RCLike.conj_to_real, mul_comm] using h

-- The zero projection is a point mass, without a nonzero-vector premise.
example (s : ℝ) (hs : 0 < s) :
    (volume.withDensity (fun x : EuclideanSpace ℝ (Fin 2) ↦
        ENNReal.ofReal (gaussianWeight s x / s ^ 2))).map
        (fun x ↦ ⟪(0 : EuclideanSpace ℝ (Fin 2)), x⟫) = Measure.dirac 0 := by
  simpa using gaussianWeight_withDensity_map_inner (E := EuclideanSpace ℝ (Fin 2)) s hs 0

-- In dimension zero the full density measure, not just its projection, is a point mass.
example (s : ℝ) (hs : 0 < s) :
    volume.withDensity (fun x : EuclideanSpace ℝ (Fin 0) ↦
      ENNReal.ofReal (gaussianWeight s x / s ^ finrank ℝ (EuclideanSpace ℝ (Fin 0)))) =
      Measure.dirac 0 := by
  rw [gaussianWeight_withDensity_eq_map_stdGaussian s hs]
  have h : (fun x : EuclideanSpace ℝ (Fin 0) ↦ (s / Real.sqrt (2 * Real.pi)) • x) =
      (fun _ ↦ 0) := funext fun _ ↦ Subsingleton.elim _ _
  rw [h]
  simp
