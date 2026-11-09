/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.MeasureTheory.Group.ConvolutionDensity
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Singular, continuous and infinite-density clients for convolution with one density. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- A singular atom shifts the actual Gaussian density in the correct direction. -/
example (a : ℝ) :
    Measure.dirac a ∗ gaussianReal 0 1 =
      volume.withDensity (fun x ↦ gaussianPDF 0 1 (-a + x)) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    conv_withDensity_eq_withDensity_lintegral (measurable_gaussianPDF 0 1)]
  congr 1
  funext x
  simp

/-- With a continuous first input, the integral density gives the actual variance-two Gaussian. -/
example : volume.withDensity
    (fun x : ℝ ↦ ∫⁻ y, gaussianPDF 0 1 (-y + x) ∂gaussianReal 0 1) = gaussianReal 0 2 := by
  have h : gaussianReal 0 1 ∗ volume.withDensity (gaussianPDF 0 1) = gaussianReal 0 2 := by
    rw [← gaussianReal_of_var_ne_zero _ (by norm_num), gaussianReal_conv_gaussianReal]
    norm_num
  exact (conv_withDensity_eq_withDensity_lintegral
    (σ := gaussianReal 0 1) (measurable_gaussianPDF 0 1)).symm.trans h

/-- The theorem accepts an infinite density; it does not assume finite output mass. -/
example : Measure.dirac (0 : ℝ) ∗ volume.withDensity (fun _ : ℝ ↦ ∞) =
    (∞ : ℝ≥0∞) • volume := by
  rw [conv_withDensity_eq_withDensity_lintegral measurable_const]
  simp [withDensity_const]

/-- A zero first measure still gives zero, including when the density is infinite everywhere. -/
example : (0 : Measure ℝ) ∗ volume.withDensity (fun _ : ℝ ↦ ∞) = 0 := by
  rw [conv_withDensity_eq_withDensity_lintegral measurable_const]
  simp

private abbrev P := Equiv.Perm (Fin 3)
private instance : MeasurableSpace P := ⊤
private instance : MeasurableSingletonClass P := ⟨fun _ ↦ trivial⟩
private instance : MeasurableMul₂ P := ⟨by measurability⟩
private instance : MeasurableInv P := ⟨by measurability⟩

private def a : P := Equiv.swap 0 1
private def b : P := Equiv.swap 1 2

/-- Multiplication is not commutative in this concrete client. -/
example : a * b ≠ b * a := by decide

/-- The multiplicative density records left translation even in a noncommutative group. -/
example : Measure.dirac a ∗ₘ Measure.count.withDensity (fun x : P ↦ if x = b then 1 else 0) =
    Measure.count.withDensity (fun x : P ↦ if x = a * b then 1 else 0) := by
  rw [mconv_withDensity_eq_withDensity_lintegral (by measurability)]
  congr 1
  funext x
  simp [inv_mul_eq_iff_eq_mul]
