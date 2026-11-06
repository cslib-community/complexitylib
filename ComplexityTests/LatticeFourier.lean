/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.Lattice.Fourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Arbitrary-domain, Schwartz, and Gaussian clients, including a sheared lattice. -/

open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace ComplexityTests.LatticeFourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

example {L : Submodule ℤ E} [Countable L] {s : Set E}
    (hs : IsAddFundamentalDomain L s volume) (f : SchwartzMap E ℂ)
    {w : E} (hw : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    (∫ x in s, (Real.fourierChar (-⟪x, w⟫) : ℂ) * ∑' z : L, f (x + z)) =
      𝓕 (f : E → ℂ) w :=
  ZLattice.integral_fourierChar_tsum_translate hs f.integrable hw

/-- The actual Gaussian coefficient, without assuming any Poisson formula. -/
private theorem gaussianCoefficient {L : Submodule ℤ E} [Countable L] {s : Set E}
    (hs : IsAddFundamentalDomain L s volume) {b : ℂ} (hb : 0 < b.re)
    {w : E} (hw : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    (∫ x in s, (Real.fourierChar (-⟪x, w⟫) : ℂ) *
      ∑' z : L, Complex.exp (-b * ‖x + z‖ ^ 2)) =
      (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / b) := by
  have hf : Integrable (fun x : E => Complex.exp (-b * ‖x‖ ^ 2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : E)
  rw [ZLattice.integral_fourierChar_tsum_translate hs hf hw]
  exact fourier_gaussian_innerProductSpace hb w

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Same shear as the normal-convergence client, transported to the Euclidean norm.
private def shear : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 0 + x 1 / 2, x 1]
  invFun x := ![x 0 - x 1 / 2, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_div, add_assoc, add_left_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp [mul_add, mul_div_assoc]

private def skewBasis : Basis (Fin 2) ℝ Plane :=
  ((Pi.basisFun ℝ (Fin 2)).map shear).map
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearEquiv

private abbrev skewLattice : Submodule ℤ Plane := Submodule.span ℤ (Set.range skewBasis)

example : skewBasis 0 = WithLp.toLp 2 ![1, 0] := by
  ext i; fin_cases i <;> simp [skewBasis, shear]

example : skewBasis 1 = WithLp.toLp 2 ![1 / 2, 1] := by
  ext i; fin_cases i <;> simp [skewBasis, shear]

private def dualFrequency : Plane := WithLp.toLp 2 ![2, 0]

private theorem dualFrequency_mem :
    dualFrequency ∈ LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    fin_cases i
    · exact ⟨2, by norm_num [dualFrequency, skewBasis, shear, PiLp.inner_apply, Fin.sum_univ_two]⟩
    · exact ⟨1, by norm_num [dualFrequency, skewBasis, shear, PiLp.inner_apply, Fin.sum_univ_two]⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x hx hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

/-- The ordinary first coordinate frequency is not dual to the sheared lattice. -/
example : WithLp.toLp 2 ![1, 0] ∉
    LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice := by
  intro hw
  have h := ZLattice.fourierChar_inner_eq_one hw
    (⟨skewBasis 1, Submodule.subset_span ⟨1, rfl⟩⟩ : skewLattice)
  have hi : ⟪skewBasis 1, WithLp.toLp 2 ![1, 0]⟫ = (1 / 2 : ℝ) := by
    norm_num [skewBasis, shear, PiLp.inner_apply, Fin.sum_univ_two]
  change Real.fourierChar ⟪skewBasis 1, WithLp.toLp 2 ![1, 0]⟫ = 1 at h
  rw [hi, Real.fourierChar_apply', show 2 * Real.pi * (1 / 2) = Real.pi by ring] at h
  exact Circle.exp_pi_ne_one h

/-- A nonzero dual frequency for a genuinely sheared lattice, with arbitrary integrable input. -/
example (f : Plane → ℂ) (hf : Integrable f) :
    (∫ x in ZSpan.fundamentalDomain skewBasis,
      (Real.fourierChar (-⟪x, dualFrequency⟫) : ℂ) * ∑' z : skewLattice, f (x + z)) =
      𝓕 f dualFrequency :=
  ZLattice.integral_fourierChar_tsum_translate
    (ZSpan.isAddFundamentalDomain skewBasis volume) hf dualFrequency_mem

/-- The sheared lattice Gaussian has an explicitly evaluated nonzero-frequency coefficient. -/
example :
    (∫ x in ZSpan.fundamentalDomain skewBasis,
      (Real.fourierChar (-⟪x, dualFrequency⟫) : ℂ) *
        ∑' z : skewLattice, Complex.exp (-(Real.pi : ℂ) * ‖x + z‖ ^ 2)) =
      Complex.exp (-4 * Real.pi) := by
  have h := gaussianCoefficient (ZSpan.isAddFundamentalDomain skewBasis volume)
    (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) dualFrequency_mem
  convert h using 1
  norm_num [dualFrequency, ← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Real.pi_ne_zero]
  congr 1
  field_simp
  norm_cast

/-- At zero frequency, the periodized integral recovers total mass. -/
example (f : Plane → ℂ) (hf : Integrable f) :
    (∫ x in ZSpan.fundamentalDomain skewBasis, ∑' z : skewLattice, f (x + z)) =
      ∫ x, f x := by
  simpa [Real.fourier_eq] using ZLattice.integral_fourierChar_tsum_translate
    (ZSpan.isAddFundamentalDomain skewBasis volume) hf
    (show (0 : Plane) ∈ LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice from
      Submodule.zero_mem _)

end ComplexityTests.LatticeFourier
