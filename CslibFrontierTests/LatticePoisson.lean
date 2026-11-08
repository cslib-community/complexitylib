/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.Gaussian.Poisson

/-! Nonunit covolume, nonorthogonal basis, phase-sign, and zero-dimensional regressions. -/

open MeasureTheory Module ProbabilityTheory
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace ComplexityTests.LatticePoisson

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def shear : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![2 * x 0 + x 1 / 2, x 1]
  invFun x := ![(x 0 - x 1 / 2) / 2, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> dsimp; ring
  map_add' x y := by ext i; fin_cases i <;> dsimp; ring
  map_smul' c x := by ext i; fin_cases i <;> dsimp; ring

private def skewBasis : Basis (Fin 2) ℝ Plane :=
  ((Pi.basisFun ℝ (Fin 2)).map shear).map
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearEquiv

private abbrev skewLattice : Submodule ℤ Plane := Submodule.span ℤ (Set.range skewBasis)

private def skewBasisInt : Basis (Fin 2) ℤ skewLattice := skewBasis.restrictScalars ℤ

example : DiscreteTopology skewLattice := inferInstance

example : IsZLattice ℝ skewLattice := inferInstance

example : skewBasis 0 = WithLp.toLp 2 ![2, 0] := by
  ext i; fin_cases i <;> simp [skewBasis, shear]

example : skewBasis 1 = WithLp.toLp 2 ![1 / 2, 1] := by
  ext i; fin_cases i <;> simp [skewBasis, shear]

private theorem covolume_skew : ZLattice.covolume skewLattice = 2 := by
  rw [ZLattice.covolume_eq_det_mul_measureReal skewLattice volume skewBasisInt
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)]
  have hv : volume.real (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)) = 1 := by
    rw [measureReal_def, OrthonormalBasis.volume_parallelepiped, ENNReal.toReal_one]
  change |_| * volume.real (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)) = 2
  rw [hv]
  norm_num [skewBasisInt, skewBasis, shear, Basis.det_apply, Matrix.det_fin_two,
    Function.comp_def, Basis.toMatrix_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis_repr]

private def frequency : Plane := WithLp.toLp 2 ![1 / 2, -1 / 4]
private def center : Plane := WithLp.toLp 2 ![1 / 2, 0]

private theorem frequency_mem :
    frequency ∈ LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    fin_cases i
    · exact ⟨1, by norm_num [frequency, skewBasis, shear, PiLp.inner_apply, Fin.sum_univ_two]⟩
    · exact ⟨0, by norm_num [frequency, skewBasis, shear, PiLp.inner_apply, Fin.sum_univ_two]⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x hx hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

private theorem pairing : ⟪center, frequency⟫ = (1 / 4 : ℝ) := by
  norm_num [center, frequency, PiLp.inner_apply, Fin.sum_univ_two]

example : (Real.fourierChar ⟪center, frequency⟫ : ℂ) = Complex.I := by
  rw [pairing, Real.fourierChar_apply]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

example : (Real.fourierChar (-⟪center, frequency⟫) : ℂ) = -Complex.I := by
  rw [pairing, Real.fourierChar_apply]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

example (g : Plane → ℂ) :
    (∫ u : Fin 2 → ℝ, g ((skewBasisInt.ofZLatticeBasis ℝ).equivFun.symm u)) =
      (1 / 2 : ℝ) • ∫ x, g x := by
  simpa [covolume_skew] using ZLattice.integral_comp_basis skewBasisInt g

namespace Line

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ => (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L := Submodule.span ℤ (Set.range twoBasis)

private def b : Basis Unit ℤ L := twoBasis.restrictScalars ℤ

example : DiscreteTopology L := inferInstance

example : IsZLattice ℝ L := inferInstance

private theorem covolume_two : ZLattice.covolume L = 2 := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b (Basis.singleton Unit ℝ)]
  have hs : ZSpan.fundamentalDomain (Basis.singleton Unit ℝ) = Set.Ico (0 : ℝ) 1 := by
    ext x
    simp [ZSpan.fundamentalDomain, Basis.singleton_repr]
  rw [hs]
  norm_num [b, twoBasis, Basis.det_apply, Matrix.det_unique, Function.comp_def]

example (g : ℝ → ℝ) :
    (∫ u : Unit → ℝ, g ((b.ofZLatticeBasis ℝ).equivFun.symm u)) =
      (1 / 2 : ℝ) * ∫ x, g x := by
  simpa [covolume_two] using ZLattice.integral_comp_basis b g

example (g : ℝ → ℂ) (s : Set ℝ) :
    (∫ u in (b.ofZLatticeBasis ℝ).equivFun '' s, g ((b.ofZLatticeBasis ℝ).equivFun.symm u)) =
      (1 / 2 : ℝ) • ∫ x in s, g x := by
  simpa [covolume_two] using ZLattice.setIntegral_comp_basis b g s

example (u : Unit → ℝ) : (b.ofZLatticeBasis ℝ).equivFun.symm u = 2 * u () := by
  have hb : (b.ofZLatticeBasis ℝ) () = (2 : ℝ) := by
    rw [Basis.ofZLatticeBasis_apply]
    change ((twoBasis.restrictScalars ℤ) () : ℝ) = 2
    rw [Basis.restrictScalars_apply]
    change ((Basis.singleton Unit ℝ).isUnitSMul _) () = 2
    rw [Basis.isUnitSMul_apply]
    simp
  simp [Basis.equivFun_symm_apply, hb, mul_comm]

end Line

example (s : ℝ) (hs : 0 < s) (w : EuclideanSpace ℝ (Fin 0)) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin 0) => (gaussianWeight s x : ℂ)) w = 1 := by
  rw [fourier_gaussianWeight s hs]
  have hw : w = 0 := Subsingleton.elim _ _
  simp [hw, gaussianWeight]

example : 𝓕 (fun x : ℝ => (gaussianWeight 2 x : ℂ)) 0 = 2 := by
  rw [fourier_gaussianWeight 2 (by norm_num)]
  simp [gaussianWeight]

example : Integrable (fun x : EuclideanSpace ℝ (Fin 0) => (gaussianWeight 2 x : ℂ)) :=
  integrable_gaussianWeight 2 (by norm_num)

example : Summable (fun w : (⊥ : Submodule ℤ ℝ) =>
    𝓕 (fun x : ℝ => (gaussianWeight 2 x : ℂ)) (w : ℝ)) :=
  ZLattice.summable_fourier_gaussianWeight ⊥ 2 (by norm_num)

example : 𝓕 (fun x : EuclideanSpace ℝ (Fin 2) => (gaussianWeight 2 x : ℂ)) 0 = 4 := by
  rw [fourier_gaussianWeight 2 (by norm_num)]
  norm_num [gaussianWeight]

example : 𝓕 (fun x : ℝ => (gaussianWeight 2 x : ℂ)) 1 =
    2 * (Real.exp (-4 * Real.pi) : ℂ) := by
  rw [fourier_gaussianWeight 2 (by norm_num)]
  norm_num [gaussianWeight]
  congr 2
  ring

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private def pointBasis : Basis (Fin 0) ℝ Point := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice : Submodule ℤ Point := Submodule.span ℤ (Set.range pointBasis)

example : DiscreteTopology pointLattice := inferInstance

example : IsZLattice ℝ pointLattice := inferInstance

private theorem covolume_point : ZLattice.covolume pointLattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain pointLattice volume
    (ZSpan.isAddFundamentalDomain pointBasis volume)]
  have hf : ZSpan.fundamentalDomain pointBasis = Set.univ := by
    ext x
    simp [ZSpan.fundamentalDomain]
  rw [hf, measureReal_def, volume_euclideanSpace_eq_dirac]
  simp

/-- The final Schwartz endpoint on a nonorthogonal lattice of covolume two. -/
example (f : SchwartzMap Plane ℂ) :
    (∑' z : skewLattice, f (center + z)) = (1 / 2 : ℂ) *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice,
        𝓕 (f : Plane → ℂ) w * (Real.fourierChar ⟪center, (w : Plane)⟫ : ℂ) := by
  simpa [covolume_skew] using f.tsum_eq_tsum_fourier_lattice skewLattice center

/-- Width two and covolume two give the nonunit prefactor `2 ^ 2 / 2 = 2`. -/
example : (ZLattice.gaussianMass skewLattice 2 center : ℂ) = 2 *
    ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ Plane) skewLattice,
      (gaussianWeight (1 / 2) (w : Plane) : ℂ) *
        (Real.fourierChar (-⟪center, (w : Plane)⟫) : ℂ) := by
  have h := ZLattice.gaussianMass_eq_tsum_dual skewLattice 2 (by norm_num) center
  norm_num [covolume_skew] at h
  exact h

/-- Zero-dimensional Poisson summation needs neither a positive rank nor a nonempty index type. -/
example (f : SchwartzMap Point ℂ) :
    (∑' z : pointLattice, f z) =
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice,
        𝓕 (f : Point → ℂ) w := by
  simpa [covolume_point] using f.tsum_eq_tsum_fourier_lattice pointLattice 0

/-- The final Gaussian endpoint evaluates to mass one in dimension zero at every positive width. -/
example (s : ℝ) (hs : 0 < s) : (ZLattice.gaussianMass pointLattice s 0 : ℂ) = 1 := by
  have h := ZLattice.gaussianMass_eq_tsum_dual pointLattice s hs 0
  have ht : (∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointLattice,
      (gaussianWeight (1 / s) (w : Point) : ℂ) *
        (Real.fourierChar (-⟪(0 : Point), (w : Point)⟫) : ℂ)) = 1 := by
    rw [tsum_eq_single 0]
    · simp [gaussianWeight]
    · intro w hw
      exact False.elim (hw (Subsingleton.elim _ _))
  rw [ht] at h
  simpa [covolume_point] using h

end ComplexityTests.LatticePoisson
