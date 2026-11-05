/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.Lattice.Dual
public import Complexity.Foundations.Analysis.Lattice.Covolume
public import Complexity.Foundations.Analysis.Lattice.Fourier
public import Complexity.Foundations.Analysis.Lattice.Schwartz
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Poisson summation on full-rank lattices

This module assembles actual continuous periodization, its Fourier coefficients, and
multivariate Fourier reconstruction with the lattice covolume normalization.

## Main results

* `ZLattice.tsum_eq_tsum_fourier_of_rpow_decay`: Poisson summation from polynomial decay,
  integrability, and summability of the actual Fourier samples on the dual lattice.
* `SchwartzMap.tsum_eq_tsum_fourier_lattice`: the full formula for Schwartz functions, with
  convergence proved on both lattices.

## References

This is an original assembly of Mathlib's Fourier reconstruction and lattice APIs, with
explicit sufficient analytic hypotheses. It uses the Fourier convention of [Regev2009],
printed page 18, and supplies the covolume form of the Poisson identity in Lemma 2.14.
Regev omits technical conditions there; they are stated explicitly here.
-/

public section

noncomputable section

open Module MeasureTheory TopologicalSpace Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace SchwartzMap Topology

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (b : Basis ι ℤ L)

omit [FiniteDimensional ℝ E] in
private theorem inner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor <;> intro x hx <;> exact inner_self_eq_zero.mp (hx x)

private def dualBasisReal : Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) inner_nondegenerate (b.ofZLatticeBasis ℝ)

private theorem dual_eq_span : LinearMap.BilinForm.dualSubmodule (innerₗ E) L =
    Submodule.span ℤ (Set.range (dualBasisReal L b)) := by
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E) inner_nondegenerate _

private def dualBasisInt : Basis ι ℤ (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :=
  ((dualBasisReal L b).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (dual_eq_span L b).symm)

private theorem dualBasisInt_coe (i : ι) :
    (dualBasisInt L b i : E) = dualBasisReal L b i := by
  simp [dualBasisInt]

private def dualIndex : (ι → ℤ) ≃ₗ[ℤ] (LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :=
  (dualBasisInt L b).equivFun.symm

private theorem inner_basis_dualIndex (n : ι → ℤ) (i : ι) :
    ⟪(b i : E), (dualIndex L b n : E)⟫ = n i := by
  rw [dualIndex, Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, inner_sum,
    ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, dualBasisInt_coe]
  have h (j : ι) : ⟪(b i : E), dualBasisReal L b j⟫ = if i = j then 1 else 0 := by
    simpa only [dualBasisReal, Basis.ofZLatticeBasis_apply, innerₗ_apply_apply] using
      (LinearMap.BilinForm.apply_dualBasis_right inner_nondegenerate ⟨fun x y ↦ real_inner_comm y x⟩
      (b.ofZLatticeBasis ℝ) i j)
  simp [h]

private theorem inner_dualIndex (n : ι → ℤ) (x : E) :
    ⟪x, (dualIndex L b n : E)⟫ = ∑ i, (b.ofZLatticeBasis ℝ).equivFun x i * n i := by
  conv_lhs => rw [← (b.ofZLatticeBasis ℝ).sum_repr x]
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, Basis.ofZLatticeBasis_apply,
    inner_basis_dualIndex, Basis.equivFun_apply]

omit [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [DiscreteTopology L] [IsZLattice ℝ L] in
private theorem quotient_basis_periodic (i : ι) :
    Function.Periodic (fun t : ℝ ↦ (Submodule.Quotient.mk (t • (b i : E)) : E ⧸ L)) 1 := by
  intro t
  dsimp only
  rw [add_smul, one_smul, Submodule.Quotient.mk_add]
  have h : (Submodule.Quotient.mk (b i : E) : E ⧸ L) = 0 :=
    (Submodule.Quotient.mk_eq_zero L).mpr (b i).property
  rw [h, add_zero]

private def torusToQuotient (x : UnitAddTorus ι) : E ⧸ L :=
  ∑ i, (quotient_basis_periodic L b i).lift (x i)

omit [DecidableEq ι] in
private theorem torusToQuotient_coe (x : ι → ℝ) :
    torusToQuotient L b (fun i ↦ (x i : UnitAddCircle)) =
      Submodule.Quotient.mk ((b.ofZLatticeBasis ℝ).equivFun.symm x) := by
  simp only [torusToQuotient, Function.Periodic.lift_coe, Basis.equivFun_symm_apply,
    Basis.ofZLatticeBasis_apply]
  exact (map_sum L.mkQ _ _).symm

omit [FiniteDimensional ℝ E] [DecidableEq ι] [DiscreteTopology L] [IsZLattice ℝ L] in
private theorem continuous_torusToQuotient : Continuous (torusToQuotient L b) := by
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun t : ℝ ↦ (Submodule.Quotient.mk (t • (b i : E)) : E ⧸ L)) := by
    exact continuous_quotient_mk'.comp (continuous_id.smul continuous_const)
  have hl : Continuous (quotient_basis_periodic L b i).lift := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact hc
  exact hl.comp (continuous_apply i)

private theorem mFourier_dualIndex (n : ι → ℤ) (x : E) :
    UnitAddTorus.mFourier n (fun i ↦ ((b.ofZLatticeBasis ℝ).equivFun x i : UnitAddCircle)) =
      (Real.fourierChar ⟪x, (dualIndex L b n : E)⟫ : ℂ) := by
  rw [inner_dualIndex, Real.fourierChar_apply]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_intCast,
    Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  push_cast
  ring

private def torusPeriodization (f : E → ℂ) (x : UnitAddTorus ι) : ℂ :=
  QuotientAddGroup.automorphize f (torusToQuotient L b x)

omit [DecidableEq ι] in
private theorem torusPeriodization_coe (f : E → ℂ) (x : ι → ℝ) :
    torusPeriodization L b f (fun i ↦ (x i : UnitAddCircle)) =
      ∑' z : L, f ((b.ofZLatticeBasis ℝ).equivFun.symm x + z) := by
  unfold torusPeriodization
  rw [torusToQuotient_coe]
  exact (L.toAddSubgroup.equivOp.tsum_eq
    (fun z ↦ f (z +ᵥ (b.ofZLatticeBasis ℝ).equivFun.symm x))).symm

omit [DecidableEq ι] [IsZLattice ℝ L] in
private theorem continuous_torusPeriodization (f : C(E, ℂ)) {r : ℝ}
    (hr : (finrank ℤ L : ℝ) < r)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-r))) :
    Continuous (torusPeriodization L b f) :=
  (continuous_automorphize L f hr hf).comp (continuous_torusToQuotient L b)

omit [Fintype ι] [DecidableEq ι] in
private theorem basis_image_fundamentalDomain [Finite ι] :
    (b.ofZLatticeBasis ℝ).equivFun '' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) =
      Set.pi Set.univ (fun _ : ι ↦ Set.Ico (0 : ℝ) 1) := by
  rw [LinearEquiv.image_eq_preimage_symm]
  ext x
  change (∀ i, (b.ofZLatticeBasis ℝ).repr ((b.ofZLatticeBasis ℝ).equivFun.symm x) i ∈
    Set.Ico 0 1) ↔ _
  simp only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Set.mem_pi,
    Set.mem_univ, forall_const]

variable [MeasurableSpace E] [BorelSpace E]

private theorem mFourierCoeff_torusPeriodization (f : E → ℂ) (hf : Integrable f) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization L b f) n =
      (covolume L)⁻¹ • 𝓕 f (dualIndex L b n) := by
  let B := (b.ofZLatticeBasis ℝ).equivFun.symm
  let g : E → ℂ := fun x ↦ (Real.fourierChar (-⟪x, (dualIndex L b n : E)⟫) : ℂ) *
    ∑' z : L, f (x + z)
  have hm (u : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (fun i ↦ (u i : UnitAddCircle)) =
        (Real.fourierChar (-⟪B u, (dualIndex L b n : E)⟫) : ℂ) := by
    simpa only [B, LinearEquiv.apply_symm_apply, map_neg, Submodule.coe_neg, inner_neg_right]
      using mFourier_dualIndex L b (-n) (B u)
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]
  simp only [Pi.zero_apply, zero_add, hm, torusPeriodization_coe, smul_eq_mul]
  change (∫ u in {u : ι → ℝ | ∀ i, u i ∈ Set.Ioc 0 1}, g (B u)) = _
  have hsets : {u : ι → ℝ | ∀ i, u i ∈ Set.Ioc 0 1} =ᵐ[volume]
      Set.pi Set.univ (fun _ : ι ↦ Set.Ico (0 : ℝ) 1) := by
    have heq : {u : ι → ℝ | ∀ i, u i ∈ Set.Ioc 0 1} =
        Set.pi Set.univ (fun _ : ι ↦ Set.Ioc (0 : ℝ) 1) := by ext; simp
    rw [heq]
    exact
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι ↦ (volume : Measure ℝ))
        (f := fun _ ↦ 0) (g := fun _ ↦ 1)).trans
        (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : ι ↦ (volume : Measure ℝ))).symm
  rw [setIntegral_congr_set hsets, ← basis_image_fundamentalDomain L b,
    setIntegral_comp_basis b g]
  congr 1
  exact integral_fourierChar_tsum_translate (isAddFundamentalDomain b volume) hf
    (dualIndex L b n).property

omit [Fintype ι] [DecidableEq ι] in
include b in
private theorem poisson_basis [Finite ι] (f : C(E, ℂ)) {r : ℝ}
    (hr : (finrank ℤ L : ℝ) < r)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-r))) (hi : Integrable f)
    (hF : Summable (fun w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L ↦ 𝓕 (f : E → ℂ) w))
    (x : E) :
    (∑' z : L, f (x + z)) = (covolume L : ℂ)⁻¹ *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
        𝓕 (f : E → ℂ) w * (Real.fourierChar ⟪x, (w : E)⟫ : ℂ) := by
  classical
  let := Fintype.ofFinite ι
  let P : C(UnitAddTorus ι, ℂ) :=
    ⟨torusPeriodization L b f, continuous_torusPeriodization L b f hr hf⟩
  have hcoeff (n : ι → ℤ) : UnitAddTorus.mFourierCoeff P n =
      (covolume L)⁻¹ • 𝓕 (f : E → ℂ) (dualIndex L b n) :=
    mFourierCoeff_torusPeriodization L b f hi n
  have hsum : Summable (UnitAddTorus.mFourierCoeff P) := by
    convert ((dualIndex L b).toEquiv.summable_iff.mpr hF).const_smul
      ((covolume L)⁻¹) using 1
    funext n
    exact hcoeff n
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := P) hsum
    (fun i ↦ ((b.ofZLatticeBasis ℝ).equivFun x i : UnitAddCircle))
  have hval : P (fun i ↦ ((b.ofZLatticeBasis ℝ).equivFun x i : UnitAddCircle)) =
      ∑' z : L, f (x + z) := by
    simpa only [P, ContinuousMap.coe_mk, LinearEquiv.symm_apply_apply] using
      torusPeriodization_coe L b f ((b.ofZLatticeBasis ℝ).equivFun x)
  rw [hval] at hseries
  rw [← hseries.tsum_eq]
  simp only [hcoeff, smul_eq_mul, mFourier_dualIndex, Complex.real_smul,
    Complex.ofReal_inv, mul_assoc]
  rw [tsum_mul_left]
  congr 1
  exact (dualIndex L b).toEquiv.tsum_eq
    (fun w ↦ 𝓕 (f : E → ℂ) w * (Real.fourierChar ⟪x, (w : E)⟫ : ℂ))

omit [Fintype ι] [DecidableEq ι] in
/-- Poisson summation for a continuous function with sufficient polynomial decay and summable
Fourier samples on the dual lattice. The hypotheses are analytic convergence conditions;
no Poisson or Fourier reconstruction identity is assumed. -/
theorem tsum_eq_tsum_fourier_of_rpow_decay (f : C(E, ℂ)) {r : ℝ}
    (hr : (finrank ℤ L : ℝ) < r)
    (hf : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-r))) (hi : Integrable f)
    (hF : Summable (fun w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L ↦ 𝓕 (f : E → ℂ) w))
    (x : E) :
    (∑' z : L, f (x + z)) = (covolume L : ℂ)⁻¹ *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
        𝓕 (f : E → ℂ) w * (Real.fourierChar ⟪x, (w : E)⟫ : ℂ) := by
  classical
  exact poisson_basis L (Module.Free.chooseBasis ℤ L) f hr hf hi hF x

end ZLattice

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Poisson summation for a Schwartz function on any full-rank discrete lattice.
Schwartz decay proves the needed summability on both the lattice and its actual dual. -/
theorem tsum_eq_tsum_fourier_lattice (f : 𝓢(E, ℂ)) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (x : E) :
    (∑' z : L, f (x + z)) = (ZLattice.covolume L : ℂ)⁻¹ *
      ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
        𝓕 (f : E → ℂ) w * (Real.fourierChar ⟪x, (w : E)⟫ : ℂ) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  have : DiscreteTopology D := ZLattice.discreteTopology_dualSubmodule L
  apply ZLattice.tsum_eq_tsum_fourier_of_rpow_decay L f.toContinuousMap
    (r := (finrank ℤ L : ℝ) + 1) (by linarith) (f.isBigO_cocompact_rpow _) f.integrable
  have hs := ZLattice.summable_translate D (𝓕 f).toContinuousMap
    (b := (finrank ℤ D : ℝ) + 1) (by linarith) ((𝓕 f).isBigO_cocompact_rpow _)
  change Summable (fun w : D ↦ 𝓕 (f : E → ℂ) w)
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, zero_add,
    SchwartzMap.toContinuousMap, BoundedContinuousFunction.coe_toContinuousMap,
    SchwartzMap.toBoundedContinuousFunction_apply, SchwartzMap.fourier_coe] using
    ContinuousMap.summable_apply hs (0 : E)

end SchwartzMap
