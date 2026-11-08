/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, extending the ZLattice API)

public import Complexity.Init
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration in lattice basis coordinates

The inverse basis chart sends ordinary coordinate volume to ambient volume divided by
the lattice covolume. These integral forms reuse Mathlib's existing volume transformation
`ZLattice.volume_image_eq_volume_div_covolume'`. No orthogonality assumption is imposed.

The statements use the total Bochner integral, so they require no integrability premise.

## Main results

* `ZLattice.integral_comp_basis`: change coordinates in a whole-space integral.
* `ZLattice.setIntegral_comp_basis`: change coordinates in a set integral.

## References

These are integral forms of Mathlib's `ZLattice.volume_image_eq_volume_div_covolume'`.
-/

public section

open MeasureTheory Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

private theorem map_basis_symm :
    Measure.map (b.ofZLatticeBasis ℝ).equivFun.symm volume =
      (ENNReal.ofReal (covolume L))⁻¹ • volume := by
  let e := (b.ofZLatticeBasis ℝ).equivFun.symm.toContinuousLinearEquiv
  have he : Measurable (b.ofZLatticeBasis ℝ).equivFun.symm := e.continuous.measurable
  ext s hs
  rw [Measure.map_apply he hs, Measure.smul_apply, smul_eq_mul]
  rw [← LinearEquiv.image_eq_preimage_symm]
  rw [volume_image_eq_volume_div_covolume' L b hs.nullMeasurableSet, div_eq_mul_inv,
    mul_comm]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrating in lattice coordinates divides the ambient integral by the covolume. -/
theorem integral_comp_basis (g : E → F) :
    (∫ u : ι → ℝ, g ((b.ofZLatticeBasis ℝ).equivFun.symm u)) =
      (covolume L)⁻¹ • ∫ x, g x := by
  let e := (b.ofZLatticeBasis ℝ).equivFun.symm.toContinuousLinearEquiv
  change (∫ u, g (e.toHomeomorph.toMeasurableEquiv u)) = _
  rw [← integral_map_equiv e.toHomeomorph.toMeasurableEquiv g]
  change (∫ x, g x ∂Measure.map (b.ofZLatticeBasis ℝ).equivFun.symm volume) = _
  rw [map_basis_symm b, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (covolume_pos L).le]

/-- The same change of coordinates on any set. No measurability assumption on the set is needed. -/
theorem setIntegral_comp_basis (g : E → F) (s : Set E) :
    (∫ u in (b.ofZLatticeBasis ℝ).equivFun '' s,
      g ((b.ofZLatticeBasis ℝ).equivFun.symm u)) =
      (covolume L)⁻¹ • ∫ x in s, g x := by
  let e := (b.ofZLatticeBasis ℝ).equivFun.symm.toContinuousLinearEquiv
  rw [LinearEquiv.image_eq_preimage_symm]
  change (∫ u in e.toHomeomorph.toMeasurableEquiv ⁻¹' s,
    g (e.toHomeomorph.toMeasurableEquiv u)) = _
  rw [← setIntegral_map_equiv e.toHomeomorph.toMeasurableEquiv g s]
  change (∫ x in s, g x ∂Measure.map (b.ofZLatticeBasis ℝ).equivFun.symm volume) = _
  rw [map_basis_symm b, Measure.restrict_smul, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (covolume_pos L).le]

end ZLattice
