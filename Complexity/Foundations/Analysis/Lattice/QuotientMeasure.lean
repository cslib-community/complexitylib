/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, normalized lattice quotient measures)

public import Complexity.Init
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Normalization of lattice quotient measures

The reference measure is the canonical quotient pushforward of Haar measure restricted to
an actual fundamental domain, divided by the positive covolume. No new measure is defined.
The opposite subgroup action agrees with Mathlib's canonical quotient conventions.

## Main results

* `ZLattice.isProbabilityMeasure_normalized_quotient`: the normalized measure is a probability.
* `ZLattice.normalized_quotient_eq`: the measure does not depend on the fundamental domain.
* `ZLattice.isAddLeftInvariant_normalized_quotient`: the normalized measure is
  translation invariant.

## References

These are consequences of Mathlib's fundamental-domain and quotient Haar measure APIs.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

local instance : Countable L.toAddSubgroup := inferInstanceAs (Countable L)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
    [DiscreteTopology L] [IsZLattice ℝ L] [μ.IsAddHaarMeasure] in
private theorem fundamentalDomain_of_op {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F μ) : IsAddFundamentalDomain L F μ := by
  let e : L.toAddSubgroup.op ≃ L := (AddSubgroup.equivOp L.toAddSubgroup).symm
  have h := hF.preimage_of_equiv (QuasiMeasurePreserving.id μ) e.bijective (fun g x ↦ ?_)
  · convert! h using 1
  · change ((e g : L) : E) + x = x + AddOpposite.unop (g : Eᵃᵒᵖ)
    exact add_comm _ _

/-- A fundamental domain has finite ambient measure equal to the positive real covolume. -/
theorem measure_fundamentalDomain_op {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F μ) :
    μ F = ENNReal.ofReal (covolume L μ) := by
  have h := fundamentalDomain_of_op L μ hF
  have : VAddInvariantMeasure L E μ :=
    inferInstanceAs (VAddInvariantMeasure L.toAddSubgroup E μ)
  have hfin : μ F ≠ ∞ := by
    rw [← h.covolume_eq_volume μ,
      (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ).covolume_eq_volume μ]
    exact (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _)).ne
  rw [covolume_eq_measure_fundamentalDomain L μ h, measureReal_def, ENNReal.ofReal_toReal hfin]

/-- Dividing the actual quotient measure by the lattice covolume gives a probability measure. -/
theorem isProbabilityMeasure_normalized_quotient {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F μ) :
    IsProbabilityMeasure ((ENNReal.ofReal (covolume L μ))⁻¹ •
      Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (μ.restrict F)) := by
  constructor
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_apply_univ, smul_eq_mul]
  rw [measure_fundamentalDomain_op L μ hF,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (covolume_pos L μ)).ne' ENNReal.ofReal_ne_top]

/-- The normalized quotient measure is independent of the chosen fundamental domain. -/
theorem normalized_quotient_eq {F G : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F μ)
    (hG : IsAddFundamentalDomain L.toAddSubgroup.op G μ) :
    (ENNReal.ofReal (covolume L μ))⁻¹ •
      Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (μ.restrict F) =
    (ENNReal.ofReal (covolume L μ))⁻¹ •
      Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (μ.restrict G) := by
  congr 1
  exact hF.addQuotientMeasure_eq μ hG

/-- The probability reference measure on the quotient is translation invariant. -/
theorem isAddLeftInvariant_normalized_quotient {F : Set E}
    (hF : IsAddFundamentalDomain L.toAddSubgroup.op F μ) :
    Measure.IsAddLeftInvariant ((ENNReal.ofReal (covolume L μ))⁻¹ •
      Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (μ.restrict F)) := by
  let ν := Measure.map (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) (μ.restrict F)
  have : HasAddFundamentalDomain L.toAddSubgroup.op E μ := ⟨F, hF⟩
  have : AddQuotientMeasureEqMeasurePreimage μ ν :=
    hF.addQuotientMeasureEqMeasurePreimage_addQuotientMeasure
  have : ν.IsAddLeftInvariant :=
    AddQuotientMeasureEqMeasurePreimage.addInvariantMeasure_quotient μ
  infer_instance

end ZLattice
