/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Folding densities onto a subgroup quotient

The quotient carries its canonical quotient measurable space. Countable sums of measurable
translates give measurable automorphized densities, including densities with infinite values.

## Main results

* `QuotientAddGroup.measurable_automorphize`: measurability of an ENNReal-valued orbit sum.
* `QuotientAddGroup.map_withDensity_eq_withDensity_automorphize`: folding a density onto the
  quotient using an actual fundamental domain.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace QuotientAddGroup

variable {G : Type*} [AddGroup G] [MeasurableSpace G] {Γ : AddSubgroup G}
  [Countable Γ] [MeasurableConstVAdd Γ.op G]

/-- A measurable nonnegative density has a measurable orbit sum on the canonical measurable
quotient. No convergence or finiteness assumption is needed. -/
theorem measurable_automorphize {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (automorphize (Γ := Γ) f) := by
  apply measurable_from_quotient.mpr
  exact Measurable.tsum fun γ : Γ.op => hf.comp (measurable_const_vadd γ)

/-- Pushing a density onto the quotient folds its translates into the existing automorphized
density. The reference measure is the image of the ambient measure restricted to a fundamental
domain. The ambient measure need only be invariant under right translations by the subgroup;
the density may have infinite mass or infinite values. -/
theorem map_withDensity_eq_withDensity_automorphize {μ : Measure G}
    [VAddInvariantMeasure Γ.op G μ] {F : Set G}
    (hF : IsAddFundamentalDomain Γ.op F μ) {f : G → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map (mk : G → G ⧸ Γ) =
      ((μ.restrict F).map (mk : G → G ⧸ Γ)).withDensity (automorphize f) := by
  ext s hs
  have hq : Measurable (mk : G → G ⧸ Γ) := measurable_coe
  have hpre := hs.preimage hq
  rw [Measure.map_apply hq hs, withDensity_apply _ hpre,
    withDensity_apply _ hs,
    setLIntegral_map hs (measurable_automorphize hf) hq,
    ← lintegral_indicator hpre, ← lintegral_indicator hpre,
    hF.lintegral_eq_tsum'']
  trans ∫⁻ x in F, ∑' γ : Γ.op, (mk ⁻¹' s).indicator f (γ +ᵥ x) ∂μ
  · exact (lintegral_tsum fun γ : Γ.op =>
      ((hf.indicator hpre).comp (measurable_const_vadd γ)).aemeasurable).symm
  apply lintegral_congr
  intro x
  have hcoset (γ : Γ.op) : (mk (γ +ᵥ x) : G ⧸ Γ) = mk x :=
    mk_add_of_mem x γ.property
  by_cases hx : x ∈ (mk : G → G ⧸ Γ) ⁻¹' s
  · rw [Set.indicator_of_mem hx]
    change ∑' γ : Γ.op, _ = ∑' γ : Γ.op, f (γ +ᵥ x)
    apply tsum_congr
    intro γ
    exact Set.indicator_of_mem (by simpa only [Set.mem_preimage, hcoset] using hx) _
  · rw [Set.indicator_of_notMem hx]
    calc
      ∑' γ : Γ.op, (mk ⁻¹' s).indicator f (γ +ᵥ x) = ∑' _ : Γ.op, (0 : ℝ≥0∞) :=
        tsum_congr fun γ => Set.indicator_of_notMem
          (by simpa only [Set.mem_preimage, hcoset] using hx) _
      _ = 0 := tsum_zero

end QuotientAddGroup
