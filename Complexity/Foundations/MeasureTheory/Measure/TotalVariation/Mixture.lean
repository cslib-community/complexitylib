/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, full-L1 bounds for finite weighted mixtures)

public import Complexity.Init
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation of finite weighted mixtures

The existing full-L1 distance controls changes in both the component measures and their
nonnegative weights. The component measures are finite; neither probability normalization
nor equality of total masses is assumed.

## Main results

* `MeasureTheory.tvDist_finsetSum_le`: subadditivity for finite sums of measures.
* `MeasureTheory.tvDist_nnreal_smul`: exact common-weight scaling.
* `MeasureTheory.tvDist_nnreal_smul_same`: exact change of weight of one finite measure.
* `MeasureTheory.tvDist_finsetSum_smul_le`: simultaneous component and weight changes.

## References

These standard variation inequalities are derived from Mathlib's existing signed-measure
variation API. They define no new distance or mixture construction.
-/

public section

noncomputable section

namespace MeasureTheory

open scoped ENNReal NNReal

variable {X ι : Type*} [MeasurableSpace X]

private theorem etvDist_add_le (μ₁ μ₂ ν₁ ν₂ : Measure X)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    etvDist (μ₁ + μ₂) (ν₁ + ν₂) ≤ etvDist μ₁ ν₁ + etvDist μ₂ ν₂ := by
  simp only [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist,
    Measure.toSignedMeasure_add]
  have he : μ₁.toSignedMeasure + μ₂.toSignedMeasure -
      (ν₁.toSignedMeasure + ν₂.toSignedMeasure) =
        (μ₁.toSignedMeasure - ν₁.toSignedMeasure) +
          (μ₂.toSignedMeasure - ν₂.toSignedMeasure) := by abel
  rw [he]
  exact VectorMeasure.variation_add_le Set.univ

/-- A finite sum of finite measure differences has at most the sum of their full-L1 distances. -/
theorem tvDist_finsetSum_le (s : Finset ι) (μ ν : ι → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    tvDist (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, tvDist (μ i) (ν i) := by
  classical
  have he : etvDist (∑ i ∈ s, μ i) (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, etvDist (μ i) (ν i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (etvDist_add_le _ _ _ _).trans (add_le_add le_rfl ih)
  have hfinite : ∑ i ∈ s, etvDist (μ i) (ν i) ≠ ∞ := by simp
  simpa only [tvDist, ENNReal.toReal_sum (fun i _ ↦ etvDist_ne_top (μ i) (ν i))] using
    ENNReal.toReal_mono hfinite he

/-- Scaling both finite measures by the same finite nonnegative weight scales their distance. -/
theorem tvDist_nnreal_smul (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a : ℝ≥0) : tvDist (a • μ) (a • ν) = a * tvDist μ ν := by
  simp only [tvDist, etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist,
    Measure.toSignedMeasure_smul]
  rw [← smul_sub]
  change (((a : ℝ) • (μ.toSignedMeasure - ν.toSignedMeasure)).variation Set.univ).toReal = _
  rw [VectorMeasure.variation_smul]
  simp

/-- Changing only a finite measure's weight costs exactly the absolute weight difference times
its total mass. This includes unequal masses and the zero measure. -/
theorem tvDist_nnreal_smul_same (μ : Measure X) [IsFiniteMeasure μ] (a b : ℝ≥0) :
    tvDist (a • μ) (b • μ) = |(a : ℝ) - b| * μ.real Set.univ := by
  simp only [tvDist, etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist,
    Measure.toSignedMeasure_smul]
  change (((a : ℝ) • μ.toSignedMeasure - (b : ℝ) • μ.toSignedMeasure).variation
    Set.univ).toReal = _
  rw [← sub_smul (a : ℝ) (b : ℝ) μ.toSignedMeasure, VectorMeasure.variation_smul,
    Measure.variation_toSignedMeasure]
  simp [measureReal_def]

/-- A finite weighted mixture changes by at most its weighted component errors plus the weight
errors times the comparison components' actual total masses. -/
theorem tvDist_finsetSum_smul_le (s : Finset ι) (a b : ι → ℝ≥0) (μ ν : ι → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)] :
    tvDist (∑ i ∈ s, a i • μ i) (∑ i ∈ s, b i • ν i) ≤
      ∑ i ∈ s, ((a i : ℝ) * tvDist (μ i) (ν i) +
        |(a i : ℝ) - b i| * (ν i).real Set.univ) := by
  apply (tvDist_finsetSum_le s _ _).trans
  apply Finset.sum_le_sum
  intro i _
  calc
    tvDist (a i • μ i) (b i • ν i) ≤
        tvDist (a i • μ i) (a i • ν i) + tvDist (a i • ν i) (b i • ν i) :=
      tvDist_triangle _ _ _
    _ = _ := by rw [tvDist_nnreal_smul, tvDist_nnreal_smul_same]

end MeasureTheory
