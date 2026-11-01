/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Natural-Number Sum and Filter-Cardinality Bounds for `PMF.uniformOfFintype`

This module converts natural-number sum bounds `(∑ a : α, f a) ≤ C * Fintype.card α` and
filter-cardinality bounds `B * #{a : α | P a} ≤ A * Fintype.card α` over a nonempty finite type `α`
into `ℝ≥0∞` expectation and outer-measure bounds under `PMF.uniformOfFintype α`.

## Main results

* `Cslib.Probability.PMF.tsum_uniformOfFintype_le_of_sum_le`: converts
  `(∑ a : α, f a) ≤ C * Fintype.card α` into
  `(∑' a : α, PMF.uniformOfFintype α a * (f a : ℝ≥0∞)) ≤ (C : ℝ≥0∞)`.
* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div`: converts
  `B * (Finset.univ.filter P).card ≤ A * Fintype.card α` into
  `(PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞)`.
-/

public section

namespace Cslib.Probability.PMF

open scoped BigOperators ENNReal

/-- Convert a natural-number sum bound `(∑ a : α, f a) ≤ C * Fintype.card α` over a nonempty finite
type `α` into an `ℝ≥0∞` expectation bound under `PMF.uniformOfFintype α`. -/
theorem tsum_uniformOfFintype_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℕ} {C : ℕ} (hle : (∑ a : α, f a) ≤ C * Fintype.card α) :
    (∑' a : α, PMF.uniformOfFintype α a * (f a : ℝ≥0∞)) ≤ (C : ℝ≥0∞) := by
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum, ← Nat.cast_sum]
  have hne_zero : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcast : ((∑ a : α, f a : ℕ) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞) := by
    exact_mod_cast hle
  calc
    (Fintype.card α : ℝ≥0∞)⁻¹ * ((∑ a : α, f a : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * ((C : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)) := by gcongr
    _ = (C : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card α : ℝ≥0∞)) := by ring
    _ = (C : ℝ≥0∞) := by rw [ENNReal.inv_mul_cancel hne_zero hne_top, mul_one]

/-- Convert a natural-number filter-cardinality bound
`B * (Finset.univ.filter P).card ≤ A * Fintype.card α` into an `ℝ≥0∞` outer-measure bound
`(PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞)`. -/
theorem toOuterMeasure_uniformOfFintype_le_div {α : Type*} [Fintype α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {A B : ℕ} (hB : 0 < B)
    (hle : B * (Finset.univ.filter P).card ≤ A * Fintype.card α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤ (A : ℝ≥0∞) / (B : ℝ≥0∞) := by
  have h1 := PMF.toOuterMeasure_uniformOfFintype (α := α) {a : α | P a}
  simp only [Set.mem_ofPred_eq] at h1
  rw [h1]
  have hcast :
      (B : ℝ≥0∞) * ((Finset.univ.filter P).card : ℝ≥0∞) ≤
        (A : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞) := by
    exact_mod_cast hle
  have hcard_ne_zero : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB_ne_zero : (B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hB_ne_top : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hB_ne_zero) (Or.inl hB_ne_top)]
  calc
    ((Finset.univ.filter P).card : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ * (B : ℝ≥0∞)
      = ((B : ℝ≥0∞) * ((Finset.univ.filter P).card : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by ring
    _ ≤ ((A : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)) * (Fintype.card α : ℝ≥0∞)⁻¹ := by gcongr
    _ = (A : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹) := by ring
    _ = (A : ℝ≥0∞) := by rw [ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top, mul_one]

end Cslib.Probability.PMF
