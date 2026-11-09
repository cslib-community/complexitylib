/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Additivity and the union bound for discrete outer measures

The outer measure of a discrete distribution is additive on disjoint events: every set is
Carathéodory-measurable for it (`PMF.toOuterMeasure_caratheodory`). For arbitrary events it is
subadditive; since every probability is finite, the union bound also holds for the real-valued
probabilities `(p.toOuterMeasure s).toReal`.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_union_of_disjoint`: additivity on two disjoint events.
* `Cslib.Probability.PMF.toOuterMeasure_biUnion_finset`: additivity on finitely many pairwise
  disjoint events.
* `Cslib.Probability.PMF.sum_toOuterMeasure_le_one`: the probabilities of finitely many pairwise
  disjoint events add up to at most `1`.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le`: the union bound for
  real-valued probabilities of finitely many events.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- The probability of a union of two disjoint events is the sum of their probabilities. -/
theorem toOuterMeasure_union_of_disjoint (p : PMF α) {s t : Set α} (h : Disjoint s t) :
    p.toOuterMeasure (s ∪ t) = p.toOuterMeasure s + p.toOuterMeasure t := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  exact tsum_congr fun y => congrFun (Set.indicator_union_of_disjoint h (⇑p)) y

/-- The probability of a union of finitely many pairwise disjoint events is the sum of their
probabilities. -/
theorem toOuterMeasure_biUnion_finset {ι : Type*} (p : PMF α) (J : Finset ι) {B : ι → Set α}
    (hB : (J : Set ι).PairwiseDisjoint B) :
    p.toOuterMeasure (⋃ j ∈ J, B j) = ∑ j ∈ J, p.toOuterMeasure (B j) := by
  simp only [PMF.toOuterMeasure_apply]
  rw [Finset.indicator_biUnion J B hB]
  exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- The probabilities of finitely many pairwise disjoint events add up to at most `1`. -/
theorem sum_toOuterMeasure_le_one {ι : Type*} (p : PMF α) (J : Finset ι) {B : ι → Set α}
    (hB : (J : Set ι).PairwiseDisjoint B) : ∑ j ∈ J, p.toOuterMeasure (B j) ≤ 1 := by
  rw [← toOuterMeasure_biUnion_finset p J hB]
  exact (p.toOuterMeasure.mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff p _).mpr (Set.subset_univ _))

/-- **Union bound** for real-valued probabilities: the probability of a union of finitely many
events is at most the sum of their probabilities. -/
theorem toOuterMeasure_toReal_biUnion_finset_le {ι : Type*} (p : PMF α) (J : Finset ι)
    (B : ι → Set α) :
    (p.toOuterMeasure (⋃ j ∈ J, B j)).toReal ≤ ∑ j ∈ J, (p.toOuterMeasure (B j)).toReal := by
  rw [← ENNReal.toReal_sum fun j _ => toOuterMeasure_ne_top p (B j)]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => toOuterMeasure_ne_top p (B j))
    (MeasureTheory.measure_biUnion_finset_le J B)

end Cslib.Probability.PMF
