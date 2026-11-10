/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product

/-!
# Coordinate events in finite products

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_pi_forall`: the probability that every coordinate lies in
  its own event is the product of the probabilities.
* `Cslib.Probability.PMF.toOuterMeasure_pi_exists_le`: a union bound for coordinate events.
-/

public section

namespace Cslib.Probability.PMF

/-- The probability that every coordinate of an independent tuple lies in its own event is the
product of the probabilities. -/
theorem toOuterMeasure_pi_forall {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) (E : ∀ i, Set (α i)) :
    (pi p).toOuterMeasure {u | ∀ i, u i ∈ E i} = ∏ i, (p i).toOuterMeasure (E i) := by
  classical
  have := fun i => Fintype.ofFinite (α i)
  simp only [PMF.toOuterMeasure_apply, tsum_fintype, Set.indicator_apply, Set.mem_ofPred_eq,
    pi_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : ∀ i, u i ∈ E i
  · rw [ite_eq_left hu]
    exact Finset.prod_congr rfl fun i _ => (ite_eq_left (hu i)).symm
  · rw [ite_eq_right hu]
    push Not at hu
    obtain ⟨i, hi⟩ := hu
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

/-- The probability that some coordinate lies in its bad event is at most the sum of the
coordinate probabilities. The marginal identities supply the exact coordinate laws. -/
theorem toOuterMeasure_pi_exists_le {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Finite (α i)] (p : ∀ i, PMF (α i)) (bad : ∀ i, Set (α i)) :
    (pi p).toOuterMeasure {x | ∃ i, x i ∈ bad i} ≤ ∑ i, (p i).toOuterMeasure (bad i) := by
  classical
  have hset : {x : ∀ i, α i | ∃ i, x i ∈ bad i} =
      ⋃ i, (fun x : ∀ i, α i => x i) ⁻¹' bad i := by ext; simp
  rw [hset]
  calc
    _ ≤ ∑ i, (pi p).toOuterMeasure ((fun x => x i) ⁻¹' bad i) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = _ := by
      congr 1 with i : 1
      rw [← PMF.toOuterMeasure_map_apply, pi_map_eval]

end Cslib.Probability.PMF
