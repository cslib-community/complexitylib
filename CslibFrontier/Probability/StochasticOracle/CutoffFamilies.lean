/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchMinimum
import Mathlib.Tactic

/-!
# Cutoff families for two-batch selection

The cutoff-pair reduction in [Wang2027], Theorem 2(2), PDF p. 8.
There are at most `k * (k + 1)` threshold pairs. Every nonempty feasible first
batch belongs to one of their lower/upper inclusion families, and every nonempty
member of an enumerated family meets the original deadline. This reduction uses
actual maxima of the prescribed cutoffs, without rounding time or relaxing the deadline.

## Main results

* `cutoff_family_feasible`: soundness of a cutoff family.
* `cutoff_families_cover`: every feasible nonempty first batch is represented.
* `cutoffPairs_card_le`: the number of enumerated families.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset
variable {ι K : Type} [Fintype ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (I : FullCoverInstance ι K)

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- A cutoff maximum is at most a threshold exactly when every cutoff is, and
zero is. Empty batches retain duration zero. -/
theorem FullCoverInstance.batchDuration_le_iff (A : Finset ι) (t : K) :
    I.batchDuration A ≤ t ↔ 0 ≤ t ∧ ∀ i ∈ A, I.cutoff i ≤ t := by
  classical
  simp [FullCoverInstance.batchDuration]

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- A nonempty batch has positive duration equal to one of its actual cutoffs. -/
theorem FullCoverInstance.batchDuration_mem {A : Finset ι} (hA : A.Nonempty) :
    0 < I.batchDuration A ∧ I.batchDuration A ∈ A.image I.cutoff := by
  classical
  obtain ⟨i,hi⟩ := hA
  have hb := (I.batchDuration_le_iff A (I.batchDuration A)).mp le_rfl
  have hp : 0 < I.batchDuration A := (I.cutoff_pos i).trans_le (hb.2 i hi)
  have hm := max'_mem (insert 0 (A.image I.cutoff)) (by simp)
  change I.batchDuration A ∈ insert 0 (A.image I.cutoff) at hm
  exact ⟨hp,(mem_insert.mp hm).resolve_left (ne_of_gt hp)⟩

/-- Threshold pairs considered by the approximation algorithm. -/
@[expose] def FullCoverInstance.cutoffPairs (D : K) : Finset (K × K) :=
  ((univ.image I.cutoff).product (insert 0 (univ.image I.cutoff))).filter
    (fun (a, b) => a + b ≤ D)

/-- Forced first-batch opportunities: their cutoff exceeds the second threshold. -/
@[expose] def FullCoverInstance.forcedFirst (b : K) : Finset ι :=
  univ.filter (fun i => b < I.cutoff i)

/-- Opportunities allowed in the first batch. -/
@[expose] def FullCoverInstance.allowedFirst (a : K) : Finset ι :=
  univ.filter (fun i => I.cutoff i ≤ a)

/-- A batch belongs to a cutoff family precisely when it contains all forced
members and only allowed members. -/
@[expose] def FullCoverInstance.InCutoffFamily (a b : K) (A : Finset ι) : Prop :=
  I.forcedFirst b ⊆ A ∧ A ⊆ I.allowedFirst a

/-- An enumerated pair never creates a spurious nonempty deadline-feasible batch. -/
theorem cutoff_family_feasible {D a b : K} (hab : (a, b) ∈ I.cutoffPairs D)
    {A : Finset ι} (hA : A.Nonempty) (hfamily : I.InCutoffFamily a b A) :
    I.TwoBatchFeasible D A := by
  classical
  obtain ⟨hpair,hD⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp hpair
  change a ∈ univ.image I.cutoff at ha
  change b ∈ insert 0 (univ.image I.cutoff) at hb
  obtain ⟨i,_,hi⟩ := mem_image.mp ha
  have ha₀ : 0 ≤ a := by rw [← hi]; exact (I.cutoff_pos i).le
  have hb₀ : 0 ≤ b := by
    rcases mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · obtain ⟨j,_,rfl⟩ := mem_image.mp hb
      exact (I.cutoff_pos j).le
  have hf := hfamily.1
  have hu := hfamily.2
  have hfirst : I.batchDuration A ≤ a := (I.batchDuration_le_iff A a).mpr
    ⟨ha₀,fun i hi => (mem_filter.mp (hu hi)).2⟩
  have hsecond : I.batchDuration Aᶜ ≤ b := (I.batchDuration_le_iff Aᶜ b).mpr
    ⟨hb₀,fun i hi => le_of_not_gt fun h =>
      (mem_compl.mp hi) (hf (mem_filter.mpr ⟨mem_univ _,h⟩))⟩
  exact ⟨hA,(add_le_add hfirst hsecond).trans hD⟩

omit [IsStrictOrderedRing K] in
/-- Every nonempty feasible first batch appears in one of the enumerated families. -/
theorem cutoff_families_cover {D : K} {A : Finset ι} (hA : I.TwoBatchFeasible D A) :
    ∃ ab ∈ I.cutoffPairs D, I.InCutoffFamily ab.1 ab.2 A := by
  classical
  let a := I.batchDuration A
  let b := I.batchDuration Aᶜ
  have ha := (I.batchDuration_mem hA.1).2
  have hau : a ∈ univ.image I.cutoff := (image_subset_iff.mpr fun i _ =>
    mem_image_of_mem _ (mem_univ i)) ha
  have hbu : b ∈ insert 0 (univ.image I.cutoff) := by
    by_cases he : Aᶜ = ∅
    · simp [b, he, FullCoverInstance.batchDuration]
    · have hb := (I.batchDuration_mem (nonempty_iff_ne_empty.mpr he)).2
      exact mem_insert_of_mem (image_subset_iff.mpr
        (fun i _ => mem_image_of_mem _ (mem_univ i)) hb)
  refine ⟨(a, b),mem_filter.mpr ⟨mem_product.mpr ⟨hau,hbu⟩,hA.2⟩,?_,?_⟩
  · intro i hi
    have hib := (mem_filter.mp hi).2
    by_contra hn
    have hle := ((I.batchDuration_le_iff Aᶜ b).mp le_rfl).2 i (mem_compl.mpr hn)
    exact (not_lt_of_ge hle) hib
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,((I.batchDuration_le_iff A a).mp le_rfl).2 i hi⟩

omit [IsStrictOrderedRing K] in
/-- A numerical bound on the actual finite threshold enumeration. -/
theorem cutoffPairs_card_le (D : K) :
    (I.cutoffPairs D).card ≤ Fintype.card ι * (Fintype.card ι + 1) := by
  classical
  have hi : (univ.image I.cutoff).card ≤ Fintype.card ι := card_image_le.trans_eq (card_univ)
  have hz : (insert 0 (univ.image I.cutoff)).card ≤ Fintype.card ι + 1 :=
    (card_insert_le _ _).trans (Nat.succ_le_succ hi)
  exact (card_filter_le ..).trans (by simpa using Nat.mul_le_mul hi hz)

end Cslib.Probability.StochasticOracle
