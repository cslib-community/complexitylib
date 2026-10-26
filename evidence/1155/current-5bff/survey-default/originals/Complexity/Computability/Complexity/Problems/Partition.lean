/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.Sublists

/-!
# Partition

`Partition` is the set of lists of natural numbers, possibly with repetitions, that split into two
sub-multisets with equal sums [Karp1972]. Numbers are encoded in binary (`encNat`).

Appending the two numbers `a.sum + 1` and `2 * t + 1` to the numbers `a` reduces `SubsetSum` to
`Partition`: together these two exceed half of the new total, so they lie on opposite sides of any
partition, and the side holding `a.sum + 1` holds numbers of `a` summing to exactly `t`. Neither
number needs subtraction, so the reduction is defined for every target, including targets larger
than `a.sum`.

## Main definitions

* `Cslib.Complexity.Partition`.
* `Cslib.Complexity.Partition.verifier`.
* `Cslib.Complexity.SubsetSum.toPartition`.

## Main results

* `Cslib.Complexity.mem_Partition_iff`, `Cslib.Complexity.mem_Partition_iff_sublist`: a partition
  is a sub-multiset, or a subsequence, with half the total sum.
* `Cslib.Complexity.Partition.mem_NP`: `Partition ∈ NP (encList encNat)`.
* `Cslib.Complexity.SubsetSum.toPartition_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_SubsetSum_Partition`, `Cslib.Complexity.Partition_npHard`,
  `Cslib.Complexity.Partition_npComplete`: `Partition` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime
open scoped List

/-- The lists of natural numbers that split into two sub-multisets with equal sums [Karp1972]. -/
def Partition : Set (List ℕ) := {l | ∃ s t : Multiset ℕ, s + t = l ∧ s.sum = t.sum}

/-- A partition is a sub-multiset holding half of the total sum. -/
theorem mem_Partition_iff {l : List ℕ} :
    l ∈ Partition ↔ ∃ s ≤ (l : Multiset ℕ), 2 * s.sum = l.sum := by
  constructor
  · rintro ⟨s, t, hst, hsum⟩
    refine ⟨s, hst ▸ Multiset.le_add_right s t, ?_⟩
    rw [← Multiset.sum_coe, ← hst, Multiset.sum_add, hsum, two_mul]
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, l - s, add_tsub_cancel_of_le hs, ?_⟩
    have h := congrArg Multiset.sum (add_tsub_cancel_of_le hs)
    rw [Multiset.sum_add, Multiset.sum_coe] at h
    lia

/-- A partition is a subsequence holding half of the total sum. -/
theorem mem_Partition_iff_sublist {l : List ℕ} :
    l ∈ Partition ↔ ∃ s, s <+ l ∧ 2 * s.sum = l.sum := by
  simpa only [Multiset.sum_coe] using
    mem_Partition_iff.trans (exists_le_coe_iff_exists_sublist (fun s => 2 * s.sum = l.sum))

namespace Partition

/-- The verifier for `Partition`: the numbers selected by the certificate mask hold half of the
total sum. -/
def verifier (x : List ℕ × List Bool) : Bool := decide (2 * (maskSelect x.1 x.2).sum = x.1.sum)

/-- `Partition.verifier` verifies `Partition` with certificates as long as the encoded list. -/
theorem isVerifier : IsVerifier (encList encNat) Polynomial.X verifier Partition := by
  intro l
  simp only [mem_Partition_iff, Polynomial.eval_X, verifier, decide_eq_true_eq]
  simpa only [Multiset.sum_coe] using exists_le_iff_exists_maskSelect
    (length_le_length_encList encNat l) (fun s => 2 * s.sum = l.sum)

/-- The `Partition` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encList encNat) encBits) encBool := by
  unfold verifier
  fun_prop

/-- `Partition` belongs to `NP`. -/
theorem mem_NP : Partition ∈ NP (encList encNat) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end Partition

namespace SubsetSum

/-- The reduction from `SubsetSum` to `Partition`: append `a.sum + 1` and `2 * t + 1`. -/
def toPartition (x : List ℕ × ℕ) : List ℕ := x.1 ++ [x.1.sum + 1, 2 * x.2 + 1]

/-- **Correctness of the reduction to `Partition`.** -/
theorem toPartition_mem_iff (x : List ℕ × ℕ) : toPartition x ∈ Partition ↔ x ∈ SubsetSum := by
  obtain ⟨l, t⟩ := x
  rw [mem_Partition_iff_sublist, mem_SubsetSum_iff_sublist]
  constructor
  · rintro ⟨s, hs, hsum⟩
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hs
    obtain ⟨r, hr⟩ := h₁.exists_perm_append
    have hl := hr.sum_eq
    simp only [toPartition, List.sum_append, List.sum_cons, List.sum_nil] at hsum hl
    have hmem := List.mem_sublists.2 h₂
    simp only [List.sublists, List.foldr_cons, List.foldr_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;>
      simp only [List.sum_cons, List.sum_nil] at hsum
    · lia
    · exact ⟨r₁, h₁, by lia⟩
    · -- The numbers of `l` beside `2 * t + 1` leave numbers of `l` summing to `t`.
      obtain ⟨r', hr', hsub⟩ : r <+~ l :=
        (List.sublist_append_right r₁ r).subperm.trans hr.symm.subperm
      exact ⟨r', hsub, by rw [hr'.sum_eq]; lia⟩
    · lia
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s ++ [l.sum + 1], hs.append (by simp), ?_⟩
    simp only [toPartition, List.sum_append, List.sum_cons, List.sum_nil]
    lia

/-- The reduction to `Partition` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toPartition :
    ComputableInPolyTime toPartition (encPair (encList encNat) encNat) (encList encNat) := by
  unfold toPartition
  fun_prop

end SubsetSum

/-- `SubsetSum` reduces to `Partition` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_Partition :
    PolyTimeReducible (encPair (encList encNat) encNat) (encList encNat) SubsetSum Partition :=
  ⟨SubsetSum.toPartition, SubsetSum.computableInPolyTime_toPartition,
    fun x => (SubsetSum.toPartition_mem_iff x).symm⟩

/-- `Partition` is `NP`-hard. -/
theorem Partition_npHard : NPHard (encList encNat) Partition :=
  SubsetSum_npHard.trans polyTimeReducible_SubsetSum_Partition

/-- **Partition is NP-complete**, with the numbers in binary [Karp1972]. -/
theorem Partition_npComplete : NPComplete (encList encNat) Partition :=
  ⟨Partition.mem_NP, Partition_npHard⟩

end Cslib.Complexity
