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

/-!
# The 0-1 knapsack problem

`Knapsack` is the decision version of the 0-1 knapsack problem: given items, each with a weight
and a value, a capacity and a goal, some sub-multiset of the items has total weight at most the
capacity and total value at least the goal [GareyJohnson1979]. All numbers are encoded in binary
(`encNat`); the verifier compares the sums in binary (`ComputableInPolyTime.binary_le`).

Giving every number of a subset sum instance equal weight and value, and taking the target as
both capacity and goal, reduces `SubsetSum` to `Knapsack`. Karp's KNAPSACK [Karp1972] is the
subset sum form of the problem.

## Main definitions

* `Cslib.Complexity.Knapsack`, `Cslib.Complexity.encKnapsack`.
* `Cslib.Complexity.Knapsack.verifier`.
* `Cslib.Complexity.SubsetSum.toKnapsack`.

## Main results

* `Cslib.Complexity.mem_Knapsack_iff_sublist`: solutions are subsequences of the items.
* `Cslib.Complexity.Knapsack.mem_NP`: `Knapsack ∈ NP encKnapsack`.
* `Cslib.Complexity.SubsetSum.toKnapsack_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_SubsetSum_Knapsack`, `Cslib.Complexity.Knapsack_npHard`,
  `Cslib.Complexity.Knapsack_npComplete`: `Knapsack` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime
open scoped List

/-- Instances `(items, capacity, goal)` of the 0-1 knapsack problem, items given as
`(weight, value)`: some sub-multiset of the items has total weight at most the capacity and total
value at least the goal [Garey and Johnson][GareyJohnson1979]. -/
def Knapsack : Set (List (ℕ × ℕ) × ℕ × ℕ) :=
  {x | ∃ s ≤ (x.1 : Multiset (ℕ × ℕ)),
    (s.map Prod.fst).sum ≤ x.2.1 ∧ x.2.2 ≤ (s.map Prod.snd).sum}

/-- Knapsack instances, with all numbers in binary. -/
abbrev encKnapsack : List (ℕ × ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair (encList (encPair encNat encNat)) (encPair encNat encNat)

/-- Knapsack asks for a subsequence of the items. -/
theorem mem_Knapsack_iff_sublist {x : List (ℕ × ℕ) × ℕ × ℕ} :
    x ∈ Knapsack ↔
      ∃ s, s <+ x.1 ∧ (s.map Prod.fst).sum ≤ x.2.1 ∧ x.2.2 ≤ (s.map Prod.snd).sum := by
  change (∃ s ≤ (x.1 : Multiset (ℕ × ℕ)), _) ↔ _
  simpa only [Multiset.map_coe, Multiset.sum_coe] using exists_le_coe_iff_exists_sublist (l := x.1)
    (fun s => (s.map Prod.fst).sum ≤ x.2.1 ∧ x.2.2 ≤ (s.map Prod.snd).sum)

namespace Knapsack

/-- The verifier for `Knapsack`: the items selected by the certificate mask fit the capacity and
reach the goal. -/
def verifier (x : (List (ℕ × ℕ) × ℕ × ℕ) × List Bool) : Bool :=
  decide (((maskSelect x.1.1 x.2).map Prod.fst).sum ≤ x.1.2.1) &&
    decide (x.1.2.2 ≤ ((maskSelect x.1.1 x.2).map Prod.snd).sum)

/-- `Knapsack.verifier` verifies `Knapsack` with certificates as long as the encoded instance. -/
theorem isVerifier : IsVerifier encKnapsack Polynomial.X verifier Knapsack := by
  intro x
  simp only [Knapsack, Set.mem_ofPred_eq, Polynomial.eval_X, verifier, Bool.and_eq_true,
    decide_eq_true_eq]
  simpa only [Multiset.map_coe, Multiset.sum_coe] using exists_le_iff_exists_maskSelect
    (length_le_length_encPair (encPair encNat encNat) (encPair encNat encNat) x)
    (fun s => (s.map Prod.fst).sum ≤ x.2.1 ∧ x.2.2 ≤ (s.map Prod.snd).sum)

/-- The `Knapsack` verifier is polynomial-time: the sums and comparisons are in binary. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encKnapsack encBits) encBool := by
  have hx11 : ComputableInPolyTime (fun x : (List (ℕ × ℕ) × ℕ × ℕ) × List Bool => x.1.1)
      (encPair encKnapsack encBits) (encList (encPair encNat encNat)) :=
    (fst _ _).comp (fst _ _)
  have hx12 : ComputableInPolyTime (fun x : (List (ℕ × ℕ) × ℕ × ℕ) × List Bool => x.1.2)
      (encPair encKnapsack encBits) (encPair encNat encNat) :=
    (snd _ _).comp (fst _ _)
  have hsel : ComputableInPolyTime
      (fun x : (List (ℕ × ℕ) × ℕ × ℕ) × List Bool => maskSelect x.1.1 x.2)
      (encPair encKnapsack encBits) (encList (encPair encNat encNat)) :=
    (computableInPolyTime_maskSelect (encPair encNat encNat)).comp (hx11.prod (snd _ _))
  have hsum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop
  have hw := hsum.comp ((map (fst encNat encNat)).comp hsel)
  have hv := hsum.comp ((map (snd encNat encNat)).comp hsel)
  exact bool_and' (binary_le' hw ((fst _ _).comp hx12)) (binary_le' ((snd _ _).comp hx12) hv)

/-- `Knapsack` belongs to `NP`. -/
theorem mem_NP : Knapsack ∈ NP encKnapsack :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end Knapsack

namespace SubsetSum

/-- The reduction from `SubsetSum` to `Knapsack`: each number becomes an item with equal weight
and value, and the target becomes both the capacity and the goal. -/
def toKnapsack (x : List ℕ × ℕ) : List (ℕ × ℕ) × ℕ × ℕ := (x.1.map fun a => (a, a), x.2, x.2)

/-- **Correctness of the reduction to `Knapsack`.** -/
theorem toKnapsack_mem_iff (x : List ℕ × ℕ) : toKnapsack x ∈ Knapsack ↔ x ∈ SubsetSum := by
  obtain ⟨l, t⟩ := x
  simp only [Knapsack, toKnapsack, mem_SubsetSum, Set.mem_ofPred_eq, ← Multiset.map_coe]
  constructor
  · rintro ⟨s, hs, hle, hge⟩
    have hdiag : s.map Prod.snd = s.map Prod.fst := Multiset.map_congr rfl fun p hp => by
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hs hp)
      rfl
    refine ⟨s.map Prod.fst, ?_, by rw [hdiag] at hge; lia⟩
    simpa [Multiset.map_map, Function.comp_def] using Multiset.map_le_map (f := Prod.fst) hs
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.map fun a => (a, a), Multiset.map_le_map hs, ?_, ?_⟩ <;> simp [Multiset.map_map]

/-- The reduction to `Knapsack` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toKnapsack :
    ComputableInPolyTime toKnapsack (encPair (encList encNat) encNat) encKnapsack :=
  ((map (id'.prod id')).comp (fst _ _)).prod ((snd _ _).prod (snd _ _))

end SubsetSum

/-- `SubsetSum` reduces to `Knapsack` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_Knapsack :
    PolyTimeReducible (encPair (encList encNat) encNat) encKnapsack SubsetSum Knapsack :=
  ⟨SubsetSum.toKnapsack, SubsetSum.computableInPolyTime_toKnapsack,
    fun x => (SubsetSum.toKnapsack_mem_iff x).symm⟩

/-- `Knapsack` is `NP`-hard. -/
theorem Knapsack_npHard : NPHard encKnapsack Knapsack :=
  SubsetSum_npHard.trans polyTimeReducible_SubsetSum_Knapsack

/-- **The 0-1 knapsack problem is NP-complete**, with all numbers in binary
[Garey and Johnson][GareyJohnson1979]. -/
theorem Knapsack_npComplete : NPComplete encKnapsack Knapsack :=
  ⟨Knapsack.mem_NP, Knapsack_npHard⟩

end Cslib.Complexity
