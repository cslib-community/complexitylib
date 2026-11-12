/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SubsetSum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# The 0-1 knapsack problem

`Knapsack` is the decision version of the 0-1 knapsack problem: an instance `x : KnapsackInstance`
(`Cslib.Complexity.encKnapsack`) gives a list of items `x.items` (`Cslib.Complexity.Knapsack.Item`),
each with a weight and a value, a capacity `x.capacity`, and a goal `x.goal`, and asks whether some
sub-multiset of the items has total weight at most `x.capacity` and total value at least `x.goal`
[GareyJohnson1979]. All numbers are encoded in binary (`encNat`); the verifier compares the sums in
binary (`ComputableInPolyTime.binary_le`).

Giving every number of a subset sum instance equal weight and value, and taking the target as
both capacity and goal, reduces `SubsetSum` to `Knapsack`. Karp's KNAPSACK [Karp1972] is the
subset sum form of the problem.

## Main definitions

* `Cslib.Complexity.Knapsack.Item`, `Cslib.Complexity.Knapsack.encItem`: knapsack items with weight
  and value, and their binary encoding.
* `Cslib.Complexity.KnapsackInstance`, `Cslib.Complexity.encKnapsack`: knapsack instances and their
  binary encoding.
* `Cslib.Complexity.Knapsack`, `Cslib.Complexity.Knapsack.verifier`.
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

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime
open scoped List

namespace Knapsack

/-- An item in `Knapsack`, with a natural-number weight and value. -/
@[ext]
structure Item where
  /-- The weight of the item. -/
  weight : ℕ
  /-- The value of the item. -/
  value : ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of a `Knapsack.Item` as `(weight, value)`. -/
enc_structure encItem : Item where weight : encNat, value : encNat

attribute [fun_prop] encItem_weight_polyTime encItem_value_polyTime encItem_mk_polyTime

end Knapsack

/-- An instance of the 0-1 knapsack problem [Garey and Johnson][GareyJohnson1979]: a list of
items `items`, a weight capacity `capacity`, and a value goal `goal`. -/
@[ext]
structure KnapsackInstance where
  /-- The available items, each with a weight and a value. -/
  items : List Knapsack.Item
  /-- The maximum total weight allowed. -/
  capacity : ℕ
  /-- The minimum total value required. -/
  goal : ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of `KnapsackInstance` as `(items, (capacity, goal))`. -/
enc_structure encKnapsack : KnapsackInstance where
  items : (encList Knapsack.encItem), capacity : encNat, goal : encNat

attribute [fun_prop] encKnapsack_items_polyTime encKnapsack_capacity_polyTime
  encKnapsack_goal_polyTime encKnapsack_mk_polyTime

/-- The 0-1 knapsack problem: instances `x : KnapsackInstance` for which some sub-multiset of
`x.items` has total weight at most `x.capacity` and total value at least `x.goal`
[Garey and Johnson][GareyJohnson1979]. -/
@[expose]
def Knapsack : Set KnapsackInstance :=
  {x | ∃ s ≤ (x.items : Multiset Knapsack.Item),
    (s.map Knapsack.Item.weight).sum ≤ x.capacity ∧ x.goal ≤ (s.map Knapsack.Item.value).sum}

/-- Knapsack asks for a subsequence of the items. -/
theorem mem_Knapsack_iff_sublist {x : KnapsackInstance} :
    x ∈ Knapsack ↔
      ∃ s, s <+ x.items ∧ (s.map Knapsack.Item.weight).sum ≤ x.capacity ∧
        x.goal ≤ (s.map Knapsack.Item.value).sum := by
  change (∃ s ≤ (x.items : Multiset Knapsack.Item), _) ↔ _
  simpa only [Multiset.map_coe, Multiset.sum_coe] using
    exists_le_coe_iff_exists_sublist (l := x.items)
      (fun s => (s.map Knapsack.Item.weight).sum ≤ x.capacity ∧
        x.goal ≤ (s.map Knapsack.Item.value).sum)

namespace Knapsack

/-- The verifier for `Knapsack`, a mask verifier (`Cslib.Complexity.maskVerifier`): the items
selected by the certificate mask fit the capacity and reach the goal. -/
@[expose]
def verifier : KnapsackInstance × List Bool → Bool :=
  maskVerifier KnapsackInstance.items fun x =>
    decide ((x.2.map Item.weight).sum ≤ x.1.capacity) &&
      decide (x.1.goal ≤ (x.2.map Item.value).sum)

/-- `Knapsack.verifier` verifies `Knapsack` with certificates as long as the encoded instance. -/
theorem isVerifier : IsVerifier encKnapsack Polynomial.X verifier Knapsack :=
  isVerifier_maskVerifier (fun x => by
    rw [Polynomial.eval_X]
    exact (length_le_length_encList _ _).trans
      (length_le_encPair_left _ _ (x.items, x.capacity, x.goal)))
    fun _ _ _ => by simp

/-- The `Knapsack` verifier is polynomial-time: the sums and comparisons are in binary. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encKnapsack encBits) encBool := by
  have hsum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop
  have hw := hsum.comp ((map (encItem_weight_polyTime id')).comp
    (snd encKnapsack (encList encItem)))
  have hv := hsum.comp ((map (encItem_value_polyTime id')).comp
    (snd encKnapsack (encList encItem)))
  exact computableInPolyTime_maskVerifier (encKnapsack_items_polyTime id')
    (bool_and' (binary_le' hw (encKnapsack_capacity_polyTime (fst _ _)))
      (binary_le' (encKnapsack_goal_polyTime (fst _ _)) hv))

/-- `Knapsack` belongs to `NP`. -/
theorem mem_NP : Knapsack ∈ NP encKnapsack :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end Knapsack

namespace SubsetSum

/-- The reduction from `SubsetSum` to `Knapsack`: each number becomes an item with equal weight
and value, and the target becomes both the capacity and the goal. -/
@[expose]
def toKnapsack (x : SubsetSumInstance) : KnapsackInstance :=
  ⟨x.numbers.map fun a => ⟨a, a⟩, x.target, x.target⟩

/-- **Correctness of the reduction to `Knapsack`.** -/
theorem toKnapsack_mem_iff (x : SubsetSumInstance) : toKnapsack x ∈ Knapsack ↔ x ∈ SubsetSum := by
  obtain ⟨l, t⟩ := x
  simp only [Knapsack, toKnapsack, mem_SubsetSum, Set.mem_ofPred_eq, ← Multiset.map_coe]
  constructor
  · rintro ⟨s, hs, hle, hge⟩
    have hdiag : s.map Knapsack.Item.value = s.map Knapsack.Item.weight :=
      Multiset.map_congr rfl fun p hp => by
        obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hs hp)
        rfl
    refine ⟨s.map Knapsack.Item.weight, ?_, by rw [hdiag] at hge; lia⟩
    simpa [Multiset.map_map, Function.comp_def] using
      Multiset.map_le_map (f := Knapsack.Item.weight) hs
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.map fun a => ⟨a, a⟩, Multiset.map_le_map hs, ?_, ?_⟩ <;> simp [Multiset.map_map]

/-- The reduction to `Knapsack` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toKnapsack :
    ComputableInPolyTime toKnapsack encSubsetSum encKnapsack := by
  unfold toKnapsack
  fun_prop

end SubsetSum

/-- `SubsetSum` reduces to `Knapsack` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_Knapsack :
    PolyTimeReducible encSubsetSum encKnapsack SubsetSum Knapsack :=
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
