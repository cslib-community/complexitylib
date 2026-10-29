/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.IntegerProgramming
import Complexity.Computability.Complexity.Problems.Knapsack
import Complexity.Computability.Complexity.Problems.Partition
import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# NP-complete number problems: tests

Concrete instances in and out of `SubsetSum`, `Partition`, `Knapsack` and `ZeroOneIP`, boundary
cases (empty lists, target zero, repeated numbers, large binary numbers), the reductions on small
inputs and compositional `fun_prop` synthesis.
-/

namespace ComplexityTests.NPCompleteNumbers

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM
open scoped List

/-! ### Deciding small instances by enumerating sublists -/

theorem mem_SubsetSum_iff_sublists {l : List ℕ} {t : ℕ} :
    (l, t) ∈ SubsetSum ↔ ∃ s ∈ l.sublists, s.sum = t := by
  simp only [mem_SubsetSum_iff_sublist, List.mem_sublists]

theorem mem_Partition_iff_sublists {l : List ℕ} :
    l ∈ Partition ↔ ∃ s ∈ l.sublists, 2 * s.sum = l.sum := by
  simp only [mem_Partition_iff_sublist, List.mem_sublists]

theorem mem_Knapsack_iff_sublists {x : List (ℕ × ℕ) × ℕ × ℕ} :
    x ∈ Knapsack ↔ ∃ s ∈ x.1.sublists,
      (s.map Prod.fst).sum ≤ x.2.1 ∧ x.2.2 ≤ (s.map Prod.snd).sum := by
  simp only [mem_Knapsack_iff_sublist, List.mem_sublists]

/-! ### Headline results -/

example : SubsetSum ∈ NP (encPair (encList encNat) encNat) ∧
    PolyTimeReducible encCNF (encPair (encList encNat) encNat) SAT SubsetSum :=
  ⟨SubsetSum_npComplete.1, SubsetSum_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : Partition ∈ NP (encList encNat) ∧
    PolyTimeReducible encCNF (encList encNat) SAT Partition :=
  ⟨Partition_npComplete.1, Partition_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : Knapsack ∈ NP encKnapsack ∧
    PolyTimeReducible encCNF encKnapsack SAT Knapsack :=
  ⟨Knapsack_npComplete.1, Knapsack_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : ZeroOneIP ∈ NP (encList (encPair (encList encNat) encNat)) ∧
    PolyTimeReducible encCNF (encList (encPair (encList encNat) encNat)) SAT ZeroOneIP :=
  ⟨ZeroOneIP_npComplete.1, ZeroOneIP_npComplete.2 encCNF SAT SAT.mem_NP⟩

example :
    PolyTimeReducible encCNF (encList encNat) ThreeSAT Partition ∧
    PolyTimeReducible encCNF encKnapsack ThreeSAT Knapsack :=
  ⟨polyTimeReducible_ThreeSAT_SubsetSum.trans polyTimeReducible_SubsetSum_Partition,
   polyTimeReducible_ThreeSAT_SubsetSum.trans polyTimeReducible_SubsetSum_Knapsack⟩

/-! ### Compositional `fun_prop` synthesis -/

example :
    ComputableInPolyTime ThreeSAT.toSubsetSum encCNF
      (encPair (encList encNat) encNat) ∧
    ComputableInPolyTime (fun x => SubsetSum.toPartition x)
      (encPair (encList encNat) encNat) (encList encNat) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 + p.2 ≤ 2 * p.1))
      (encPair encNat encNat) encBool ∧
    ComputableInPolyTime (fun l : List ℕ => decide (l.sum < 2 ^ l.length))
      (encList encNat) encBool :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

/-! ### Binary comparison -/

example : (5 : ℕ) < 6 :=
  (Nat.lt_iff_exists_testBit 5 6).mpr ⟨1, by decide, by decide, by decide, by decide⟩

/-! ### `SubsetSum` -/

example : SubsetSum.verifier (([3, 5, 7], 12), [false, true, true]) = true := rfl
example : SubsetSum.verifier (([3, 5, 7], 12), [true, true, false]) = false := rfl
example : ([3, 5, 7], 12) ∈ SubsetSum := mem_SubsetSum_iff_sublists.2 (by decide)
example : ([3, 5, 7], 11) ∉ SubsetSum :=
  fun h => absurd (mem_SubsetSum_iff_sublists.1 h) (by decide)

-- Boundary cases: the empty list, target zero, and repeated numbers used with multiplicity.
example : ([], 0) ∈ SubsetSum := ⟨0, bot_le, rfl⟩
example : ([], 1) ∉ SubsetSum := fun h => absurd (mem_SubsetSum_iff_sublists.1 h) (by decide)
example : ([4, 9], 0) ∈ SubsetSum := mem_SubsetSum_iff_sublists.2 (by decide)
example : ([5, 5], 10) ∈ SubsetSum := mem_SubsetSum_iff_sublists.2 (by decide)
example : ([5], 10) ∉ SubsetSum := fun h => absurd (mem_SubsetSum_iff_sublists.1 h) (by decide)

-- Large numbers are compared in binary.
example : SubsetSum.verifier (([2 ^ 100, 2 ^ 100, 1], 2 ^ 101), [true, true, false]) = true := by
  decide
example : SubsetSum.verifier (([2 ^ 100, 2 ^ 100, 1], 2 ^ 101), [true, true, true]) = false := by
  decide

-- Certificates longer than the list select nothing beyond it.
example : maskSelect [3, 5] [true, false, true, true] = [3] := rfl
example : maskSelect [3, 5, 5] [false, true, true] = [5, 5] := rfl

/-! ### Sipser's digit construction -/

-- One clause `x₀`: numbers `9 = 1 + 8` (literal `x₀`), `1` (literal `¬x₀`) and two slack numbers
-- `8`, with target `1 + 3 * 8 = 25`.
example : ThreeSAT.toSubsetSum [[(0, true)]] = ([9, 1, 8, 8], 25) := by decide
example : ThreeSAT.toSubsetSum [[(0, true)]] ∈ SubsetSum :=
  (ThreeSAT.toSubsetSum_mem_iff _).2 ⟨by decide, fun _ => true, rfl⟩

-- Variable labels are numbered by first occurrence, so large binary labels do not enlarge the
-- numbers.
example : ThreeSAT.toSubsetSum [[(2 ^ 80, true)]] = ([9, 1, 8, 8], 25) := by decide

-- `x₀ ∧ ¬x₀` is unsatisfiable, and so is its digit construction.
example : ThreeSAT.toSubsetSum [[(0, true)], [(0, false)]] = ([9, 65, 8, 8, 64, 64], 217) := by
  decide
example : ThreeSAT.toSubsetSum [[(0, true)], [(0, false)]] ∉ SubsetSum := by
  intro h
  have : ([9, 65, 8, 8, 64, 64], 217) ∈ SubsetSum := by
    rwa [show ThreeSAT.toSubsetSum [[(0, true)], [(0, false)]] = ([9, 65, 8, 8, 64, 64], 217) by
      decide] at h
  exact absurd (mem_SubsetSum_iff_sublists.1 this) (by decide)

-- Repeated and complementary literals in a clause.
example : ThreeSAT.toSubsetSum [[(0, true), (0, true)]] = ([9, 1, 8, 8], 25) := by decide
example : ThreeSAT.toSubsetSum [[(0, true), (0, false)]] = ([9, 9, 8, 8], 25) := by decide

-- The empty formula is satisfiable; the empty clause is not.
example : ThreeSAT.toSubsetSum [] = ([], 0) := by decide
example : ThreeSAT.toSubsetSum [[]] = ([1, 1], 3) := by decide
example : ([1, 1], 3) ∉ SubsetSum := fun h => absurd (mem_SubsetSum_iff_sublists.1 h) (by decide)

-- Clauses wider than three literals give an instance without solutions.
example : ThreeSAT.toSubsetSum [[(0, true), (1, true), (2, true), (3, true)]] = ([], 1) := by
  decide

/-! ### `Partition` -/

example : Partition.verifier ([3, 1, 1, 2, 2, 1], [true, false, false, true, false, false]) =
    true := rfl
example : [3, 1, 1, 2, 2, 1] ∈ Partition := mem_Partition_iff_sublists.2 (by decide)
example : [1, 5] ∉ Partition := fun h => absurd (mem_Partition_iff_sublists.1 h) (by decide)
example : [1, 2] ∉ Partition := fun h => absurd (mem_Partition_iff_sublists.1 h) (by decide)

-- Boundary cases: the empty list and repeated numbers.
example : [] ∈ Partition := ⟨0, 0, rfl, rfl⟩
example : [7, 7] ∈ Partition := mem_Partition_iff_sublists.2 (by decide)
example : [7] ∉ Partition := fun h => absurd (mem_Partition_iff_sublists.1 h) (by decide)

-- The reduction appends `a.sum + 1` and `2 * t + 1`; it is defined for targets above `a.sum`.
example : SubsetSum.toPartition ([3, 5], 5) = [3, 5, 9, 11] := rfl
example : [3, 5, 9, 11] ∈ Partition := mem_Partition_iff_sublists.2 (by decide)
example : SubsetSum.toPartition ([3, 5], 4) = [3, 5, 9, 9] := rfl
example : [3, 5, 9, 9] ∉ Partition := fun h => absurd (mem_Partition_iff_sublists.1 h) (by decide)
example : SubsetSum.toPartition ([3, 5], 20) = [3, 5, 9, 41] := rfl
example : [3, 5, 9, 41] ∉ Partition := fun h => absurd (mem_Partition_iff_sublists.1 h) (by decide)
example : SubsetSum.toPartition ([], 0) = [1, 1] := rfl

/-! ### `Knapsack` -/

example : Knapsack.verifier (([(2, 3), (3, 4), (4, 5)], 5, 7), [true, true, false]) = true := rfl
example : ([(2, 3), (3, 4), (4, 5)], 5, 7) ∈ Knapsack := mem_Knapsack_iff_sublists.2 (by decide)
example : ([(2, 3), (3, 4), (4, 5)], 5, 8) ∉ Knapsack :=
  fun h => absurd (mem_Knapsack_iff_sublists.1 h) (by decide)

-- Boundary cases: no items, goal zero, and repeated items.
example : ([], 0, 0) ∈ Knapsack := mem_Knapsack_iff_sublists.2 (by decide)
example : ([], 5, 1) ∉ Knapsack := fun h => absurd (mem_Knapsack_iff_sublists.1 h) (by decide)
example : ([(1, 1), (1, 1)], 2, 2) ∈ Knapsack := mem_Knapsack_iff_sublists.2 (by decide)
example : ([(1, 1)], 2, 2) ∉ Knapsack :=
  fun h => absurd (mem_Knapsack_iff_sublists.1 h) (by decide)

-- Large weights and values are compared in binary.
example : Knapsack.verifier (([(2 ^ 90, 2 ^ 95)], 2 ^ 90, 2 ^ 95), [true]) = true := by decide
example : Knapsack.verifier (([(2 ^ 90 + 1, 2 ^ 95)], 2 ^ 90, 2 ^ 95), [true]) = false := by
  decide

example : SubsetSum.toKnapsack ([3, 5], 5) = ([(3, 3), (5, 5)], 5, 5) := rfl

-- The reduction carries the solvable instance `([3, 5], 8)` to a solvable knapsack, and the
-- unsolvable `([3, 5], 4)` to an unsolvable one.
example : SubsetSum.toKnapsack ([3, 5], 8) ∈ Knapsack :=
  (SubsetSum.toKnapsack_mem_iff _).2 (mem_SubsetSum_iff_sublists.2 (by decide))
example : SubsetSum.toKnapsack ([3, 5], 4) ∉ Knapsack := fun h =>
  absurd (mem_SubsetSum_iff_sublists.1 ((SubsetSum.toKnapsack_mem_iff _).1 h)) (by decide)

/-! ### `ZeroOneIP` -/

-- `x₀ + x₁ = 1` and `2 x₀ + 3 x₁ + x₂ = 4` with `x = (0, 1, 1)`.
example : ZeroOneIP.verifier ([([1, 1], 1), ([2, 3, 1], 4)], [false, true, true]) = true := rfl
example : [([1, 1], 1), ([2, 3, 1], 4)] ∈ ZeroOneIP :=
  ⟨fun j => decide (j = 1 ∨ j = 2), by decide⟩
example : [([2], 1)] ∉ ZeroOneIP := by
  rintro ⟨x, hx⟩
  have := hx _ (List.mem_singleton_self _)
  cases h : x 0 <;> simp [h] at this

-- The empty system is feasible; an equation without variables must have right-hand side zero.
example : [] ∈ ZeroOneIP := ⟨fun _ => false, by simp⟩
example : [([], 1)] ∉ ZeroOneIP := by
  rintro ⟨x, hx⟩
  simp at hx

example : SubsetSum.toZeroOneIP ([3, 5], 5) = [([3, 5], 5)] := rfl

-- The reduction carries the solvable instance `([3, 5], 8)` to a feasible system, and the
-- unsolvable `([3, 5], 4)` to an infeasible one.
example : SubsetSum.toZeroOneIP ([3, 5], 8) ∈ ZeroOneIP :=
  (SubsetSum.toZeroOneIP_mem_iff _).2 (mem_SubsetSum_iff_sublists.2 (by decide))
example : SubsetSum.toZeroOneIP ([3, 5], 4) ∉ ZeroOneIP := fun h =>
  absurd (mem_SubsetSum_iff_sublists.1 ((SubsetSum.toZeroOneIP_mem_iff _).1 h)) (by decide)

end ComplexityTests.NPCompleteNumbers
