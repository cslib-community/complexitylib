/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.SetFamily.RayChaudhuriWilson
import Complexity.Foundations.Combinatorics.SimpleGraph.Ramsey.FranklWilson
import Complexity.Computability.Complexity.ExplicitRamsey.FranklWilson
import Mathlib.Tactic.NormNum.Prime

/-!
# Ray-Chaudhuri–Wilson and Frankl–Wilson: checked instances

* The six `2`-subsets of a `4`-set attain the Ray-Chaudhuri–Wilson bound `C(4, 2)` with
  `L = {0, 1}`, and the modular Frankl–Wilson bound with `p = 3`.
* The side condition `|L| ≤ d mod p` cannot be dropped: with `p = 5` and `L = {0, 1, 3, 4}` the same
  family satisfies the other hypotheses, but `6 > C(4, 4)`.
* The near-pencil on four points (one triple and the three pairs through the remaining point),
  pairwise meeting in one point, is a nonuniform instance of the bound `∑_{i ≤ 1} C(4, i) = 5`.
* The Frankl–Wilson graph for `p = 2`: `56 < R(9, 9)`; adjacency and recognition on names, and the
  strict-sortedness test `List.isSortedLT`.
-/

open Finset SimpleGraph Cslib.ExplicitRamsey

/-! ### The intersection bounds -/

/-- The six `2`-subsets of `Fin 4`. -/
def pairs : Fin 6 → Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

/-- Ray-Chaudhuri–Wilson is tight: six `2`-sets pairwise meeting in `0` or `1` points. -/
example : Fintype.card (Fin 6) ≤ (Fintype.card (Fin 4)).choose #({0, 1} : Finset ℕ) :=
  Fintype.card_le_choose_of_card_inter_mem_of_lt pairs (d := 2) {0, 1} (by decide) (by decide)
    (by decide)

/-- Modular Frankl–Wilson is tight at `p = 3`, `d = 2`, `L = {0, 1}`. -/
example : Fintype.card (Fin 6) ≤ (Fintype.card (Fin 4)).choose #({0, 1} : Finset (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact Fintype.card_le_choose_of_card_inter_mem_zmod pairs (d := 2) {0, 1} (by decide)
    (by decide) (by decide) (by decide)

/-- Without `|L| ≤ d mod p` the bound fails: at `p = 5`, `L = {0, 1, 3, 4}` contains every
intersection size mod `5` and avoids `d = 2`, yet six sets exceed `C(4, 4) = 1`. -/
example : (∀ i j, i ≠ j → ((#(pairs i ∩ pairs j) : ℕ) : ZMod 5) ∈ ({0, 1, 3, 4} : Finset _)) ∧
    ((2 : ℕ) : ZMod 5) ∉ ({0, 1, 3, 4} : Finset (ZMod 5)) ∧
    ¬ #({0, 1, 3, 4} : Finset (ZMod 5)) ≤ 2 % 5 ∧
    ¬ Fintype.card (Fin 6) ≤ (Fintype.card (Fin 4)).choose #({0, 1, 3, 4} : Finset (ZMod 5)) := by
  decide

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The near-pencil on `Fin 4`: pairwise intersections have exactly one point. -/
def nearPencil : Fin 4 → Finset (Fin 4) := ![{1, 2, 3}, {0, 1}, {0, 2}, {0, 3}]

/-- The nonuniform bound over `ZMod 5` with `L = {1}`: at most `1 + 4 = 5` sets. -/
example : Fintype.card (Fin 4) ≤
    ∑ i ∈ range (#({1} : Finset (ZMod 5)) + 1), (Fintype.card (Fin 4)).choose i :=
  Fintype.card_le_sum_choose_of_card_inter_mem nearPencil {1} (by decide) (by decide)

/-! ### The Frankl–Wilson graph -/

/-- For `p = 2`: `C(8, 3) = 56 < R(9, 9)`, where `9 = C(8, 1) + 1`. -/
example : 56 < ramseyNumber 9 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := choose_lt_ramseyNumber_franklWilson 2
  rwa [show (2 ^ 3 : ℕ).choose (2 ^ 2 - 1) = 56 by decide,
    show (2 ^ 3 : ℕ).choose (2 - 1) + 1 = 9 by decide] at h

/-- The superpolynomial bound at `c = 2`, which needs a prime `p ≥ 15`. -/
example : ((17 ^ 3 : ℕ).choose (17 - 1) + 1) ^ 2 <
    ramseyNumber ((17 ^ 3 : ℕ).choose (17 - 1) + 1) ((17 ^ 3 : ℕ).choose (17 - 1) + 1) := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact pow_lt_ramseyNumber_franklWilson (by norm_num)

/-- For `p = 2`, `d = 3`: `{0, 1, 2}` and `{0, 3, 4}` meet in one point, which is `≡ d`, so they
are not adjacent. -/
example : franklWilsonAdj (2, [0, 1, 2], [0, 3, 4]) = false := by decide

/-- `{0, 1, 2}` and `{0, 1, 3}` meet in two points, `≢ d (mod 2)`: adjacent. -/
example : franklWilsonAdj (2, [0, 1, 2], [0, 1, 3]) = true := by decide

/-- Disjoint sets meet in zero points: adjacent for `p = 2`. -/
example : franklWilsonAdj (2, [0, 1, 2], [3, 4, 5]) = true := by decide

/-- A vertex is not adjacent to itself. -/
example : franklWilsonAdj (2, [0, 1, 2], [0, 1, 2]) = false := by decide

example : franklWilsonIsLabel (2, [0, 5, 7]) = true := by decide

/-- Entries must lie below `p ^ 3 = 8`. -/
example : franklWilsonIsLabel (2, [0, 5, 8]) = false := by decide

/-- Entries must be strictly increasing. -/
example : franklWilsonIsLabel (2, [0, 5, 5]) = false := by decide

/-- Names must have `p ^ 2 - 1 = 3` entries. -/
example : franklWilsonIsLabel (2, [0, 5]) = false := by decide

example : isSubsetLabel (10, 2, [3, 9]) = true := by decide

example : [1, 4, 6].isSortedLT = true := by decide

example : [1, 4, 4].isSortedLT = false := by decide

example : ([] : List ℕ).isSortedLT = true := by decide

example : subsetAdj (3, 2, [1, 2], [2, 4]) = true := by decide

/-- Adjacency in the Frankl–Wilson graph on `Fin 8` with `p = 2`, `d = 3` is `franklWilsonAdj`. -/
example (s t : {s : Finset (Fin (2 ^ 3)) // #s = 2 ^ 2 - 1}) :
    (franklWilsonGraph (Fin (2 ^ 3)) 2 (2 ^ 2 - 1)).Adj s t ↔
      franklWilsonAdj (2, subsetLabel s, subsetLabel t) = true :=
  franklWilsonGraph_adj_iff_franklWilsonAdj s t
