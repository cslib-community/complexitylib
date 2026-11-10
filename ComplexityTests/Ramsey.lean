/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.SimpleGraph.Ramsey.Erdos
import Complexity.Computability.Complexity.ExplicitRamsey
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Ramsey numbers: checked instances

* `R(3, 3) = 6`: the upper bound is Erdős–Szekeres, the lower bound is the `5`-cycle, which has no
  triangle and no independent triple.
* Erdős's counting bound at small `k`, where the hypothesis holds, and an instance where it fails.
* Oddtown and the uniform Fisher inequality are tight: singletons, and the seven lines of the Fano
  plane on seven points, pairwise meeting in one point.
* Nagy's adjacency on names: two triples meeting in one point are adjacent, triples meeting in
  zero or two points are not, and names are recognized.
-/

open SimpleGraph Finset Cslib.ExplicitRamsey

/-! ### `R(3, 3) = 6` -/

/-- `C₅` has no triangle and no independent triple, so `5 < R(3, 3)`. -/
example : 5 < ramseyNumber 3 3 := by
  have h := card_lt_ramseyNumber_iff (k := 3) (l := 3) (V := Fin 5)
  rw [Fintype.card_fin] at h
  refine h.2 ⟨cycleGraph 5, ?_, ?_⟩
  · unfold CliqueFree; decide
  · unfold IndepSetFree; decide

example : ramseyNumber 3 3 = 6 := by
  refine le_antisymm (ramseyNumber_succ_succ_le 2 2) ?_
  have h := card_lt_ramseyNumber_iff (k := 3) (l := 3) (V := Fin 5)
  rw [Fintype.card_fin] at h
  refine h.2 ⟨cycleGraph 5, ?_, ?_⟩
  · unfold CliqueFree; decide
  · unfold IndepSetFree; decide

example : ramseyNumber 4 4 ≤ 20 := ramseyNumber_succ_succ_le 3 3

example : ramseyNumber 5 3 = ramseyNumber 3 5 := ramseyNumber_comm 5 3

example (k : ℕ) : ramseyNumber k k ≤ 4 ^ (k - 1) := ramseyNumber_le_four_pow k

/-! ### Erdős's bound -/

example : 3 < ramseyNumber 3 3 := lt_ramseyNumber_of_two_mul_choose_lt (by decide)

example : 6 < ramseyNumber 4 4 := lt_ramseyNumber_of_two_mul_choose_lt (by decide)

example : 32 < ramseyNumber 10 10 := lt_ramseyNumber_of_sq_le (by norm_num) (by norm_num)

/-- The asymmetric form at `(k, l) = (3, 4)` with `n = 4`. -/
example : 4 < ramseyNumber 3 4 := lt_ramseyNumber_of_choose (by decide)

/-- The hypothesis of Erdős's bound fails at `n = 7`, `k = 4`, although `7 < R(4, 4) = 18`. -/
example : ¬ 2 * (7 : ℕ).choose 4 < 2 ^ (4 : ℕ).choose 2 := by decide

example : (2 : ℝ) ^ ((20 : ℝ) / 2) < ramseyNumber 20 20 :=
  two_rpow_half_lt_ramseyNumber (by norm_num)

/-! ### Oddtown and Fisher are tight -/

/-- Singletons form an oddtown family of `|κ|` sets. -/
example : Fintype.card (Fin 4) ≤ Fintype.card (Fin 4) :=
  Fintype.card_le_of_odd_card_of_even_card_inter (fun i : Fin 4 => {i})
    (fun i => by simp) (fun i j hij => by simp [hij])

/-- The seven lines of the Fano plane on seven points. -/
def fanoLine : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

example : Fintype.card (Fin 7) ≤ Fintype.card (Fin 7) :=
  Fintype.card_le_of_card_eq_of_card_inter_eq fanoLine (d := 3) (c := 1) (by decide)
    (by decide) (by decide)

/-! ### Nagy's graph -/

example (t : ℕ) : t.choose 3 < ramseyNumber (t + 1) (t + 1) := choose_three_lt_ramseyNumber t

/-- `C(7, 3) = 35 < R(8, 8)`. For small `k` the explicit bound beats Erdős's `16 < R(8, 8)`;
the exponential bound `2 ^ (k / 2)` overtakes `C(k - 1, 3)` from `k = 20` on. -/
example : 35 < ramseyNumber 8 8 := by
  have h := choose_three_lt_ramseyNumber 7
  rwa [show (7 : ℕ).choose 3 = 35 by decide] at h

/-- `{0, 1, 2}` and `{2, 3, 4}` meet in one point. -/
example : nagyAdj ((0, 1, 2), (2, 3, 4)) = true := by decide

/-- `{0, 1, 2}` and `{1, 2, 3}` meet in two points. -/
example : nagyAdj ((0, 1, 2), (1, 2, 3)) = false := by decide

/-- `{0, 1, 2}` and `{3, 4, 5}` are disjoint. -/
example : nagyAdj ((0, 1, 2), (3, 4, 5)) = false := by decide

/-- A vertex is not adjacent to itself. -/
example : nagyAdj ((0, 1, 2), (0, 1, 2)) = false := by decide

example : nagyIsLabel (5, 0, 2, 4) = true := by decide

example : nagyIsLabel (5, 0, 2, 5) = false := by decide

example : nagyIsLabel (5, 2, 2, 4) = false := by decide

/-- Adjacency in Nagy's graph on `Fin 5` agrees with `nagyAdj` on names. -/
example (s s' : {s : Finset (Fin 5) // #s = 3}) :
    (nagyGraph (Fin 5)).Adj s s' ↔ nagyAdj (nagyLabel s, nagyLabel s') = true :=
  nagyGraph_adj_iff_nagyAdj s s'
