/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Problems.TSP.HeldKarp
import Mathlib.Data.Fin.VecNotation

/-!
# Worked Bellman–Held–Karp examples

These kernel-checked examples (using `decide`, never `native_decide`) exercise
`Cslib.Algorithms.Lean.TSP.heldKarp` and its `TSP`/`HamCycle` deciders:

1. An asymmetric instance on three cities with optimal tour `0 → 1 → 2 → 0` of cost `3`, whose
   reverse costs `15`, and the observed tick count `6 ≤ 2² · 2²`.
2. The four-city instance with optimum `21`, checked against brute force over all `3!` orderings,
   in `24 ≤ 3² · 2³` ticks.
3. Integer costs, including negative ones: `W` need not be `ℕ`.
4. Edge cases: one city (`n = 0`) costs its self-loop in zero ticks, and the empty `TSP` instance
   is accepted.
5. The `TSP` decider on both sides of the optimum, and the `HamCycle` decider on a triangle (yes)
   and a path on three vertices (no).
-/

public section

namespace ComplexityTests.TSPHeldKarp

open Cslib.Algorithms.Lean.TSP Cslib.Complexity

/-! ### 1. An asymmetric three-city instance -/

/-- Going around `0 → 1 → 2 → 0` costs `1` per step; the other direction costs `5` per step. -/
def d3 : Fin 3 → Fin 3 → ℕ := ![![0, 1, 5], ![5, 0, 1], ![1, 5, 0]]

example : (heldKarp d3).ret = 3 := by decide
example : walkCost d3 0 [1, 2] 0 = 3 := by decide
example : walkCost d3 0 [2, 1] 0 = 15 := by decide
example : (heldKarp d3).time = 6 := by decide

/-! ### 2. A four-city instance against brute force -/

/-- An asymmetric four-city cost matrix with optimal tour `0 → 2 → 3 → 1 → 0` of cost `21`. -/
def d4 : Fin 4 → Fin 4 → ℕ := ![![0, 2, 9, 10], ![1, 0, 6, 4], ![15, 7, 0, 8], ![6, 3, 12, 0]]

example : (heldKarp d4).ret = 21 := by decide
example : walkCost d4 0 [2, 3, 1] 0 = 21 := by decide

/-- Brute force: the costs of all `3!` orderings of the cities `1, 2, 3` (kernel reduction does
not unfold `List.permutations`, so they are listed explicitly). -/
example :
    ([[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] : List (List (Fin 3))).map
      (fun L => walkCost d4 0 (L.map Fin.succ) 0) = [22, 33, 26, 21, 34, 30] := by decide

example : (heldKarp d4).time = 24 := by decide
example : (heldKarp d4).time ≤ 3 ^ 2 * 2 ^ 3 := time_heldKarp_le d4

/-! ### 3. Integer costs -/

/-- A cost matrix with negative entries; the optimal tour `0 → 2 → 1 → 0` costs `-6`. -/
def dZ : Fin 3 → Fin 3 → ℤ := ![![0, 4, -2], ![-3, 0, 1], ![2, -1, 0]]

example : (heldKarp dZ).ret = -6 := by decide
example : walkCost dZ 0 [1, 2] 0 = 7 := by decide

/-! ### 4. Edge cases -/

/-- One city: the only tour is the self-loop, found without any relaxation. -/
example : (heldKarp (n := 0) fun _ _ => (7 : ℕ)).ret = 7 := by decide
example : (heldKarp (n := 0) fun _ _ => (7 : ℕ)).time = 0 := by decide

/-- The empty instance has the empty tour of length `0`. -/
example : (TSP.heldKarpDecide ([], 0)).ret = true := by decide
example : (([], 0) : List (List ℕ) × ℕ) ∈ TSP :=
  (TSP.heldKarpDecide_eq_true_iff _).1 (by decide)

/-! ### 5. Deciding `TSP` and `HamCycle` -/

/-- The three-city instance of §1 as a distance matrix: budget `3` suffices, budget `2` does not. -/
def D3 : List (List ℕ) := [[0, 1, 5], [5, 0, 1], [1, 5, 0]]

example : (D3, 3) ∈ TSP := (TSP.heldKarpDecide_eq_true_iff _).1 (by decide)
example : (D3, 2) ∉ TSP := fun h => by
  have := (TSP.heldKarpDecide_eq_true_iff _).2 h
  revert this
  decide

/-- A triangle has a Hamiltonian cycle. -/
example : (([0, 1, 2], [(0, 1), (1, 2), (2, 0)]) : Graph) ∈ HamCycle :=
  (HamCycle.heldKarpDecide_toTSP_eq_true_iff _).1 (by decide)

/-- A path on three vertices has none. -/
example : (([0, 1, 2], [(0, 1), (1, 2)]) : Graph) ∉ HamCycle := fun h => by
  have := (HamCycle.heldKarpDecide_toTSP_eq_true_iff _).2 h
  revert this
  decide

end ComplexityTests.TSPHeldKarp
