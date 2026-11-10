/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.DataStructure.ListUpdate.MoveToFront
public import Complexity.DataStructure.ListUpdate.LowerBound

/-!
# Tests for list update and move-to-front

Concrete inversion counts, move-to-front runs, the cost decomposition, adversary sequences, and
nonvacuity of the lower bound for `Complexity.DataStructure.ListUpdate`.
-/

@[expose] public section

namespace ComplexityTests.ListUpdate

open Cslib.DataStructure.Online Cslib.DataStructure.ListUpdate

/-! ### Arrangements and inversions -/

example : IsArrangement ([0, 1, 2] : List (Fin 3)) := ⟨by decide, by decide⟩

/-- A list missing an item is not an arrangement. -/
example : ¬ IsArrangement ([0, 1] : List (Fin 3)) := fun h => by
  have := h.2 2
  revert this
  decide

example : inversions ([0, 1, 2] : List (Fin 3)) [2, 1, 0] = 3 := by decide

example : inversions ([0, 1, 2] : List (Fin 3)) [1, 0, 2] = 1 := by decide

/-- Reversal attains the bound `2 * inversions ≤ n (n - 1)`. -/
example : 2 * inversions ([0, 1, 2, 3] : List (Fin 4)) [3, 2, 1, 0] = 4 * 3 := by decide

/-! ### Move-to-front runs -/

example : moveToFront (2 : Fin 3) [0, 1, 2] = [2, 0, 1] := by decide

/-- Serving `[2, 2, 1]` from `[0, 1, 2]`: positions `3`, `1`, `3`. -/
example : (mtf (Fin 3)).runMem [0, 1, 2] [2, 2, 1] = [1, 2, 0] := by decide

example : (mtf (Fin 3)).cost [0, 1, 2] [2, 2, 1] = 7 := by decide

/-- An offline schedule that reorders to `[2, 1, 0]` (`3` inversions) and then pays `1 + 1 + 2`. -/
example : (problem (Fin 3)).scheduleCost [0, 1, 2] [2, 2, 1]
    (List.replicate 3 [2, 1, 0]) = 7 := by decide

example : accessCost ([2, 2, 1] : List (Fin 3)) (List.replicate 3 [2, 1, 0]) = 4 := by decide

example : exchangeCost ([0, 1, 2] : List (Fin 3)) [2, 2, 1]
    (List.replicate 3 [2, 1, 0]) = 3 := by decide

/-- The Sleator–Tarjan bound on this instance: `7 + inversions + 3 ≤ 2 * 4 + 3 + 0`. -/
example : (mtf (Fin 3)).cost [0, 1, 2] [2, 2, 1] +
      inversions ((mtf (Fin 3)).runMem [0, 1, 2] [2, 2, 1]) [2, 1, 0] + 3 ≤
    2 * accessCost ([2, 2, 1] : List (Fin 3)) (List.replicate 3 [2, 1, 0]) +
      exchangeCost ([0, 1, 2] : List (Fin 3)) [2, 2, 1] (List.replicate 3 [2, 1, 0]) +
      inversions ([0, 1, 2] : List (Fin 3)) [0, 1, 2] :=
  mtf_cost_add_inversions_add_length_le ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    (validSchedule_static (τ := [2, 1, 0]) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ [2, 2, 1])

example : (mtf (Fin 3)).IsCompetitive 2 0 := mtf_isCompetitive

example : (mtf (Fin 3)).IsCompetitiveAnyInit 2 3 := by
  simpa using (mtf_isCompetitiveAnyInit (α := Fin 3))

/-! ### The cruel adversary -/

/-- Against move-to-front from `[0, 1, 2]` the cruel adversary requests `2`, `1`, `0`. -/
example : cruelRequests 0 (mtf (Fin 3)) [0, 1, 2] 3 = [2, 1, 0] := by decide

/-- Every request costs move-to-front `n = 3`. -/
example : (mtf (Fin 3)).cost [0, 1, 2] (cruelRequests 0 (mtf (Fin 3)) [0, 1, 2] 3) = 9 := by
  decide

/-- The static schedule on `[0, 1, 2]` costs `3 + 2 + 1 = 6` on the same requests. -/
example : (problem (Fin 3)).scheduleCost [0, 1, 2] [2, 1, 0] (List.replicate 3 [0, 1, 2]) = 6 := by
  decide

/-! ### Deterministic lower bound -/

/-- No deterministic strategy over three items is `(1, b)`-competitive. -/
example (A : DetStrategy (problem (Fin 3))) (b : Nat) : ¬ A.IsCompetitive 1 b :=
  not_isCompetitive_one A (by simp) b

/-- The rational ratio `7/5 < 3/2 = 2n/(n+1)` is violated by every deterministic strategy over
three items, including move-to-front. -/
example (b : Nat) : ∃ reqs states, (problem (Fin 3)).ValidSchedule [0, 1, 2] reqs states ∧
    7 * (problem (Fin 3)).scheduleCost [0, 1, 2] reqs states + b <
      5 * (mtf (Fin 3)).cost [0, 1, 2] reqs :=
  exists_ratio_violation_of_lt (mtf (Fin 3)) ⟨by decide, by decide⟩ (by simp) b

end ComplexityTests.ListUpdate
