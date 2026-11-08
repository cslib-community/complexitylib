/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Pebbling.ReversiblePath

/-!
# Reversible pebbling of the directed path

Concrete instances of Bennett's strategy and of the exact reversible prices of the directed path.
Each characterization is checked at a budget where it holds and at one where it fails, so the
lower bounds are not vacuous. The reversible rule is checked against the black rule on a single
move.
-/

namespace ComplexityTests.ReversiblePebbling

open Cslib Cslib.Pebbling

/-- Bennett's strategy on two vertices: pebble `0`, pebble `1`, remove `0`. -/
example : bennettMoves 0 1 = [.place 0, .place 1, .remove 0] := rfl

/-- Bennett's strategy on four vertices, nine moves:
`{0}, {0,1}, {1}, {1,2}, {1,2,3}, {1,3}, {0,1,3}, {0,3}, {3}`. -/
example : bennettMoves 0 2 =
    [.place 0, .place 1, .remove 0, .place 2, .place 3, .remove 2, .place 0, .remove 1,
      .remove 0] := rfl

/-- The nine moves are a run with three pebbles that ends with only vertex `3` pebbled. -/
example : (reversiblePebbleGame pathDigraph 3).MTr ∅ (bennettMoves 0 2) {3} := by
  have h := bennettMoves_mTr 2 (a := 0) (C := ∅) (by simp) fun _ hu => absurd hu pathDigraph_source
  rwa [Finset.card_empty, insert_empty_eq] at h

example : (bennettMoves 5 4).length = 81 := by simp

/-- Bennett's budget is optimal: vertex `7 = 2 ^ 3 - 1` needs exactly `4` pebbles in both forms,
and `exists_mTr_bennett` reaches it in `27` moves. -/
example : persistentReversiblePebblingPrice pathDigraph 7 = 4 :=
  persistentReversiblePebblingPrice_pathDigraph_two_pow_sub_one 3

example : reversiblePebblingPrice pathDigraph 7 = 4 :=
  reversiblePebblingPrice_pathDigraph_two_pow_sub_one 3

example : ∃ ms : List (Move ℕ), ms.length = 27 ∧
    (reversiblePebbleGame pathDigraph 4).MTr ∅ ms {7} :=
  exists_mTr_bennett 3

/-- Removing a pebble whose predecessor is unpebbled is a black move but not a reversible one. -/
example : BlackStep pathDigraph {1} (.remove 1) ∅ := by
  simpa using BlackStep.remove (G := pathDigraph) (C := {1}) (v := 1)

example : ¬ RevStep pathDigraph {1} (.remove 1) ∅ := fun h => by
  have := h.forall_adj_of_mem_iff (x := 1) (by simp) 0 (by simp)
  simp at this

/-- Three pebbles reach vertex `6` but not vertex `7`. -/
example : ReversiblePebblable pathDigraph 3 6 := by
  rw [reversiblePebblable_pathDigraph_iff]; decide

example : ¬ ReversiblePebblable pathDigraph 3 7 := by
  rw [reversiblePebblable_pathDigraph_iff]; decide

/-- Three pebbles can end holding only vertex `3`, but not only vertex `4`, and two pebbles cannot
end holding only vertex `3`. -/
example : PersistentReversiblePebblable pathDigraph 3 3 := by
  rw [persistentReversiblePebblable_pathDigraph_iff]; decide

example : ¬ PersistentReversiblePebblable pathDigraph 3 4 := by
  rw [persistentReversiblePebblable_pathDigraph_iff]; decide

example : ¬ PersistentReversiblePebblable pathDigraph 2 3 := by
  rw [persistentReversiblePebblable_pathDigraph_iff]; decide

/-- Vertex `6` has reversible price `3` and black price `2`. -/
example : reversiblePebblingPrice pathDigraph 6 = 3 := by
  rw [reversiblePebblingPrice_pathDigraph]
  exact Nat.clog_pow 2 3 Nat.one_lt_two

example : blackPebblingPrice pathDigraph 6 = 2 := blackPebblingPrice_pathDigraph_succ 5

/-- Vertex `7` has persistent reversible price `4`. -/
example : persistentReversiblePebblingPrice pathDigraph 7 = 4 := by
  rw [persistentReversiblePebblingPrice_pathDigraph]
  exact congrArg (· + 1) (Nat.clog_pow 2 3 Nat.one_lt_two)

/-- The source has every price `1`. -/
example : reversiblePebblingPrice pathDigraph 0 = 1 := by
  rw [reversiblePebblingPrice_pathDigraph]
  exact Nat.clog_pow 2 1 Nat.one_lt_two

example : persistentReversiblePebblingPrice pathDigraph 0 = 1 := by
  rw [persistentReversiblePebblingPrice_pathDigraph]
  exact congrArg (· + 1) (Nat.clog_one_right 2)

example : blackPebblingPrice pathDigraph 0 = 1 := blackPebblingPrice_pathDigraph_zero

end ComplexityTests.ReversiblePebbling
