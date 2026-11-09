/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Pebbling.ReversiblePathReachable

/-!
# Reachable configurations of reversible pebbling on the path

Concrete instances of the Li–Tromp–Vitányi characterization. `decide` runs the greedy test, so each
reachability claim below is checked by the kernel through Corollary 1. Reachable and unreachable
configurations are paired at the same budget, including unreachable ones whose pebbles each satisfy
the per-pebble bound, so the characterization says more than that bound. A removal numbering is
written out by hand, and the bounds of `ReversiblePath.lean` are rederived from the new bound.
-/

namespace ComplexityTests.ReversiblePathReachable

open Cslib Cslib.Pebbling

/-- Three pebbles reach `{3, 5, 6}`: remove `6` (from `5`, with no free pebble), then `5` (from
`3`, with one), then `3` (from the start, with two). -/
example : ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {3, 5, 6} :=
  exists_reversiblePebbleGame_pathDigraph_mTr_iff.2 (by decide)

/-- Three pebbles do not reach `{3, 6}`, although both `3` and `6` lie in the reachable
configuration `{3, 5, 6}`. Nor do they reach `{6}`. -/
example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {3, 6} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {6} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

/-- Two pebbles do not reach `{0, 2}`, although both pebbles satisfy the bound
`v + 1 + 2 ^ f ≤ 2 ^ n` with no free pebble; `{1, 2}` is reachable. -/
example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 2).MTr ∅ ms {0, 2} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

example : ∀ v ∈ ({0, 2} : Finset ℕ), v + 1 + 2 ^ (2 - 2) ≤ 2 ^ 2 := by decide

example : ∃ ms, (reversiblePebbleGame pathDigraph 2).MTr ∅ ms {1, 2} :=
  exists_reversiblePebbleGame_pathDigraph_mTr_iff.2 (by decide)

/-- With three pebbles, `{0, 4}` is unreachable but `{3, 4}` is reachable, although `{4}` alone
cannot be the final configuration. -/
example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {0, 4} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

example : ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {3, 4} :=
  exists_reversiblePebbleGame_pathDigraph_mTr_iff.2 (by decide)

example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {4} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

/-- Four pebbles reach `{7, 11, 13, 14}` but not `{7, 11, 13, 15}`. -/
example : ∃ ms, (reversiblePebbleGame pathDigraph 4).MTr ∅ ms {7, 11, 13, 14} :=
  exists_reversiblePebbleGame_pathDigraph_mTr_iff.2 (by decide)

example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 4).MTr ∅ ms {7, 11, 13, 15} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

/-- More pebbles than the budget: `{0, 1, 2, 3}` is not reachable with three pebbles. -/
example : ¬ ∃ ms, (reversiblePebbleGame pathDigraph 3).MTr ∅ ms {0, 1, 2, 3} := by
  rw [exists_reversiblePebbleGame_pathDigraph_mTr_iff]; decide

/-- An explicit removal numbering of `{3, 5, 6}` with three pebbles: `6 ↦ 0`, `5 ↦ 1`, `3 ↦ 2`. -/
example : IsPathRemovalNumbering 3 {3, 5, 6} (fun x => if x = 6 then 0 else if x = 5 then 1 else 2)
    where
  injOn := by decide
  le := by decide
  lt := by decide
  near := by decide

/-- The bound with free pebbles gives back the visiting bound of `ReversiblePath.lean`. -/
example {n v : ℕ} {ms : List (Move ℕ)} {C : Finset ℕ}
    (h : (reversiblePebbleGame pathDigraph n).MTr ∅ ms C) (hv : v ∈ C) : v + 2 ≤ 2 ^ n := by
  have := add_one_add_two_pow_le_of_reversiblePebbleGame_pathDigraph_mTr h hv
  have := Nat.one_le_two_pow (n := n - C.card)
  omega

/-- … and, for `C = {v}`, the persistent bound. -/
example {n v : ℕ} {ms : List (Move ℕ)} (h : (reversiblePebbleGame pathDigraph n).MTr ∅ ms {v}) :
    2 * (v + 1) ≤ 2 ^ n := by
  have := add_one_add_two_pow_le_of_reversiblePebbleGame_pathDigraph_mTr h
    (Finset.mem_singleton_self v)
  rw [Finset.card_singleton] at this
  cases n with
  | zero => omega
  | succ n =>
    rw [Nat.add_sub_cancel, pow_succ] at this
    rw [pow_succ]
    omega

/-- Theorem 1 on an instance: `{3, 5, 6}` is strongly solvable with three pebbles, so removing the
available pebble `5` first still leaves a weakly solvable configuration. -/
example : PathStronglySolvable 3 {3, 5, 6} :=
  (show PathWeaklySolvable 3 {3, 5, 6} by decide).pathStronglySolvable

example : ¬ PathWeaklySolvable 3 {3, 6} := by decide

/-- The greedy test is a Boolean function and evaluates directly. -/
example : pathGreedySolvable 3 3 {3, 5, 6} = true := by decide

example : pathGreedySolvable 3 2 {3, 6} = false := by decide

end ComplexityTests.ReversiblePathReachable
