/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of CslibFrontier.Computability.Pebbling.Descending)

public import CslibFrontier.Computability.Pebbling.Descending

/-! # Evaluating a descending computation along a pebbling walk

The computation on indices `0, 1, 2, 3` with source `1` and gates adding the values at `i - 1` and
`i - 2` (the second child of `1` is `0`) has values `1, 2, 3, 5`. A walk of indicator words with
three pebbles places `0, 1, 2`, drops `0`, places `3` and drops `1` and `2`; following it with
`tableStep` ends with the value `5` of index `3`. The legality of every move is checked by
`decide`, and the correctness theorem then yields the value without unfolding the tables. -/

@[expose] public section

namespace CslibFrontierTests.PebblingDescending

open Cslib.BitString Cslib.Pebbling Cslib.Pebbling.Descending

/-- Children `i - 1` and `i - 2`. -/
def child (i : ℕ) (a : Fin 2) : ℕ := if a = 0 then i - 1 else i - 2

/-- Each gate adds its two arguments. -/
def gates (_ : ℕ) (x : Fin 2 → ℕ) : ℕ := x 0 + x 1

/-- The values of the computation. -/
def value (i : ℕ) : ℕ := [1, 2, 3, 5].getD i 0

/-- The walk of indicator words. -/
def walk (j : ℕ) : List Bool :=
  [[false, false, false, false], [true, false, false, false], [true, true, false, false],
    [true, true, true, false], [false, true, true, false], [false, true, true, true],
    [false, false, true, true], [false, false, false, true]].getD j []

/-- The tables along the walk, with room for three entries. -/
def tables : ℕ → List (ℕ × ℕ)
  | 0 => []
  | j + 1 => tableStep child gates 1 3 (walk j) (walk (j + 1)) (tables j)

theorem child_lt : ∀ i, 0 < i → ∀ a, child i a < i := by
  intro i hi a
  unfold child
  split_ifs <;> omega

theorem value_succ : ∀ i, 0 < i → i < 4 → value i = gates i fun a => value (child i a) := by
  have h : ∀ i < 4, 0 < i → value i = gates i fun a => value (child i a) := by decide
  exact fun i hi h4 => h i h4 hi

-- Every step of the walk is a legal move with at most three pebbles, and it ends at `{3}`.
theorem walk_legal : ∀ j < 7, walk j = walk (j + 1) ∨
    wordStep (ready child) 3 (walk j) (walk (j + 1)) = true := by
  decide

theorem walk_end : walk 7 = indicatorList ({3} : Finset (Fin 4)) := by
  rw [indicatorList_singleton]
  decide

-- The correctness theorem returns the value of index `3`.
example : lookupD (tables 7) 3 = 5 :=
  lookupD_eq_of_tableStep (N := 4) child gates 1 child_lt rfl value_succ walk tables 7
    (by decide) rfl walk_legal rfl (fun _ _ => rfl) (v := 3) walk_end

-- The same value, computed directly; the table never holds more than three entries.
example : lookupD (tables 7) 3 = 5 ∧ ∀ j ≤ 7, (tables j).length ≤ 3 := by
  decide

-- The dependency graph is a DAG of in-degree at most two.
example : WellFounded (graph (N := 4) child).Adj ∧
    ∀ v : Fin 4, {u | (graph child).Adj u v}.ncard ≤ 2 :=
  ⟨wellFounded_graph child child_lt, ncard_graph_adj_le child⟩

end CslibFrontierTests.PebblingDescending
