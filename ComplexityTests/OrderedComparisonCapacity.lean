/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Leaves

/-! Concrete clients of exact ordered query-activity capacity. -/

open Cslib Cslib.DecisionTree

-- A depth-three, energy-one tree distinguishing four consecutive scalar values.
-- Equality at a query threshold must take the true branch.
private def fourValues : DecisionTree ℕ ℕ :=
  .node 13 (.node 12 (.node 11 (.leaf 10) (.leaf 11)) (.leaf 12)) (.leaf 13)

example : fourValues.leafCount = 4 ∧ fourValues.depth = 3 ∧ fourValues.energy = 1 := by
  decide

example : ∀ j : Fin 4,
    fourValues.eval (fun k => decide (k ≤ 10 + j.val)) = 10 + j.val := by
  decide

-- The constructive direction realizes all eleven values at the exact capacity B(4, 2).
example : ∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 11 ∧ t.depth ≤ 4 ∧ t.energy ≤ 2 ∧
      ∀ j : Fin 11, t.eval (fun k => decide (k ≤ 37 + j.val)) = 37 + j.val := by
  obtain ⟨t, hc, hd, he, hv⟩ :=
    (exists_orderedComparisonTree_iff 4 2 11 37).mpr (by decide)
  exact ⟨t, hc, hd, he, fun j => hv j.val j.isLt⟩

-- One more output is impossible at those same resource bounds, even with offset zero.
example : ¬∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 12 ∧ t.depth ≤ 4 ∧ t.energy ≤ 2 ∧
      ∀ j < 12, t.eval (fun k => decide (k ≤ 0 + j)) = 0 + j := by
  rw [exists_orderedComparisonTree_iff]
  decide

-- Zero depth still allows one reachable leaf, regardless of the energy budget.
example : ∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 1 ∧ t.depth ≤ 0 ∧ t.energy ≤ 7 ∧
      t.eval (fun k => decide (k ≤ 19)) = 19 := by
  obtain ⟨t, hc, hd, he, hv⟩ :=
    (exists_orderedComparisonTree_iff 0 7 1 19).mpr (by decide)
  exact ⟨t, hc, hd, he, by simpa using hv 0 (by decide)⟩

-- Zero energy permits only one leaf, even with unused depth available.
example : ¬∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 2 ∧ t.depth ≤ 5 ∧ t.energy ≤ 0 ∧
      ∀ j < 2, t.eval (fun k => decide (k ≤ 8 + j)) = 8 + j := by
  rw [exists_orderedComparisonTree_iff]
  decide

-- The theorem also handles energy greater than depth: the capacity saturates at 2^q.
example : ∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 4 ∧ t.depth ≤ 2 ∧ t.energy ≤ 5 ∧
      ∀ j : Fin 4, t.eval (fun k => decide (k ≤ j.val)) = j.val := by
  obtain ⟨t, hc, hd, he, hv⟩ :=
    (exists_orderedComparisonTree_iff 2 5 4 0).mpr (by decide)
  exact ⟨t, hc, hd, he, fun j => by simpa using hv j.val j.isLt⟩

-- The positivity condition is necessary, not a convention about empty input intervals.
example : ¬∃ t : DecisionTree ℕ ℕ,
    t.leafCount = 0 ∧ t.depth ≤ 3 ∧ t.energy ≤ 2 ∧
      ∀ j < 0, t.eval (fun k => decide (k ≤ 5 + j)) = 5 + j := by
  rw [exists_orderedComparisonTree_iff]
  decide
