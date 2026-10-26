/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting

/-! # Exact counts under occurrence splitting and numbering -/

open Cslib.Logic.PL Cslib.Complexity

/-- The empty formula has one assignment on its empty variable set. -/
example : (toThreeSATThree []).modelCount = 1 := by
  rw [modelCount_toThreeSATThree _ (by simp)]
  decide

/-- An empty clause has no satisfying assignment. -/
example : (toThreeSATThree [[]]).modelCount = 0 := by
  rw [modelCount_toThreeSATThree _ (by simp)]
  decide

/-- Repeated literals within a clause do not multiply the satisfying-assignment count. -/
example : (toThreeSATThree [[(0, true), (0, true), (0, true)]]).modelCount = 1 := by
  rw [modelCount_toThreeSATThree _ (by simp)]
  decide

/-- A singleton cycle introduces no additional choice for a forced variable. -/
example : (toThreeSATThree [[(7, true)]]).modelCount = 1 := by
  rw [modelCount_toThreeSATThree _ (by simp)]
  decide

/-- Several occurrences per variable preserve all three satisfying assignments of a disjunction. -/
example : (toThreeSATThree
    [[(0, true), (1, true)], [(0, true), (1, true)]]).modelCount = 3 := by
  rw [modelCount_toThreeSATThree _ (by simp)]
  decide

/-- The unnumbered splitter preserves counts even beyond width three. -/
example : (CNF.toThreeOccurrence
    [[(0, true), (0, false), (0, true), (0, false)]]).modelCount = 2 := by
  rw [CNF.modelCount_toThreeOccurrence]
  decide

/-- The numbered reduction rejects a width-four input, so its width hypothesis is necessary. -/
example : (toThreeSATThree
    [[(0, true), (0, false), (0, true), (0, false)]]).modelCount = 0 := by
  decide

/-- A satisfiable width-four formula has raw models but is rejected by the 3SAT count. -/
example : SharpThreeSAT [[(0, true), (0, false), (0, true), (0, false)]] = 0 := by decide

/-- The source count accepts width three even when the occurrence bound fails. -/
example : SharpThreeSAT [[(0, true), (0, true), (0, true)], [(0, true)]] = 1 := by decide

/-- The target count rejects the same formula for its fourth literal occurrence. -/
example : SharpThreeSATThree [[(0, true), (0, true), (0, true)], [(0, true)]] = 0 := by decide

/-- The actual compiler preserves that source count after repairing the occurrence bound. -/
example : SharpThreeSATThree
    (toThreeSATThree [[(0, true), (0, true), (0, true)], [(0, true)]]) = 1 := by
  rw [sharpThreeSATThree_toThreeSATThree]
  decide
