/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting
import Complexity.Logics.Propositional.CNF.Compact.ModelCount
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

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

/-- Two used labels stay distinct even though parity merges many unused labels. -/
example : CNF.modelCount (CNF.relabel (fun v : ℕ => v % 2) [[(7, true), (42, true)]]) = 3 := by
  rw [CNF.modelCount_relabel_of_injOn _ (by
    intro a ha b hb h
    change a ∈ [7, 42] at ha
    change b ∈ [7, 42] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | norm_num at h)]
  decide

/-- Identifying two occurring variables can change a disjunction's model count. -/
example :
    CNF.modelCount ([[(0, true), (1, true)]] : CNF ℕ) = 3 ∧
    CNF.modelCount (CNF.relabel (fun _ => 0) ([[(0, true), (1, true)]] : CNF ℕ)) = 1 := by
  decide

/-- The transport theorem also applies to an empty source variable type. -/
example : CNF.modelCount (CNF.relabel (fun v => nomatch v : Empty → ℕ) []) = 1 := by
  rw [CNF.modelCount_relabel_of_injOn _ (fun v => nomatch v)]
  decide

/-- An empty support permits even a constant map from an infinite variable type. -/
example : CNF.modelCount (CNF.relabel (fun _ => 0) ([] : CNF ℕ)) = 1 := by
  rw [CNF.modelCount_relabel_of_injOn _ (by simp [CNF.vars, Set.InjOn])]
  decide

/-- Repeated first occurrences leave a gap in compact names while preserving all models. -/
example :
    CNF.compact ([[(1000000, true), (1000000, true), (7, true)]] : CNF ℕ) =
      [[(0, true), (0, true), (2, true)]] ∧
    CNF.modelCount (CNF.compact ([[(1000000, true), (1000000, true), (7, true)]] : CNF ℕ)) = 3 := by
  constructor
  · decide
  · rw [CNF.modelCount_compact]
    decide

/-- Positive guarded source counts recover the existing decision language. -/
example : [[(7, true)]] ∈ ThreeSAT :=
  SharpThreeSAT.mem_ThreeSAT_iff.mpr (by decide)

/-- Positive guarded target counts recover the existing decision language. -/
example : [[(7, true)]] ∈ ThreeSATThree :=
  SharpThreeSATThree.mem_ThreeSATThree_iff.mpr (by decide)

/-- Rejected target syntax cannot belong to the decision language, even when satisfiable. -/
example : [[(0, true), (0, true), (0, true)], [(0, true)]] ∉ ThreeSATThree := by
  rw [SharpThreeSATThree.mem_ThreeSATThree_iff]
  decide
