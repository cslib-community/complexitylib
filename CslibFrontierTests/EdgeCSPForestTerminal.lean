/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Terminal

/-! Lemma 34 on real partial scans and the terminal star that must lose all its children. -/

namespace CslibFrontierTests.EdgeCSPForestTerminal

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest
open Cslib.Logic.PL.CSP.DAG

private def sem (r : Bool) : List Bool → Bool
  | [a, b, c] => !r &&
      ([[false, false, false], [true, true, false], [true, false, true]].contains [a, b, c])
  | [a] => a == r
  | _ => false

private abbrev star : CSP Bool ℕ :=
  [(false, [0, 1, 2]), (true, [0]), (false, [1]), (true, [2])]

private def labels : star.OccurrenceLabeling Bool :=
  fun o => o.1.val == 1 || o.1.val == 3

private abbrev port (j : Fin 3) : star.Occurrence := ⟨0, j⟩

private theorem edge : EdgeInstance star := by unfold EdgeInstance; decide
private theorem valid : ValidLabeling sem labels := by unfold ValidLabeling; decide

private def terminal : Meeting star :=
  ⟨[0, 2], [], ⟨port 0, [port 1]⟩, port 2⟩

private theorem actual : search sem labels = .augment terminal := by decide +kernel

-- The first expansion stops after inserting child one and meeting root two, at timestamp zero.
example : terminal.current.outputs = [port 1] ∧ terminal.copy.2 = 0 := by decide

example : terminal.toDAG.IsFDAG sem labels ∧ terminal.prunedDAG.IsFDAG sem labels := by
  have hh := search_terminal_isFDAG sem labels edge valid
  simpa only [actual, Result.Events] using hh

-- Child one is isolated after pruning, rather than being deleted from the variable support.
example : 1 ∈ terminal.prunedDAG.vars ∧
    ∀ a ∈ terminal.prunedDAG.arcs, a.occurrence.var ≠ 1 := by decide

-- Keeping that child's outgoing arc would require the infeasible tuple 011.
example : ¬ ValidLabeling sem (pairFlip labels (port 2) (port 1)) := by
  unfold ValidLabeling
  decide

-- Every prefix of the actual feasible-partner list, including the empty partial expansion,
-- satisfies all six conditions. No even-delta-matroid premise is supplied here.
example (n : ℕ) :
    (Log.toDAG (roots labels)
      [⟨port 0, (scan (roots labels) [] (port 0) []
        ((partners sem labels (port 0)).take n)).outputs⟩]).IsFDAG sem labels := by
  apply scan_isFDAG edge valid Grown.nil (by decide) (by decide)
  exact fun _ hm => List.mem_of_mem_take hm

-- The terminal graph contains exactly two incoming ports and no outgoing port at the copy.
example : terminal.prunedDAG.arcs =
    {⟨port 2, 0, true⟩, ⟨port 0, 0, true⟩} := by decide

end CslibFrontierTests.EdgeCSPForestTerminal
