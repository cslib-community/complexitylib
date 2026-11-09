/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.ChoiceTable
import Mathlib.Tactic.FinCases

/-! The parsimonious bridge retains duplicate occurrences and forces every padding bit.
Width two includes unused local codes and a final partial block. -/

namespace ComplexityTests.CountingChoice

open _root_.Turing _root_.Turing.MultiTapeTM

private def stop : MultiTapeMachine.Action 0 Bool Unit Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }
    Empty.elim Empty.elim

private def double : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [stop, stop]

private theorem halts (input : List Bool) :
    double.HaltsWithin 1 (Cfg.init double.initial input) := by
  apply MultiTapeCTM.HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index <;> exact .halt rfl

private theorem count (input : List Bool) :
    double.acceptCount 1 (Cfg.init double.initial input) = 2 := by
  change double.branchCount (· == [true]) _ _ = 2
  rw [(halts input).branchCount_eq_countP, MultiTapeCTM.runList_succ _ _ 0 () rfl]
  simp [MultiTapeCTM.actions, double, stop, MultiTapeMachine.Action.emptyOracleEquiv,
    Turing.Action.apply, Cfg.init]

/-- Two identical accepting occurrences give two accepting strings even after long padding. -/
example (input : List Bool) :
    (MultiTapeCTM.CountingChoice.table (by decide : 0 < 1) double).acceptCount input 7 = 2 := by
  rw [MultiTapeCTM.CountingChoice.acceptCount_table_of_halts (by decide) double input
    (by intro cfg; cases hs : cfg.state <;> simp [MultiTapeCTM.actions, hs, double])
    (halts input) (by decide), count]

/-- With width two, invalid codes reject and the odd final bit has exactly one valid value. -/
example (input : List Bool) :
    (MultiTapeCTM.CountingChoice.table (by decide : 0 < 2) double).acceptCount input 7 = 2 := by
  rw [MultiTapeCTM.CountingChoice.acceptCount_table_of_halts (by decide) double input
    (by intro cfg; cases hs : cfg.state <;> simp [MultiTapeCTM.actions, hs, double])
    (halts input) (by decide), count]

end ComplexityTests.CountingChoice
