/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Guess

/-! Clients for exact binary guessing, its clock, and its shared FreeM interpretation. -/

namespace ComplexityTests.CountingGuess

open Cslib Turing MultiTapeCTM GuessMachine

private def initial (input : List Bool) : Cfg 0 Bool Unit input :=
  Cfg.init guessMachine.initial input

-- An empty input has one singleton halt, no discarded binary choice and no zero-step halt.
example :
    guessMachine.branches 0 (initial []) = ∅ ∧
    guessMachine.branches 1 (initial []) = {[0]} ∧
    guessMachine.runBranch (initial []) [0, 0] = none ∧
    guessMachine.HaltsWithin 1 (initial []) :=
  ⟨by decide, by decide, by decide, haltsWithin []⟩

-- Both bit occurrences exist, with distinct outputs and no additional final coin, and a longer
-- mixed witness is written in chronological choice order.
example :
    guessMachine.branches 2 (initial [false]) = {[0, 0], [1, 0]} ∧
    guessMachine.branchCount (· == [false]) 2 (initial [true]) = 1 ∧
    guessMachine.branchCount (· == [true]) 2 (initial [true]) = 1 ∧
    guessMachine.branches 1 (initial [true]) = ∅ ∧
    guessMachine.runBranch (initial [true]) [2, 0] = none ∧
    guessMachine.runBranch (initial [true]) [1, 1] = none ∧
    guessMachine.runBranch (initial [true]) [1, 0, 0] = none ∧
    (guessMachine.runBranch (initial [false, false, true]) [1, 0, 1, 0]).map
      Cfg.output = some [true, false, true] ∧
    (guessMachine.branches 4 (initial [false, false, true])).card = 8 ∧
    guessMachine.branchCount (fun word => word.headD false) 4
      (initial [false, false, true]) = 4 := by
  decide

example (input : List Bool) (fuel : ℕ) (h : input.length + 1 ≤ fuel)
    (verdict : List Bool → Bool) :
    guessMachine.branchCount verdict fuel (initial input) =
      (Finset.univ.filter fun word : BitString input.length => verdict (List.ofFn word)).card := by
  unfold initial
  rw [(haltsWithin input).branchCount_eq h verdict]
  exact GuessMachine.branchCount_eq input verdict

-- The List handler preserves duplicates, singleton instructions, an empty choice list, and output
-- multiplicity.
example :
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (chooseOccurrence [true, true]) = [true, true] ∧
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (chooseOccurrence [false]) = [false] ∧
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (chooseOccurrence ([] : List Bool)) = [] ∧
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (Cfg.output <$> guessMachine.runProgram 1 (initial []))).count [] = 1 ∧
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (Cfg.output <$> guessMachine.runProgram 2 (initial [false]))).count [] = 0 :=
  ⟨interpret_chooseOccurrence _, interpret_chooseOccurrence _, interpret_chooseOccurrence _,
    by simpa [initial] using count_interpret_output [] [],
    by simpa [initial] using count_interpret_output [false] []⟩

example (input word : List Bool) (h : word.length = input.length) :
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (Cfg.output <$> guessMachine.runProgram (input.length + 1) (initial input))).count word =
      1 := by
  unfold initial
  rw [count_interpret_output, ite_eq_left h]

/--
info: 'Turing.MultiTapeCTM.interpret_chooseOccurrence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.interpret_chooseOccurrence

end ComplexityTests.CountingGuess
