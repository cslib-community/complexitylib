/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of local input-query replay)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySpace

/-!
# Local replay boundary and update regressions

A transition records the queried input symbol on its work tape. Both input boundaries must mask
that symbol. Writes distinguish erasing a cell from leaving it unchanged, and halted native
control still consumes the subroutine's duration counter.
-/

@[expose] public section

namespace ComplexityTests.QueryReplay

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay

/-- Read once, write the symbol, emit an accepting bit and halt. -/
def reader : MultiTapeTM 1 Bool Unit := MultiTapeTM.ofTr () fun _ input _ =>
    { inputTape := .zero, workTapes := fun _ => (some input, .zero),
      output := some true, state := none }

def state (pos : ℕ) : Config 1 Unit :=
  ⟨1, 1, 1, pos, some (), fun _ => 1, fun _ => [0, 1, 0], .empty⟩

example : (tick reader (state 0) (some true)).cells 0 = [0, 0, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
example : (tick reader (state 1) (some true)).cells 0 = [0, 2, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
example : (tick reader (state 2) (some true)).cells 0 = [0, 0, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
example : (tick reader (state 1) (some true)).track = .accept := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
example : (tick reader { state 1 with track := .accept } (some true)).track = .other := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide

example : (applyAction (state 1)
    { inputTape := .neg, workTapes := fun _ => (none, .zero), output := none,
      state := none }).cells 0 = [0, 1, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
example : (applyAction (state 1)
    { inputTape := .neg, workTapes := fun _ => (some none, .zero), output := none,
      state := none }).cells 0 = [0, 0, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  decide

example : (tick reader { state 1 with control := none, remaining := 2 } (some true)).remaining
    = 1 := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
example : (tick reader { state 1 with control := none, remaining := 2 } (some true)).cells 0
    = [0, 1, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
example : ((machine reader).runFrom [true] (state 1) 1).cells 0 = [0, 2, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
example : ((machine reader).runFrom [true] (state 0) 1).cells 0 = [0, 0, 0] := by
  dsimp [tick, reader, state, applyAction,
    MultiTapeNTM.ConfigurationGraph.inputSymbol, MultiTapeNTM.ConfigurationGraph.inputMove,
    machine, QueryMachine.runFrom, QueryMachine.step]
  simp only [MultiTapeTM.tr_ofTr]
  decide
/-- The same concrete replay is certified with its actual binary local-window encoding. -/
example : ComputableInSpace (machine reader).next
    (encPair encConfig (encOption encBool)) encConfig
    (fun p => (encPair encConfig (encOption encBool) p).length) :=
  machine_next_inSpace reader

example : (encConfig (state 1)).length ≤ 1024 * (1 + 1) *
    (1 + Nat.log2 1 + Nat.card (Option Unit) +
      Nat.card MultiTapeNTM.ChoiceTable.OutputTrack + 1) := by
  apply length_encConfig_le <;> decide

end ComplexityTests.QueryReplay
