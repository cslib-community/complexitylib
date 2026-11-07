/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of physical local-replay space bounds)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayBounds
public import ComplexityTests.Machines.Turing.MultiTape.QueryReplay

/-!
# Actual replay storage bounds

A nontrivial three-window view starts at the left input boundary. Its head residues and
canonical cell codes instantiate the all-clock bounds before and after replay halts.
-/

@[expose] public section

namespace ComplexityTests.QueryReplayBounds

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay

def view : View 1 Unit 2 :=
  ((some (), fun _ => 1, .empty), fun _ port residue =>
    if port = 0 then none else some (residue = 0))

def origin : Option (Fin 1) → ℤ := fun _ => -1

example (w : List Bool) (clock : ℕ) :
    (encConfig ((machine QueryReplay.reader).runFrom w
      (loadView w.length 2 origin view) clock)).length ≤
        1024 * (1 + 1) * (2 + Nat.log2 w.length + Nat.card (Option Unit) +
          Nat.card MultiTapeNTM.ChoiceTable.OutputTrack + 1) :=
  length_runFrom_loadView_le _ _ _ _ _ _

example (w : List Bool) (clock : ℕ) :
    (encRawResult (rawResult ((machine QueryReplay.reader).runFrom w
      (loadView w.length 2 origin view) clock))).length ≤
        128 * (1 + 1) * (2 + Nat.card (Option Unit) +
          Nat.card MultiTapeNTM.ChoiceTable.OutputTrack + 1) :=
  length_rawResult_runFrom_loadView_le _ _ _ _ _ _

example : (loadView 3 2 origin view).inputPos = 0 := by decide
example : ((machine QueryReplay.reader).runFrom [true] (loadView 1 2 origin view) 2).remaining
    = 0 := by rw [remaining_runFrom]; rfl
example : (machine QueryReplay.reader).runFrom [true] (loadView 1 2 origin view) 100 =
    (machine QueryReplay.reader).runFrom [true] (loadView 1 2 origin view) 2 := by
  exact runFrom_loadView_min QueryReplay.reader [true] 2 origin view 100

end ComplexityTests.QueryReplayBounds
