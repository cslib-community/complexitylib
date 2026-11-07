/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native replay result extraction and input scanning)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.InputLength
public import ComplexityTests.Machines.Turing.MultiTape.QueryReplay

/-!
# Native replay access

The scan starts with a fixed counter and finds empty and nonempty input lengths. Result
extraction checks the negative input coordinate at the left blank boundary, zero width and
work-head residues. Its native certificate uses the same concrete representation as replay.
-/

@[expose] public section

namespace ComplexityTests.QueryReplayAccess

open Turing MultiTapeTM MultiTapePTM.BlockComputation.QueryReplay

example : QueryMachine.InputLength.machine.run [] 1 = (0, true) := rfl
example : QueryMachine.InputLength.machine.run [false, true, false] 4 = (3, true) := rfl
example : QueryMachine.InputLength.machine.run [false, true, false] 10 = (3, true) := rfl
example (w : List Bool) :
    (QueryMachine.InputLength.encState
      (QueryMachine.InputLength.machine.run w (w.length + 100))).length ≤
        2 * (Nat.log2 w.length + 1) + 2 := QueryMachine.InputLength.length_run_le _ _

example : inputResidue 4 0 = 3 := rfl
example : inputResidue 4 1 = 0 := rfl
example : inputResidue 4 6 = 1 := rfl
example : inputResidue 0 100 = 0 := rfl
example : workResidue 4 9 = 1 := rfl

example : (rawResult { QueryReplay.state 0 with width := 4 }).2.1 none = 3 := rfl
example : (rawResult { QueryReplay.state 1 with width := 4, heads := fun _ => 9 }).2.1
    (some 0) = 1 := rfl
example : (rawResult { QueryReplay.state 0 with width := 0 }).2.1 none = 0 := rfl

/-- Every field of the extracted raw result is realized using the actual binary state. -/
example : ComputableInSpace (rawResult (k := 1) (Q := Unit)) encConfig encRawResult
    (fun s => (encConfig s).length) := rawResult_inSpace

/-- Native extraction bridges to the same semantic leaving-view interface. -/
example : (rawResult { QueryReplay.state 0 with width := 4 }).toView 4 =
    result 4 { QueryReplay.state 0 with width := 4 } := toView_rawResult _ _ rfl

/-- Invalid absolute input coordinates use the existing embedding's blank-left convention. -/
example : (loadView (k := 0) (Q := Unit) 3 1 (fun _ => -100)
    ((some (), fun _ => 0, .empty), Fin.elim0)).inputPos = 0 := by decide

end ComplexityTests.QueryReplayAccess
