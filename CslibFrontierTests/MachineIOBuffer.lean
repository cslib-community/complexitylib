/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.OutputToTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput

/-! Buffering retains stateful effects and correctly clamps both ends of an empty virtual input. -/

namespace ComplexityTests.MachineIOBuffer

open Cslib Turing MultiTapeMachine

private def advance (direction : SignType) : MultiTapePTM 0 Bool Unit Bool where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := direction, workTapes := Fin.elim0, output := some bit, state := some () }
    (fun op => if op then some bit else none) (fun _ => -1)

private def spec : OracleSpec Unit := fun _ => Bool

private def coin : OracleComp spec Bool := OracleComp.query ()

private def countCoins : (q : Unit) → StateT ℕ Id (spec q) :=
  fun _ => modifyGet fun state => (true, state + 1)

private def initial (position : Fin 2) : Config 0 Bool Unit Bool [] :=
  { tapes := { ((advance 0).initialConfig []).tapes with inputPos := position, output := [false] }
    channels := fun _ => { queryBuffer := [false], answer := [true], answerPos := 2 } }

private def observeInput (cfg : Config 2 Bool Unit Bool [true, false]) :=
  (cfg.tapes.inputPos.val, cfg.tapes.workTapePos 0, cfg.tapes.workTapePos 1, cfg.tapes.output,
    (cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer,
    (cfg.channels true).answerPos)

-- Repeated left moves at the left end stay at -1 on both virtual tapes. The real head stays at 2.
example : (OracleComp.interpret countCoins (observeInput <$>
    (advance (-1)).inputFromTape.runConfigFrom coin (fun _ _ => pure []) 3
      (InputFromTape.config true (initial 0) [true, false] 2))).run 4 =
    ((2, -1, -1, [false, true, true, true], [false], [false, true, true, true], -1), 7) := by
  rw [MultiTapePTM.runConfigFrom_inputFromTape]
  rfl

-- At the right end of the empty input, repeated right moves stay at cell zero.
example : (OracleComp.interpret countCoins (observeInput <$>
    (advance 1).inputFromTape.runConfigFrom coin (fun _ _ => pure []) 3
      (InputFromTape.config false (initial 1) [true, false] 2))).run 4 =
    ((2, 0, 0, [false, true, true, true], [false], [false, true, true, true], -1), 7) := by
  rw [MultiTapePTM.runConfigFrom_inputFromTape]
  rfl

private def observeOutput (cfg : Config 1 Bool Unit Bool []) :=
  (cfg.tapes.output, cfg.tapes.workTapePos 0, cfg.tapes.workTapes 0 0,
    cfg.tapes.workTapes 0 1, cfg.tapes.workTapes 0 3, cfg.tapes.workTapes 0 4,
    (cfg.channels false).queryBuffer, (cfg.channels true).queryBuffer)

-- Existing output is retained in the buffer, followed by all three new bits, with no real output.
example : (OracleComp.interpret countCoins (observeOutput <$>
    (advance 0).outputToTape.runConfigFrom coin (fun _ _ => pure []) 3
      (OutputToTape.config (initial 1)))).run 4 =
    (([], 4, some false, some true, some true, none, [false], [false, true, true, true]), 7) := by
  rw [MultiTapePTM.runConfigFrom_outputToTape]
  rfl

end ComplexityTests.MachineIOBuffer
