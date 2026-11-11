/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes

/-! Nontrivial tape embeddings retain scratch data, channels, and stateful coin effects. -/

namespace CslibFrontierTests.MachineExtendTapes

open Cslib Turing MultiTapeMachine

private def writeCoin : MultiTapePTM 1 Bool Unit Bool where
  initial := ()
  tr _ _ _ _ coin := .step
    { inputTape := 0, workTapes := fun _ => (some coin, 1), output := some coin, state := none }
    (fun op => some op) (fun _ => -1)

private def spec : OracleSpec Unit := fun _ => Bool

private def coin : OracleComp spec Bool := OracleComp.query ()

private def countCoins : (q : Unit) → StateT ℕ Id (spec q) :=
  fun _ => modifyGet fun state => (true, state + 1)

private def initial : Config 1 Bool Unit Bool [] :=
  { writeCoin.initialConfig [] with
    channels := fun _ => { queryBuffer := [false], answer := [true], answerPos := 2 } }

private def extraTapes : Fin 3 → ℤ → Option Bool := fun _ _ => some false

private def extraPos : Fin 3 → ℤ := fun _ => -3

private def observe (cfg : Config 3 Bool Unit Bool []) :=
  (cfg.tapes.output, cfg.tapes.state, cfg.tapes.workTapes 0 17, cfg.tapes.workTapePos 0,
    cfg.tapes.workTapes 1 0, cfg.tapes.workTapePos 1,
    cfg.tapes.workTapes 2 (-9), cfg.tapes.workTapePos 2,
    (cfg.channels true).queryBuffer, (cfg.channels true).answerPos)

-- Tape 1 is active; tapes 0 and 2 retain nonblank data and negative heads. One coin is counted.
example : (OracleComp.interpret countCoins
    (observe <$> (writeCoin.extendTapes (MultiTapeTM.tapeEmb (1 : Fin 3))).runConfigFrom
      coin (fun _ _ => pure []) 5
      (initial.embed (MultiTapeTM.tapeEmb (1 : Fin 3)) extraTapes extraPos))).run 4 =
    (([true], none, some false, -3, some true, 1, some false, -3, [false, true], 1), 5) := by
  rw [MultiTapePTM.runConfigFrom_embed]
  change (observe (Config.embed _ _ _ _), 5) = _
  simp [observe, Config.embed, MultiTapeTM.embed_tapeEmb,
    extraTapes, extraPos, initial, Config.step, Turing.Action.apply,
    initialConfig, Cfg.init]

end CslibFrontierTests.MachineExtendTapes
