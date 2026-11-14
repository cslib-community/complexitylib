/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.MapOutput

namespace CslibFrontierTests.MapOutput

open Turing Turing.MultiTapeTM

private noncomputable def emit : MultiTapeTM 1 Bool Unit :=
  ofTr () (fun _ _ _ => ⟨1, fun _ => (some (some false), 1), some true, none⟩)

-- Relabeling an emitted bit does not relabel the bit physically written to a work tape.
example :
    let cfg : Cfg 1 Bool Unit [true] :=
      { Cfg.init () [true] with output := [true, false] }
    let result := (emit.mapOutput Bool.not).runFrom (cfg.mapOutput Bool.not) 1
    result.state = none ∧ result.inputPos = 2 ∧ result.workTapes 0 0 = some false ∧
      result.workTapePos 0 = 1 ∧ result.output = [false, true, false] := by
  dsimp only
  rw [runFrom_mapOutput, runFrom_one, emit, step_of_state rfl, tr_ofTr]
  simp [Action.apply, Cfg.init, Cfg.mapOutput, moveInputPos]

-- A relabeled halted machine retains its mapped output at every longer exact clock.
example (time : ℕ) :
    let cfg : Cfg 1 Bool Unit [true] :=
      { Cfg.init () [true] with state := none, output := [true, false] }
    (emit.mapOutput (fun _ => false)).runFrom (cfg.mapOutput (fun _ => false)) time =
      cfg.mapOutput (fun _ => false) := by
  dsimp only
  rw [runFrom_mapOutput, runFrom_eq_of_halt _ _ (Nat.zero_le time) rfl]
  rfl

end CslibFrontierTests.MapOutput
