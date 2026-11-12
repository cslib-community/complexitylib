/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation

open Turing Turing.MultiTapeATM

namespace CslibFrontierTests.StateSimulation

private noncomputable def source : MultiTapeATM 1 Bool (Fin 2) :=
  ofTMs (fun _ => MultiTapeTM.ofTr 0 (fun _ _ _ =>
    ⟨0, fun _ => (none, 0), some true, none⟩)) (fun _ => false)

private noncomputable def target : MultiTapeATM 1 Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ _ =>
    ⟨0, fun _ => (none, 0), some true, none⟩)) (fun _ => false)

-- Two distinct native control states collapse to one. The proof requires no injectivity.
private def collapse : StateSimulation source target where
  stateMap _ := ()
  universal_eq _ := rfl
  next_eq c b := by
    cases hs : c.state with
    | none => rw [next_of_halted _ (by simp [hs]), next_of_halted _ hs]
    | some q =>
      rw [source, target, next_ofTMs, next_ofTMs,
        MultiTapeTM.step_of_state (q := ()) (by simp [hs]), MultiTapeTM.step_of_state hs]
      simp [MultiTapeTM.tr_ofTr, Action.apply, Cfg.mapState]

example : ¬ Function.Injective collapse.stateMap := by
  intro h
  have := h (a₁ := 0) (a₂ := 1) rfl
  contradiction

example {input : List Bool} (cfg : Cfg 1 Bool (Fin 2) input) (n : ℕ) :
    target.AcceptsWithin n (cfg.mapState (Option.map collapse.stateMap)) ↔
      source.AcceptsWithin n cfg := collapse.acceptsWithin_iff n cfg

example {input : List Bool} (cfg : Cfg 1 Bool (Fin 2) input) (n : ℕ) :
    target.HaltsWithin n (cfg.mapState (Option.map collapse.stateMap)) ↔
      source.HaltsWithin n cfg := collapse.haltsWithin_iff n cfg

end CslibFrontierTests.StateSimulation
