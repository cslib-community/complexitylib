/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TruthTable

import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Local

namespace CslibFrontierTests.TruthTable

open Turing Turing.MultiTapeATM

private noncomputable def child (p : Fin 7) (bit : Bool) : MultiTapeATM 1 Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ work =>
    ⟨0, fun _ => (none, 0), some ((decide (p.val = 0) == bit) && work 0 == some true), none⟩))
    (fun _ => false)

private def store (tape : ℤ → Option Bool) (pos : ℤ) : Cfg 1 Bool Unit [] :=
  ⟨none, 0, fun _ => tape, fun _ => pos, []⟩

private theorem child_next (tape : ℤ → Option Bool) (pos : ℤ) (h : tape pos = some true)
    (p : Fin 7) (bit move : Bool) :
    (child p bit).next move ((store tape pos).withState (some ())) =
      { store tape pos with output := [decide (p.val = 0) == bit] } := by
  rw [child, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [Action.apply, store, Cfg.withState, Cfg.workTapeSymbols, h]

/-- An arbitrary pre-existing tape and nonzero cursor survive all ten dispatch moves: the
continuation still observes the original true sentinel. Both true and false claims are tested. -/
example (tape : ℤ → Option Bool) (h : tape 37 = some true) (carry claim : Bool) :
    (TruthTable.machine (fun v => (Cslib.Circuits.Boolean.CarrySaveLocal.formula carry).eval
      Cslib.Circuits.Boolean.interpretation v) claim child).AcceptsWithin 11
      ((store tape 37).withState (some .guess₀)) ↔ claim = !carry := by
  rw [TruthTable.acceptsWithin_eval _ _ _ 1 (store tape 37) rfl
    (fun p => decide (p.val = 0))]
  · cases carry <;> simp [Cslib.Circuits.Boolean.CarrySaveLocal.eval_formula,
      Cslib.Circuits.Boolean.maj3, eq_comm]
  · intro p b
    rw [acceptsWithin_succ_of_existential _ rfl rfl]
    simp only [show (child p b).toPTM.toNTM.q₀ = () from rfl, child_next tape 37 h]
    simp [AcceptsWithin, store]

/-- Rejection and the dummy eighth universal port are included in the eleven-step time bound. -/
example (tape : ℤ → Option Bool) (h : tape 37 = some true) (carry claim : Bool) :
    (TruthTable.machine (fun v => (Cslib.Circuits.Boolean.CarrySaveLocal.formula carry).eval
      Cslib.Circuits.Boolean.interpretation v) claim child).HaltsWithin 11
      ((store tape 37).withState (some .guess₀)) := by
  apply TruthTable.haltsWithin _ _ _ 1 (store tape 37)
  intro p b
  apply haltsWithin_succ.mpr
  intro move
  rw [show (child p b).toPTM.toNTM.q₀ = () from rfl, child_next tape 37 h]
  apply haltsWithin_of_halted
  rfl

end CslibFrontierTests.TruthTable
