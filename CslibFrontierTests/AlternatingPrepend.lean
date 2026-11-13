/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Prepend
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Deterministic

open Turing Turing.MultiTapeATM

private def prepare : MultiTapeTM 1 Bool Unit :=
  MultiTapeTM.ofTr () (fun _ _ _ => ⟨0, fun _ => (some (some true), 0), none, none⟩)

private noncomputable def leaf (player : Bool) : MultiTapeATM 1 Bool Unit :=
  ofTMs (fun b => MultiTapeTM.ofTr () (fun _ _ work =>
    ⟨0, fun _ => (none, 0), some (b && work 0 == some true), none⟩)) (fun _ => player)

private def start : Cfg 1 Bool Unit [] :=
  ⟨none, 0, fun _ _ => none, fun _ => 0, []⟩

private def finish : Cfg 1 Bool Unit [] :=
  ⟨none, 0, fun _ => Function.update (fun _ => none) 0 (some true), fun _ => 0, []⟩

private theorem prepare_run : prepare.runFrom (start.withState (some ())) 3 = finish := by
  have h : prepare.step (start.withState (some ())) = finish := by
    rw [MultiTapeTM.step_of_state rfl, prepare, MultiTapeTM.tr_ofTr]
    rfl
  rw [show 3 = 1 + 2 from rfl, MultiTapeTM.runFrom_add]
  change prepare.runFrom (prepare.step _) 2 = _
  rw [h]
  exact MultiTapeTM.runFrom_eq_of_halt prepare finish (show 0 ≤ 2 by decide) rfl

private theorem leaf_step (player b : Bool) :
    (leaf player).next b (finish.withState (some ())) = { finish with output := [b] } := by
  rw [leaf, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  cases b <;> simp [finish, Cfg.withState, Action.apply, Cfg.workTapeSymbols]

private theorem leaf_halts (player : Bool) :
    (leaf player).HaltsWithin 1 (finish.withState (some ())) := by
  simp only [haltsWithin_succ, leaf_step, haltsWithin_zero]
  exact fun _ => rfl

private theorem leaf_accepts (player : Bool) :
    (leaf player).AcceptsWithin 1 (finish.withState (some ())) ↔ player = false := by
  simp only [AcceptsWithin, Cfg.withState_state]
  change (if player then ∀ b, _ else ∃ b, _) ↔ _
  simp only [leaf_step]
  cases player <;> simp [finish]

-- A one-step prefix supplied with a padded clock of three still preserves both players.
example (player : Bool) :
    let atm := prependTM prepare (leaf player)
    atm.HaltsWithin 4 (start.withState (some atm.toPTM.toNTM.q₀)) ∧
      (atm.AcceptsWithin 4 (start.withState (some atm.toPTM.toNTM.q₀)) ↔ player = false) := by
  obtain ⟨hh, ha⟩ := prependTM_spec prepare (leaf player) start finish 3 1
    prepare_run (leaf_halts player)
  exact ⟨hh, ha.trans (leaf_accepts player)⟩

-- Nonblank extra tapes at nonzero cursors do not change existential or universal semantics.
example (player : Bool) :
    ((leaf player).extendTapes (Fin.castAddEmb 1)).AcceptsWithin 1
      (MultiTapeTM.embed (Fin.castAddEmb 1) (finish.withState (some ()))
        (fun _ _ => some false) (fun _ => 37)) ↔ player = false := by
  rw [acceptsWithin_embed_iff, leaf_accepts]
