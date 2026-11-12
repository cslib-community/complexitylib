/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Deterministic

open Turing Turing.MultiTapeATM

private def readBit : MultiTapeTM 1 Bool Unit :=
  MultiTapeTM.ofTr () (fun _ _ work =>
    ⟨0, fun _ => (none, 0), some (work 0 == some true), none⟩)

private def storage (bit : Bool) (out : List Bool) : Cfg 1 Bool Unit [] :=
  ⟨some (), 0, fun _ _ => some bit, fun _ => 37, out⟩

private theorem run_readBit (bit : Bool) (out : List Bool) :
    readBit.runFrom (storage bit out) 1 =
      { storage bit out with state := none, output := out ++ [bit] } := by
  change readBit.step (storage bit out) = _
  rw [MultiTapeTM.step_of_state rfl, readBit, MultiTapeTM.tr_ofTr]
  cases bit <;> simp [storage, Action.apply, Cfg.workTapeSymbols]

-- Both existential and universal labels give the same exact native answer at a nonzero cursor.
example (bit player : Bool) :
    (ofTMs (fun _ => readBit) (fun _ => player)).AcceptsWithin 1 (storage bit []) ↔
      bit = true := by
  rw [acceptsWithin_ofTMs_const_iff, run_readBit]
  simp

example (bit player : Bool) :
    (ofTMs (fun _ => readBit) (fun _ => player)).HaltsWithin 1 (storage bit []) := by
  rw [haltsWithin_ofTMs_const_iff, run_readBit]

-- A previous output bit cannot silently disappear in the lifting theorem.
example (player : Bool) :
    ¬ (ofTMs (fun _ => readBit) (fun _ => player)).AcceptsWithin 1
      (storage true [false]) := by
  rw [acceptsWithin_ofTMs_const_iff, run_readBit]
  simp

example (bit player : Bool) :
    ¬ (ofTMs (fun _ => readBit) (fun _ => player)).HaltsWithin 0 (storage bit []) := by
  rw [haltsWithin_ofTMs_const_iff]
  simp [MultiTapeTM.runFrom, storage]
