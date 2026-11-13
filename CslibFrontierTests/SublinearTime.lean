/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Complexity.Classes.Time.Sublinear

/-! # Sublinear-time boundary clients

An actual one-step machine reads the first bit, so constant-time behavior need not be constant
as a function. Prefix agreement includes the step at the prefix's length. The empty-input
case demonstrates why unrestricted extension invariance would be false.
-/

open Turing Turing.MultiTapeTM

private def firstBitTM : MultiTapeTM 0 Bool Unit :=
  .ofTr () fun _ bit _ =>
    { state := none, inputTape := 0, workTapes := fun i => i.elim0,
      output := some (bit.getD false) }

private theorem firstBitTM_run (x : List Bool) :
    (firstBitTM.runFrom (firstBitTM.initCfg x) 1).Halted ∧
      (firstBitTM.runFrom (firstBitTM.initCfg x) 1).output = [x.headD false] := by
  rw [runFrom_succ]
  rw [show firstBitTM.runFrom (firstBitTM.initCfg x) 0 = firstBitTM.initCfg x from rfl]
  rw [firstBitTM.step_of_state (q := ()) rfl]
  cases x with
  | nil => simp [firstBitTM, tr_ofTr, Cfg.inputSymbol, MultiTapeNTM.initCfg, Action.apply]
  | cons b xs =>
    simp [firstBitTM, tr_ofTr, Cfg.inputSymbol, MultiTapeNTM.initCfg, Action.apply]

private theorem firstBit_computable :
    ComputableInTimeAndSpace (fun x : List Bool => x.headD false) encBits encBool
      (fun _ => 1) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, firstBitTM, fun x => ?_⟩
  have hr := firstBitTM_run x
  exact ⟨⟨1, hr.1, hr.2⟩, runsInTime_iff_halted.mpr hr.1,
    MultiTapeNTM.runsInSpace_zero_tapes _ _ _⟩

-- Full function-computability endpoint, with the same zero-space bound and nonconstant output.
example :
    (∃ C, ComputableInTimeAndSpace (fun x : List Bool => x.headD false) encBits encBool
      (fun _ => C) (fun _ => 0)) ∧
    ([true].headD false ≠ ([] : List Bool).headD false) := by
  refine ⟨firstBit_computable.exists_const_time_of_isLittleO (p := fun _ => 1) ?_, by decide⟩
  convert (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop using 1 <;> simp

-- Inclusive boundary: one step on a one-bit prefix is still preserved on its extension.
example : (firstBitTM.runFrom (firstBitTM.initCfg [true]) 1).output =
    (firstBitTM.runFrom (firstBitTM.initCfg [true, false]) 1).output :=
  (matches_runFrom_append firstBitTM [true] [false] (by decide)).output

-- One step exceeds the empty prefix's length and can distinguish the added symbol.
example : (firstBitTM.runFrom (firstBitTM.initCfg []) 1).output ≠
    (firstBitTM.runFrom (firstBitTM.initCfg [true]) 1).output := by
  rw [(firstBitTM_run []).2, (firstBitTM_run [true]).2]
  decide

-- Even a zero asymptotic bound denotes constant time because DTIME includes affine offsets.
example : Cslib.Complexity.DTIME encBits (fun _ => 0) =
    Cslib.Complexity.DTIME encBits (fun _ => 1) := by
  apply Cslib.Complexity.DTIME_eq_const_of_isLittleO
  convert (Asymptotics.isLittleO_const_id_atTop (0 : ℝ)).natCast_atTop using 1 <;> simp
