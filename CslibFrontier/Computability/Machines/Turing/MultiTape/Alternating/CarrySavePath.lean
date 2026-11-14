/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveStream
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PreparePath
import Mathlib.Tactic.FinCases

/-!
# Physical candidate-path preparation inside the streamed evaluator

The persistent path on controller tape 2 is reverse-copied to private tape 6, using private
tape 7 as a temporary marker. The other controller tapes and their head positions are preserved.
The space bound counts visited cells during this phase, including one cell on each of the five
unused tapes; it does not assert a bound on the pre-existing controller contents.
-/

public section

namespace Turing.MultiTapeATM.CarrySavePath

open MultiTapeTM

/-- Destination, persistent source, and temporary marker in the eight-tape layout. -/
def tapes : Fin 3 ↪ Fin 8 where
  toFun := ![6, 2, 7]
  inj' := by decide

/-- The concrete path preparation phase in the streamed evaluator's layout. -/
noncomputable def machine := PreparePath.machine.extendTapes tapes

/-- The resulting configuration changes only the candidate tape and the persistent path cursor. -/
def prepared {input : List Bool} (cfg : Cfg 8 Bool Unit input) (path : List Bool) :
    Cfg 8 Bool Unit input :=
  { cfg with
    workTapes := Function.update cfg.workTapes 6 (tapeOfList path.reverse)
    workTapePos := Function.update cfg.workTapePos 2 0 }

private theorem view_config {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    viewCfg tapes (CarrySaveStream.config (k := 2) (input := input)
      height bits path unary frontier status) = PreparePath.initial input path [] := by
  have ht := CarrySaveStream.config_path_tape (scratch := CarrySaveStream.Scratch.blank 2)
    (input := input) height bits path unary frontier status
  have hp := CarrySaveStream.config_path_head (scratch := CarrySaveStream.Scratch.blank 2)
    (input := input) height bits path unary frontier status
  change (CarrySaveStream.config (k := 2) height bits path unary frontier status).workTapes 2 =
    tapeOfList path at ht
  change (CarrySaveStream.config (k := 2) height bits path unary frontier status).workTapePos 2 =
    path.length at hp
  simp only [CarrySaveStream.Scratch.blank] at ht hp
  apply Cfg.ext
  · simp [viewCfg, PreparePath.initial_eq, tapesCfg]
  · simp [viewCfg, PreparePath.initial_eq, tapesCfg]
  · funext j
    fin_cases j <;>
      simp [viewCfg, tapes, PreparePath.initial_eq, tapesCfg, ht,
        CarrySaveStream.config_extra_tape, CarrySaveStream.Scratch.blank]
  · funext j
    fin_cases j <;>
      simp [viewCfg, tapes, PreparePath.initial_eq, tapesCfg, hp,
        CarrySaveStream.config_extra_head, CarrySaveStream.Scratch.blank]
  · simp [viewCfg, PreparePath.initial_eq, tapesCfg]

private theorem partialInv_tapes (i : Fin 8) :
    partialInv tapes i = ![none, none, some 1, none, none, none, some 0, some 2] i := by
  fin_cases i
  all_goals first
    | exact partialInv_embed tapes 0
    | exact partialInv_embed tapes 1
    | exact partialInv_embed tapes 2
    | apply partialInv_eq_none; rintro ⟨j, hj⟩; fin_cases j <;> simp [tapes] at hj

/-- A physical leaf phase prepares candidate digits from the actual persistent controller path. -/
theorem runsBetween {input : List Bool} (height bits path unary : List Bool)
    (frontier : ℤ) (status : Bool) :
    let cfg := CarrySaveStream.config (k := 2) (input := input)
      height bits path unary frontier status
    RunsBetween machine cfg (prepared cfg path) (4 * path.length + 12)
      (7 * path.length + 44) := by
  dsimp only
  let cfg := CarrySaveStream.config (k := 2) (input := input)
    height bits path unary frontier status
  have hp := PreparePath.runsBetween input path []
  rw [← view_config height bits path unary frontier status] at hp
  have h := hp.extendTapes (c := cfg) tapes
  have hout : embed tapes (PreparePath.final input path []) cfg.workTapes cfg.workTapePos =
      prepared cfg path := by
    have hv := view_config (input := input) height bits path unary frontier status
    have ht (j : Fin 3) := congrArg (fun c => c.workTapes j) hv
    have hp (j : Fin 3) := congrArg (fun c => c.workTapePos j) hv
    apply Cfg.ext
    · simp [embed, PreparePath.final_eq, prepared, tapesCfg, cfg]
    · simp [embed, PreparePath.final_eq, prepared, tapesCfg, cfg]
    · funext i
      fin_cases i <;>
        simp [embed, partialInv_tapes, PreparePath.final_eq, tapesCfg, prepared]
      · simpa [PreparePath.initial_eq, viewCfg, tapes, tapesCfg, cfg] using (ht 1).symm
      · simpa [PreparePath.initial_eq, viewCfg, tapes, tapesCfg, cfg] using (ht 2).symm
    · funext i
      fin_cases i <;>
        simp [embed, partialInv_tapes, PreparePath.final_eq, tapesCfg, prepared]
      · simpa [PreparePath.initial_eq, viewCfg, tapes, tapesCfg, cfg] using (hp 0).symm
      · simpa [PreparePath.initial_eq, viewCfg, tapes, tapesCfg, cfg] using (hp 2).symm
    · simp [embed, PreparePath.final_eq, prepared, tapesCfg, cfg]
  rw [hout] at h
  exact h

end Turing.MultiTapeATM.CarrySavePath
