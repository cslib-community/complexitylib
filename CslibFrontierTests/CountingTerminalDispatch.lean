/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalDispatch

/-! Concrete terminals use actual flag reads, suffix copying, and selected native evaluators. -/

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Turing.MultiTapeATM.CountingTerminalDispatch

namespace CountingTerminalDispatchTest

/-- The test evaluator reads the copied root bit and uses both finite selector flags. -/
public noncomputable def leaf (carry claim : Bool) : MultiTapeATM 2 Bool Unit :=
  ofTMs (fun _ => ofTr () fun _ _ work =>
    ⟨0, fun _ => (none, 0), some (((work 1).getD false ^^ carry) == claim), none⟩)
    (fun _ => false)

private def storage (flags : List Bool) : Cfg 2 Bool Unit [] :=
  { tapesCfg [] ![flags, []] 0 0 [] with inputPos := 0 }

private theorem leaf_halts (carry claim : Bool) (c : Cfg 2 Bool Unit []) :
    (leaf carry claim).HaltsWithin 1 (c.withState (some (leaf carry claim).toPTM.initial)) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, haltsWithin_succ]
  intro b
  apply haltsWithin_of_halted
  rw [leaf, next_ofTMs, step_of_state rfl]
  simp only [tr_ofTr, Turing.Action.apply]

private theorem query_result (carry claim : Bool) :
    (machine (0 : Fin 2) 1 (by decide) leaf).HaltsWithin 13
        ((storage [true, carry, claim, true, false]).withState
          (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) ∧
      ((machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 13
        ((storage [true, carry, claim, true, false]).withState
          (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) ↔
        ((true ^^ carry) == claim) = true) := by
  have h := query_spec (0 : Fin 2) 1 (by decide) leaf
    (storage [true, carry, claim, true, false]) carry claim [true, false] 1
    (by funext z; simp [storage, tapesCfg]) rfl (by funext z; simp [storage, tapesCfg]) rfl rfl
    (leaf_halts carry claim _)
  refine ⟨h.1, h.2.trans ?_⟩
  simp [leaf, AcceptsWithin, next_ofTMs, step_of_state, Turing.Action.apply, copied,
    storage, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, tapeOfList_zero]

-- True carry and false claim accept on the actual copied first index bit true.
example : (machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 13
    ((storage [true, true, false, true, false]).withState
      (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) :=
  (query_result true false).2.mpr rfl

-- Changing only the claimed answer changes acceptance of the chosen family member.
example : ¬(machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 13
    ((storage [true, true, true, true, false]).withState
      (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) :=
  fun h => Bool.false_ne_true ((query_result true true).2.mp h)

-- Changing only the carry selector also changes acceptance.
example : ¬(machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 13
    ((storage [true, false, false, true, false]).withState
      (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) :=
  fun h => Bool.false_ne_true ((query_result false false).2.mp h)

-- Even an empty index pays the copy and rewind costs before the evaluator reads its blank.
example : (machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 9
    ((storage [true, false, false]).withState
      (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) := by
  have h := query_spec (0 : Fin 2) 1 (by decide) leaf (storage [true, false, false])
    false false [] 1 (by funext z; simp [storage, tapesCfg]) rfl
    (by funext z; simp [storage, tapesCfg]) rfl rfl (leaf_halts false false _)
  apply h.2.mpr
  simp [leaf, AcceptsWithin, next_ofTMs, step_of_state, Turing.Action.apply, copied,
    storage, tapesCfg, Cfg.withState, Cfg.workTapeSymbols]

-- Constant true accepts after the three flag reads without invoking the evaluator.
example : (machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 3
    ((storage [false, false, true]).withState
      (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) := by
  exact (constant_spec (0 : Fin 2) 1 (by decide) leaf (storage [false, false, true])
    false true [] (by funext z; simp [storage, tapesCfg]) rfl rfl).2.mpr rfl

-- Constant false halts on every branch and rejects.
example : (machine (0 : Fin 2) 1 (by decide) leaf).HaltsWithin 3
      ((storage [false, true, false]).withState
        (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) ∧
    ¬(machine (0 : Fin 2) 1 (by decide) leaf).AcceptsWithin 3
      ((storage [false, true, false]).withState
        (some (machine (0 : Fin 2) 1 (by decide) leaf).toPTM.initial)) := by
  have h := constant_spec (0 : Fin 2) 1 (by decide) leaf (storage [false, true, false])
    true false [] (by funext z; simp [storage, tapesCfg]) rfl rfl
  exact ⟨h.1, fun ha => Bool.false_ne_true (h.2.mp ha)⟩

end CountingTerminalDispatchTest
