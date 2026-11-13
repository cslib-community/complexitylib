/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Runs on inputs with a common prefix

A native machine receives its input through the read-only input tape, without a separate
length argument. Runs agree while the head cannot have reached the differing part of that
tape. The input position starts at one; positions zero and `input.length + 1` are blank.

## Main definitions

* `Turing.Cfg.Matches`: configurations on different inputs with identical runtime fields.

## Main results

* `Turing.MultiTapeTM.matches_runFrom_append`: extending an unread suffix preserves a run.
* `Turing.MultiTapeTM.runsInTime_append`: a run halting within the input's length also halts
  within the same bound on every extension.
-/

public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {x y : List Symbol}

/-- Equality of all runtime fields across two input-dependent configuration types. The immutable
input words may differ; the input head positions agree as natural numbers. -/
structure Cfg.Matches (a : Cfg k Symbol State x) (b : Cfg k Symbol State y) : Prop where
  /-- Equal control states, including halting. -/
  state : a.state = b.state
  /-- Equal numerical input-head positions. -/
  inputPos : a.inputPos.val = b.inputPos.val
  /-- Equal work-tape contents. -/
  workTapes : a.workTapes = b.workTapes
  /-- Equal work-head positions. -/
  workTapePos : a.workTapePos = b.workTapePos
  /-- Equal output words. -/
  output : a.output = b.output

namespace Cfg.Matches

/-- Initial configurations agree apart from their immutable input words. -/
theorem init (q : State) : Matches (Cfg.init (k := k) q x) (Cfg.init q y) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Applying the same action preserves matching configurations away from the right blank. -/
theorem apply_action {a : Cfg k Symbol State x} {b : Cfg k Symbol State y}
    (h : a.Matches b) (ha : a.inputPos.val ≤ x.length) (hb : b.inputPos.val ≤ y.length)
    (action : Action k Symbol State) : (action.apply a).Matches (action.apply b) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [Action.apply_inputPos, Action.apply_inputPos,
      val_moveInputPos_eq_moveInputPosNat, val_moveInputPos_eq_moveInputPosNat]
    have hp := h.inputPos
    rcases action.inputTape with _ | _ | _ <;>
      simp only [moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;>
      omega
  · simp only [Action.apply_workTapes, h.workTapes, h.workTapePos]
  · simp only [Action.apply_workTapePos, h.workTapePos]
  · simp only [Action.apply_output, h.output]

/-- A step preserves matching configurations when both heads are before the right blank
and currently read the same symbol. -/
theorem step {a : Cfg k Symbol State x} {b : Cfg k Symbol State y}
    (h : a.Matches b) (ha : a.inputPos.val ≤ x.length) (hb : b.inputPos.val ≤ y.length)
    (hread : a.inputSymbol = b.inputSymbol) (tm : MultiTapeTM k Symbol State) :
    (tm.step a).Matches (tm.step b) := by
  cases hs : a.state with
  | none =>
    rw [tm.step_of_halt hs, tm.step_of_halt (h.state.symm.trans hs)]
    exact h
  | some q =>
    rw [tm.step_of_state hs, tm.step_of_state (h.state.symm.trans hs)]
    have hw : a.workTapeSymbols = b.workTapeSymbols := by
      funext i
      change a.workTapes i (a.workTapePos i) = b.workTapes i (b.workTapePos i)
      rw [h.workTapes, h.workTapePos]
    rw [hread, hw]
    exact h.apply_action ha hb _

end Cfg.Matches

namespace MultiTapeTM

/-- Before a transition can inspect the first extra symbol, an extension preserves every
runtime field. A differing symbol can first be read after `x.length` steps. -/
theorem matches_runFrom_append (tm : MultiTapeTM k Symbol State) (x y : List Symbol)
    {t : ℕ} (ht : t ≤ x.length) :
    (tm.runFrom (tm.initCfg x) t).Matches (tm.runFrom (tm.initCfg (x ++ y)) t) := by
  induction t with
  | zero => exact Cfg.Matches.init _
  | succ t ih =>
    have ih := ih (by omega)
    have hp := tm.inputPos_runFrom_le (tm.initCfg x) t
    have hi : (tm.initCfg x).inputPos.val = 1 := by simp [MultiTapeNTM.initCfg, Cfg.init]
    rw [hi] at hp
    have hp' : (tm.runFrom (tm.initCfg x) t).inputPos.val ≤ x.length := by omega
    have hp'' : (tm.runFrom (tm.initCfg (x ++ y)) t).inputPos.val ≤ (x ++ y).length := by
      rw [← ih.inputPos, List.length_append]
      omega
    rw [runFrom_succ, runFrom_succ]
    apply ih.step hp' hp'' ?_ tm
    rw [Cfg.inputSymbol_eq_inputAt, Cfg.inputSymbol_eq_inputAt, ← ih.inputPos]
    unfold inputAt
    split_ifs with hz
    · rfl
    · rw [List.getElem?_append_left (by omega)]

/-- Halting within the input's length also bounds the runtime on every extension. -/
theorem runsInTime_append {tm : MultiTapeTM k Symbol State} {x y : List Symbol} {t : ℕ}
    (ht : t ≤ x.length) (h : tm.RunsInTime x t) : tm.RunsInTime (x ++ y) t := by
  apply runsInTime_iff_halted.mpr
  change (tm.runFrom (tm.initCfg (x ++ y)) t).state = none
  rw [← (matches_runFrom_append tm x y ht).state]
  exact runsInTime_iff_halted.mp h

end MultiTapeTM
end Turing
