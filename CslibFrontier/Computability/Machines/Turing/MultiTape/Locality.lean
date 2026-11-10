/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Locality of a step

A step of a multi-tape machine reads the cells under its heads, writes at most the cells under
its work heads, and moves every head by at most one cell. This file records these facts in the
form used to cut a computation into local pieces.

The heads are indexed by `Option (Fin k)`: `none` is the read-only input head and `some i` the
head of work tape `i`. `Turing.Cfg.headPos` places them in coordinates where every head starts at
zero; the input head's stored position `inputPos` is shifted by one, so its coordinate ranges over
`[-1, n]` on an input of length `n`. The write-only output tape is never read and has no head
here.

Two configurations *agree on* a family `W` of work-tape cells (`Turing.Cfg.AgreeOn`) when they have
the same control state and head positions and the same work-tape contents on `W`. If the work
heads lie in `W`, a step reads the same symbols in both, takes the same action, and preserves
agreement on `W`; both append the same symbol, if any, to their outputs
(`Turing.MultiTapeTM.agreeOn_step`). Contents outside `W` and earlier outputs may differ.

## Main definitions

* `Turing.Cfg.headPos`: head positions, starting at zero.
* `Turing.Cfg.AgreeOn`: same control and heads, and same work-tape contents on given cells.

## Main results

* `Turing.MultiTapeNTM.Step.abs_headPos_sub_le`: a step moves every head by at most one cell.
* `Turing.MultiTapeTM.agreeOn_step`: agreement on cells containing the work heads is preserved
  by a step, which emits the same output in both configurations.
-/

public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The position of a head, in coordinates where every head starts at zero: the input head
(`none`) at its stored position shifted by one, and the head of work tape `i` (`some i`). -/
@[expose] def Cfg.headPos (cfg : Cfg k Symbol State input) : Option (Fin k) → ℤ
  | none => (cfg.inputPos.val : ℤ) - 1
  | some i => cfg.workTapePos i

@[simp] theorem Cfg.headPos_none (cfg : Cfg k Symbol State input) :
    cfg.headPos none = (cfg.inputPos.val : ℤ) - 1 := rfl

@[simp] theorem Cfg.headPos_some (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.headPos (some i) = cfg.workTapePos i := rfl

/-- Every head starts at zero. -/
theorem Cfg.headPos_init (q₀ : State) (head : Option (Fin k)) :
    (Cfg.init q₀ input : Cfg k Symbol State input).headPos head = 0 := by
  cases head with
  | none => simp [Cfg.headPos]
  | some i => rfl

/-- The input head is at a coordinate in `[-1, n]` on an input of length `n`. -/
theorem Cfg.headPos_none_mem_Icc (cfg : Cfg k Symbol State input) :
    cfg.headPos none ∈ Set.Icc (-1) (input.length : ℤ) := by
  have := cfg.inputPos.isLt
  simp only [headPos_none, Set.mem_Icc]
  omega

/-- An action moves every head by at most one cell. -/
theorem Action.abs_headPos_apply_sub_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (head : Option (Fin k)) :
    |(action.apply cfg).headPos head - cfg.headPos head| ≤ 1 := by
  cases head with
  | none =>
    have hmove := val_moveInputPos_eq cfg.inputPos action.inputTape
    have hlt := cfg.inputPos.isLt
    have hcast : (action.inputTape.cast : ℤ) = -1 ∨ (action.inputTape.cast : ℤ) = 0 ∨
        (action.inputTape.cast : ℤ) = 1 := by
      rcases action.inputTape with _ | _ | _ <;> simp [SignType.cast]
    simp only [Cfg.headPos_none, Action.apply_inputPos, abs_le]
    omega
  | some i => exact workTapePos_apply_le action cfg i

/-- **A step moves every head by at most one cell.** -/
theorem MultiTapeNTM.Step.abs_headPos_sub_le {ntm : MultiTapeNTM k Symbol State}
    {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (head : Option (Fin k)) :
    |c'.headPos head - c.headPos head| ≤ 1 := by
  unfold MultiTapeNTM.Step at h
  split at h
  · simp [h]
  · obtain ⟨action, -, rfl⟩ := h
    exact action.abs_headPos_apply_sub_le c head

/-- Two configurations agree on the work-tape cells `W`: they have the same control state, the
same input and work head positions, and the same work-tape contents on `W`. Their outputs and
their contents outside `W` are unconstrained. -/
structure Cfg.AgreeOn (W : Fin k → Set ℤ) (c c' : Cfg k Symbol State input) : Prop where
  /-- The same control state. -/
  state_eq : c.state = c'.state
  /-- The same input head position. -/
  inputPos_eq : c.inputPos = c'.inputPos
  /-- The same work head positions. -/
  workTapePos_eq : c.workTapePos = c'.workTapePos
  /-- The same work-tape contents on `W`. -/
  workTapes_eq : ∀ i, ∀ z ∈ W i, c.workTapes i z = c'.workTapes i z

/-- A configuration agrees with itself on every family of cells. -/
theorem Cfg.AgreeOn.refl (W : Fin k → Set ℤ) (c : Cfg k Symbol State input) : c.AgreeOn W c :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem Cfg.AgreeOn.symm {W : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') : c'.AgreeOn W c :=
  ⟨h.state_eq.symm, h.inputPos_eq.symm, h.workTapePos_eq.symm,
    fun i z hz => (h.workTapes_eq i z hz).symm⟩

theorem Cfg.AgreeOn.trans {W : Fin k → Set ℤ} {c c' c'' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') (h' : c'.AgreeOn W c'') : c.AgreeOn W c'' :=
  ⟨h.state_eq.trans h'.state_eq, h.inputPos_eq.trans h'.inputPos_eq,
    h.workTapePos_eq.trans h'.workTapePos_eq,
    fun i z hz => (h.workTapes_eq i z hz).trans (h'.workTapes_eq i z hz)⟩

/-- Agreement on more cells is agreement on fewer. -/
theorem Cfg.AgreeOn.mono {W W' : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') (hW : ∀ i, W' i ⊆ W i) : c.AgreeOn W' c' :=
  ⟨h.state_eq, h.inputPos_eq, h.workTapePos_eq, fun i z hz => h.workTapes_eq i z (hW i hz)⟩

/-- Agreeing configurations are at the same head positions. -/
theorem Cfg.AgreeOn.headPos_eq {W : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') : c.headPos = c'.headPos := by
  funext head
  cases head with
  | none => simp [h.inputPos_eq]
  | some i => simp [h.workTapePos_eq]

/-- Agreement on cells containing the work heads gives the same read symbols. -/
theorem Cfg.AgreeOn.workTapeSymbols_eq {W : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') (hpos : ∀ i, c.workTapePos i ∈ W i) :
    c.workTapeSymbols = c'.workTapeSymbols := by
  funext i
  simp only [Cfg.workTapeSymbols, ← h.workTapePos_eq]
  exact h.workTapes_eq i _ (hpos i)

/-- One action applied to agreeing configurations keeps them agreeing on `W`: it writes the same
symbols under the same heads. -/
theorem Cfg.AgreeOn.apply {W : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') (action : Action k Symbol State) :
    (action.apply c).AgreeOn W (action.apply c') := by
  refine ⟨rfl, by simp [h.inputPos_eq], by funext i; simp [h.workTapePos_eq], fun i z hz => ?_⟩
  simp only [Action.apply_workTapes, ← h.workTapePos_eq]
  cases (action.workTapes i).1 with
  | none => exact h.workTapes_eq i z hz
  | some s =>
    by_cases hz' : z = c.workTapePos i
    · simp [hz']
    · simp only [Function.update_of_ne hz']
      exact h.workTapes_eq i z hz

/-- **Locality of a step.** If two configurations agree on cells `W` containing their work
heads, one step keeps them agreeing on `W`, and both append the same word to their outputs. -/
theorem MultiTapeTM.agreeOn_step (tm : MultiTapeTM k Symbol State) {W : Fin k → Set ℤ}
    {c c' : Cfg k Symbol State input} (h : c.AgreeOn W c') (hpos : ∀ i, c.workTapePos i ∈ W i) :
    (tm.step c).AgreeOn W (tm.step c') ∧
      ∃ e, (tm.step c).output = c.output ++ e ∧ (tm.step c').output = c'.output ++ e := by
  cases hs : c.state with
  | none =>
    have hs' : c'.state = none := h.state_eq ▸ hs
    rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.step_of_halt hs']
    exact ⟨h, [], by simp, by simp⟩
  | some q =>
    have hs' : c'.state = some q := h.state_eq ▸ hs
    have hread : c.inputSymbol = c'.inputSymbol := by
      simp only [Cfg.inputSymbol, h.inputPos_eq]
    rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hs', hread,
      h.workTapeSymbols_eq hpos]
    exact ⟨h.apply _, _, Action.apply_output _ _, Action.apply_output _ _⟩

end Turing
