/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reading and moving the input head

Two machines with one work tape that leave the input head where a two-way computation needs it:
`peekInput` writes the symbol under the input head into the first two cells of the word on its
work tape, without moving the input head, and `moveInput` moves the input head by the move written
at the start of the word on its work tape.

## Main definitions

* `Turing.MultiTapeTM.peekInput`, `Turing.MultiTapeTM.moveInput`: the machines.

## Main results

* `Turing.MultiTapeTM.TransformsTapesAt.tapeEmb`: a one-tape specification on tape `i`.
* `Turing.MultiTapeTM.transformsTapesAt_peekInput`,
  `Turing.MultiTapeTM.transformsTapesAt_moveInput`: their specifications.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- **A one-tape specification on tape `i`**, for a machine that may move the input head. -/
public theorem TransformsTapesAt.tapeEmb {tm : MultiTapeTM 1 Symbol State}
    {P : (input : List Symbol) → Fin (input.length + 2) → (Fin 1 → List Symbol) → Prop}
    {Q : (input : List Symbol) → Fin (input.length + 2) → (Fin 1 → List Symbol) →
      Fin (input.length + 2) → (Fin 1 → List Symbol) → List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapesAt tm P Q t s) (i : Fin k) :
    TransformsTapesAt (tm.extendTapes (MultiTapeTM.tapeEmb i))
      (fun input p ws => P input p fun _ => ws i)
      (fun input p ws p' ws' emitted =>
        ∃ v, Q input p (fun _ => ws i) p' v emitted ∧ ws' = Function.update ws i (v 0))
      t (s + (k - 1)) := by
  intro input p ws out hP
  obtain ⟨p', v, emitted, hrun, hQ, hspace⟩ := h input p (fun _ => ws i) out hP
  simp only [wordsCfgAt] at hrun hspace
  refine ⟨p', Function.update ws i (v 0), emitted, ?_, ⟨v, hQ, rfl⟩, ?_⟩
  · rw [extendTapes_q₀, runFrom_tapeEmb]
    simp only [oneTapeCfg, wordsCfgAt, hrun]
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [hl]
  · rw [extendTapes_q₀]
    exact (space_tapeEmb_le _ _ _ _).trans (Nat.add_le_add_right hspace _)

/-! ### Reading the symbol under the input head -/

/-- The word that records the symbol `a` under the input head: whether it is a symbol, and the
symbol. -/
@[expose] public def peekWord (a : Option Bool) : List Bool := [a.isSome, a.getD false]

/-- The states of `peekInput`: before writing the first and the second cell. -/
public inductive PeekState
  | first | second

public instance : Finite PeekState :=
  Finite.of_surjective (fun b : Bool => if b then PeekState.first else .second)
    fun q => by cases q; exacts [⟨true, rfl⟩, ⟨false, rfl⟩]

/-- Writes `peekWord` of the symbol under the input head into the first two cells of its work
tape, moving the input head nowhere. -/
public def peekInput : MultiTapeTM 1 Bool PeekState :=
  ofTr .first fun q inp _ =>
    match q with
    | .first =>
      { inputTape := 0, workTapes := fun _ => (some (some inp.isSome), 1), output := none,
        state := some .second }
    | .second =>
      { inputTape := 0, workTapes := fun _ => (some (some (inp.getD false)), -1), output := none,
        state := none }

lemma tapeOfList_update_two (x₀ x₁ y₀ y₁ : Bool) (w : List Bool) :
    Function.update (Function.update (tapeOfList (x₀ :: x₁ :: w)) 0 (some y₀)) 1 (some y₁) =
      tapeOfList (y₀ :: y₁ :: w) := by
  funext z
  rcases z with (_ | _ | n) | n <;> simp [Function.update_apply] <;> rfl

/-- **Reading the symbol under the input head**: `peekInput` replaces the first two cells of the
word on its tape by `peekWord` of the symbol under the input head, which it does not move. -/
public theorem transformsTapesAt_peekInput :
    TransformsTapesAt peekInput (fun _ _ ws => 2 ≤ (ws 0).length)
      (fun input p ws p' ws' e => p' = p ∧
        ws' 0 = peekWord (inputSymbolAt input p) ++ (ws 0).drop 2 ∧ e = []) 2 2 := by
  intro input p ws out hlen
  obtain ⟨x₀, x₁, w, hw⟩ : ∃ x₀ x₁ w, ws 0 = x₀ :: x₁ :: w := by
    match h : ws 0, hlen with
    | x₀ :: x₁ :: w, _ => exact ⟨x₀, x₁, w, rfl⟩
  set a := inputSymbolAt input p
  have h₁ : peekInput.runFrom (wordsCfgAt input p (some peekInput.q₀) ws out) 1 =
      ⟨some .second, p, fun _ => Function.update (tapeOfList (ws 0)) 0 (some a.isSome),
        fun _ => 1, out⟩ := by
    rw [runFrom_one, step_of_state rfl, inputSymbol_eq_inputSymbolAt]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> (try funext _) <;>
      simp [peekInput, Action.apply, wordsCfgAt, a, Fin.fin_one_eq_zero]
  have h₂ : peekInput.runFrom (wordsCfgAt input p (some peekInput.q₀) ws out) 2 =
      wordsCfgAt input p none (Function.update ws 0 (peekWord a ++ w)) out := by
    rw [show 2 = 1 + 1 from rfl, runFrom_add, h₁, runFrom_one, step_of_state rfl,
      inputSymbol_eq_inputSymbolAt]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> (try funext j) <;>
      simp [peekInput, Action.apply, wordsCfgAt, a, Fin.fin_one_eq_zero, hw, peekWord,
        tapeOfList_update_two]
  refine ⟨p, Function.update ws 0 (peekWord a ++ w), [], by rw [h₂, List.append_nil],
    ⟨rfl, by simp [hw, a], rfl⟩, ?_⟩
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := {0, 1}) fun m hm => ?_).trans (by decide)
  rcases m with _ | _ | m
  · simp [runFrom, wordsCfgAt]
  · simp [h₁]
  · obtain rfl : m = 0 := by omega
    rw [show 0 + 1 + 1 = 2 from rfl, h₂]
    simp [wordsCfgAt]

/-! ### Moving the input head -/

/-- The move written as the first cell of a word: none, to the left, or to the right. -/
@[expose] public def moveOfCell : Option Bool → SignType
  | none => 0
  | some false => -1
  | some true => 1

/-- Moves the input head by `moveOfCell` of the cell under its work-tape head, in one step. -/
public def moveInput : MultiTapeTM 1 Bool Unit :=
  ofTr () fun _ _ work =>
    { inputTape := moveOfCell (work 0), workTapes := fun _ => (none, 0), output := none,
      state := none }

/-- **Moving the input head**: `moveInput` moves the input head by the move at the start of the
word on its tape, and changes nothing else. -/
public theorem transformsTapesAt_moveInput :
    TransformsTapesAt moveInput (fun _ _ _ => True)
      (fun _ p ws p' ws' e => p' = moveInputPos p (moveOfCell (ws 0).head?) ∧ ws' = ws ∧ e = [])
      1 1 := by
  rintro input p ws out -
  have h₁ : moveInput.runFrom (wordsCfgAt input p (some moveInput.q₀) ws out) 1 =
      wordsCfgAt input (moveInputPos p (moveOfCell (ws 0).head?)) none ws out := by
    rw [runFrom_one, step_of_state rfl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> (try funext _) <;>
      simp [moveInput, Action.apply, wordsCfgAt, Cfg.workTapeSymbols, tapeOfList_zero,
        Fin.fin_one_eq_zero]
  refine ⟨_, ws, [], by rw [h₁, List.append_nil], ⟨rfl, rfl, rfl⟩, ?_⟩
  exact space_le_of_workTapePos_const _ _ fun m hm => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · rfl
    · rw [h₁]; rfl

end Turing.MultiTapeTM
