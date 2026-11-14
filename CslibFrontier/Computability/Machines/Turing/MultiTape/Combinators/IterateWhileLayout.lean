/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate
-- Extracted unchanged from crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
import Mathlib.Tactic.FinCases

/-!
# Tape layout for iterate-while machines

Deterministic and probabilistic iterate-while machines share a current-word tape, a next-word
tape and a flag tape. The copy and emit embeddings and the intermediate word layout are
independent of the machine's choice semantics and of its alphabet.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*}

namespace IterateWhile

section Tapes

variable (k)

/-- The tape holding the current word: the input tape of `Turing.MultiTapeTM.onWords`. -/
abbrev curTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 0

/-- The tape holding the next word: the output tape of `Turing.MultiTapeTM.onWords`. -/
abbrev nextTape : Fin (k + 1 + 2) := (Fin.last k).castAdd 2

/-- The flag tape of `Turing.MultiTapeTM.onWords`. -/
abbrev flagTape : Fin (k + 1 + 2) := Fin.natAdd (k + 1) 1

/-- The tapes of `Turing.MultiTapeTM.copyWord`: from the next tape to the current tape, flagged on
the flag tape. -/
@[expose] def copyEmb : Fin (0 + 1 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, nextTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢ <;> omega⟩

/-- The tapes of `Turing.MultiTapeTM.emitWord`: the current tape, flagged on the flag tape. -/
@[expose] def emitEmb : Fin (0 + 2) ↪ Fin (k + 1 + 2) :=
  ⟨![curTape k, flagTape k], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [Fin.ext_iff] at h ⊢⟩

end Tapes

@[simp] lemma copyEmb_zero : copyEmb k 0 = curTape k := rfl
@[simp] lemma copyEmb_one : copyEmb k 1 = nextTape k := rfl
@[simp] lemma copyEmb_two : copyEmb k 2 = flagTape k := rfl
@[simp] lemma emitEmb_zero : emitEmb k 0 = curTape k := rfl
@[simp] lemma emitEmb_one : emitEmb k 1 = flagTape k := rfl

lemma curTape_ne_nextTape : curTape k ≠ nextTape k := Fin.ne_of_val_ne (by simp)

lemma flagTape_ne_nextTape : flagTape k ≠ nextTape k :=
  Fin.ne_of_val_ne (by simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]; omega)

lemma flagTape_ne_curTape : flagTape k ≠ curTape k := Fin.ne_of_val_ne (by simp)

/-- The words between two phases: `vc` on the current tape, `vn` on the next tape, all other
tapes blank. -/
@[expose] def words (vc vn : List Symbol) : Fin (k + 1 + 2) → List Symbol :=
  Function.update (Function.update (fun _ => []) (curTape k) vc) (nextTape k) vn

@[simp]
lemma words_cur (vc vn : List Symbol) : words (k := k) vc vn (curTape k) = vc := by
  simp [words, curTape_ne_nextTape]

@[simp]
lemma words_next (vc vn : List Symbol) : words (k := k) vc vn (nextTape k) = vn := by
  simp [words]

@[simp]
lemma words_flag (vc vn : List Symbol) : words (k := k) vc vn (flagTape k) = [] := by
  simp [words, flagTape_ne_nextTape, flagTape_ne_curTape]

lemma update_words_cur (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (curTape k) v = words v vn := by
  rw [words, Function.update_comm curTape_ne_nextTape.symm, Function.update_idem, ← words]

lemma update_words_next (vc vn v : List Symbol) :
    Function.update (words (k := k) vc vn) (nextTape k) v = words vc v := by
  rw [words, Function.update_idem, ← words]

lemma words_nil_next (v : List Symbol) :
    words (k := k) v [] = Function.update (fun _ => []) (curTape k) v :=
  Function.update_eq_self_iff.mpr (by simp [curTape_ne_nextTape.symm])

lemma words_nil_cur (v : List Symbol) :
    words (k := k) [] v = Function.update (fun _ => []) (nextTape k) v := by
  rw [words, Function.update_eq_self]

lemma words_nil_nil : words (k := k) (Symbol := Symbol) [] [] = fun _ => [] := by
  rw [words_nil_next, Function.update_eq_self]

end IterateWhile

end Turing.MultiTapeTM
