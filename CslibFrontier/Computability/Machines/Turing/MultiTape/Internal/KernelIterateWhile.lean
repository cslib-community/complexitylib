/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- The newer version of cslib PR #1112 @0b9e55ce, which is on an older base.
-- vendored: the loop states are `State ⊕ Unit`, those of `repeatUntilBlank` since cslib #1151

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhileLayout
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Order.Interval.Finset.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RepeatUntilBlank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The existing iterate-while machine and its fixed-machine run law

Machine programs, tape layouts and resource formulas are preserved from the original module.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### The tapes -/



open IterateWhile

/-! ### The machine -/

/-- The states of `Turing.MultiTapeTM.iterateWhileRound`. -/
public abbrev IterateWhileRoundState (State : Type*) :=
  (Unit ⊕ RewindWorkState) ⊕
    (MarkWorkState ⊕ ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕ MarkWorkState) ⊕
      (Unit ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ (State ⊕ RewindWorkState) ⊕ MarkWorkState)

/-- The states of `Turing.MultiTapeTM.iterateWhile`. -/
public abbrev IterateWhileState (State : Type*) :=
  ((Unit ⊕ RewindState) ⊕ RewindWorkState) ⊕
    (IterateWhileRoundState State ⊕ Unit) ⊕
      (MarkWorkState ⊕ (Unit ⊕ RewindState) ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState

section Machine

variable (tm : MultiTapeTM k Symbol State) (mark : Symbol)

/-- One round: clear the current tape, copy the next word to it, clear the next tape and apply
`tm` from the current tape to the next tape, using `mark` to flag the left end of words. -/
noncomputable def iterateWhileRound :
    MultiTapeTM (k + 1 + 2) Symbol (IterateWhileRoundState State) :=
  ((clearWork Symbol).extendTapes (tapeEmb (curTape k))).seq
    ((copyWord (copyEmb k) mark).seq
      (((clearWork Symbol).extendTapes (tapeEmb (nextTape k))).seq (tm.onWords mark)))

/-- `tm`, applied repeatedly while its result is non-empty, using `mark` to flag the left end of
words: load the input to the next tape, repeat rounds until the next tape is empty, then output
the current word and clear its tape. -/
public noncomputable def iterateWhile :
    MultiTapeTM (k + 1 + 2) Symbol (IterateWhileState State) :=
  (loadWord Symbol (nextTape k)).seq
    ((repeatUntilBlank (nextTape k) (iterateWhileRound tm mark)).seq
      ((emitWord (emitEmb k) mark).seq ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))))

end Machine

/-! ### The phases -/

namespace IterateWhile

variable (Symbol) in
lemma transformsTapes_clearCur (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (curTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words [] vn ∧ e = [])
      (3 * (vc.length + 1)) (vc.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vc).imp (fun _ _ h => by rw [h, words_cur])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_cur], he⟩) le_rfl le_rfl

variable (Symbol) in
lemma transformsTapes_clearNext (vc vn : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb (nextTape k)))
      (fun _ ws => ws = words vc vn) (fun _ _ ws' e => ws' = words vc [] ∧ e = [])
      (3 * (vn.length + 1)) (vn.length + 1 + (k + 1 + 2)) :=
  (transformsTapes_clearWork_tapeEmb _ vn).imp (fun _ _ h => by rw [h, words_next])
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, update_words_next], he⟩) le_rfl le_rfl

lemma transformsTapes_copy (mark : Symbol) (v : List Symbol) :
    TransformsTapes (copyWord (copyEmb k) mark) (fun _ ws => ws = words [] v)
      (fun _ _ ws' e => ws' = words v v ∧ e = [])
      (3 * v.length + 10) (4 * v.length + (k + 1 + 2) + 15) :=
  (transformsTapes_copyWord (copyEmb k) mark v).imp (fun _ _ h => by subst h; simp)
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨by rw [h', h, copyEmb_zero, update_words_cur], he⟩) le_rfl le_rfl

-- vendored: the space bounds of `onWords` and `loadWord` from here on are 3 and 1 cells larger
-- than in crei:crei/tidy-universal, following the space bounds of cslib #1111
lemma transformsTapes_onWords_step {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (tm.onWords mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + v'.length + 6) (s + 2 * v.length + 2 * v'.length + 3 * k + 18) :=
  (h.onWords mark).imp (fun _ _ hws => hws.trans (words_nil_next v))
    (fun _ _ _ _ hws ⟨h', he⟩ => ⟨by rw [h', hws, update_words_next], he⟩) le_rfl le_rfl

/-- One round takes `vp` on the current tape and `v` on the next tape to `v` on the current tape
and `v'` on the next tape. -/
lemma transformsTapes_iterateWhileRound {tm : MultiTapeTM k Symbol State} (mark : Symbol)
    {vp v v' : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace v v' t s) :
    TransformsTapes (iterateWhileRound tm mark) (fun _ ws => ws = words vp v)
      (fun _ _ ws' e => ws' = words v v' ∧ e = [])
      (t + 3 * vp.length + 6 * v.length + v'.length + 22)
      (s + vp.length + 7 * v.length + 2 * v'.length + 6 * k + 44) :=
  ((transformsTapes_clearCur Symbol vp v).seq_eq ((transformsTapes_copy mark v).seq_eq
    ((transformsTapes_clearNext Symbol v v).seq_eq (transformsTapes_onWords_step mark h)))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨h', he⟩ => ⟨h', by simp [he]⟩) (by omega) (by omega)

lemma transformsTapes_load (v : List Symbol) :
    TransformsTapes (loadWord Symbol (nextTape k)) (fun inp ws => inp = v ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = words [] v ∧ e = [])
      (3 * v.length + 6) (2 * v.length + (k + 1 + 2) + 3) :=
  (transformsTapes_loadWord (nextTape k) v).imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by rw [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨h', he⟩ => ⟨by rw [h', hws, words_nil_cur], he⟩) le_rfl le_rfl

lemma transformsTapes_emit (mark : Symbol) (v : List Symbol) :
    TransformsTapes (emitWord (emitEmb k) mark) (fun _ ws => ws = words v [])
      (fun _ _ ws' e => ws' = words v [] ∧ e = v)
      (2 * v.length + 8) (2 * v.length + (k + 1 + 2) + 10) :=
  (transformsTapes_emitWord (emitEmb k) mark v).imp (fun _ _ h => by subst h; simp)
    (fun _ _ _ _ h ⟨h', he⟩ => ⟨h'.trans h, he⟩) le_rfl le_rfl

end IterateWhile

/-! ### Iterating a machine -/

open IterateWhile in
/-- If `tm` computes `w (n + 1)` from `w n` tidily within `t` steps and `s` cells for every
`n ≤ r`, the words `w n` for `n ≤ r` have length at most `l`, and `w (n + 1)` is empty exactly for
`n = r`, then `tm.iterateWhile mark` computes `w r` from `w 0` tidily. -/
public theorem computesTidily_iterateWhile {tm : MultiTapeTM k Symbol State}
    {w : ℕ → List Symbol} {r t s l : ℕ}
    (h : ∀ n ≤ r, tm.ComputesTidilyInTimeAndSpace (w n) (w (n + 1)) t s)
    (hl : ∀ n ≤ r, (w n).length ≤ l) (hne : ∀ n < r, w (n + 1) ≠ []) (hnil : w (r + 1) = [])
    (mark : Symbol) :
    (tm.iterateWhile mark).ComputesTidilyInTimeAndSpace (w 0) (w r)
      ((r + 1) * (t + 10 * l + 24) + 8 * l + 17)
      (2 * (k + 3) * (s + 10 * l + 6 * k + 44) + 5 * l + 4 * k + 26) := by
  have hl' (n : ℕ) (hn : n ≤ r) : (w (n + 1)).length ≤ l := by
    rcases hn.lt_or_eq with hn | rfl
    exacts [hl _ hn, by simp [hnil]]
  -- the word on the current tape at the start of round `n`
  let prev : ℕ → List Symbol := fun | 0 => [] | n + 1 => w n
  have hprev (n : ℕ) (hn : n ≤ r) : (prev n).length ≤ l := by
    cases n with
    | zero => simp [prev]
    | succ n => exact hl n (by omega)
  -- each round, within uniform bounds
  have hround (n : ℕ) (hn : n ≤ r) := by
    have := hprev n hn; have := hl n hn; have := hl' n hn
    exact (transformsTapes_iterateWhileRound mark (vp := prev n) (h n hn)).mono
      (t' := t + 10 * l + 23) (s' := s + 10 * l + 6 * k + 44) (by omega) (by omega)
  have hloop := (transformsTapes_repeatUntilBlank (nextTape k) (tm := iterateWhileRound tm mark)
    (P := fun n _ ws emitted => ws = words (prev n) (w n) ∧ emitted = [])
    (R := fun _ ws emitted => ws = words (w r) [] ∧ emitted = [])
    (fun n hn _ => (hround n hn.le).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨hws', by simp [hem, he]⟩,
        by rw [hws', words_next]; exact hne n hn⟩) le_rfl le_rfl)
    (fun _ => (hround r le_rfl).imp (fun _ _ hP => hP.1)
      (fun _ _ _ _ ⟨_, hem⟩ ⟨hws', he⟩ => ⟨⟨by rw [hws', hnil], by simp [hem, he]⟩,
        by rw [hws', words_next, hnil]⟩) le_rfl le_rfl)).imp
    (P' := fun _ ws => ws = words [] (w 0))
    (Q' := fun _ _ ws' e => ws' = words (w r) [] ∧ e = [])
    (fun _ _ h => ⟨h, rfl⟩) (fun _ _ _ _ _ h => h) le_rfl le_rfl
  refine ((transformsTapes_load (k := k) (w 0)).seq_eq (hloop.seq_eq
    ((transformsTapes_emit mark (w r)).seq_eq (transformsTapes_clearCur Symbol (w r) [])))).imp
    (fun _ _ h => h) (fun _ _ _ _ _ ⟨hws, he⟩ => ⟨hws.trans words_nil_nil, by simp [he]⟩) ?_ ?_
  all_goals have := hl 0 (Nat.zero_le _); have := hl r le_rfl; ring_nf; omega

end Turing.MultiTapeTM
