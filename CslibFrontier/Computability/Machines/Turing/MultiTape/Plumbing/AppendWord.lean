/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordMoves
import Mathlib.Tactic.FinCases

/-!
# Appending a framed or raw word at a persistent destination cursor

The source on tape 0 is preserved. Tape 1 is extended at its right blank, without scanning its
existing prefix. Framed mode emits two cells per source bit and a delimiter; raw mode emits one
cell per source bit. The certified clocks include the terminating blank test.
-/

public section

namespace Turing.MultiTapeTM.AppendWord

/-- The output fragment for one field, optionally self-delimited. -/
@[expose] def fragment (framed : Bool) (word : List Bool) : List Bool :=
  if framed then frame word else word

/-- Fixed finite control for framed/raw append; `some b` is the pending second framed cell. -/
@[expose] def machine (framed : Bool) : MultiTapeTM 2 Bool (Option Bool) :=
  ofTr none fun q _ work => match q with
  | some b => ⟨0, ![(none, 1), (some (some b), 1)], none, some none⟩
  | none => match work 0 with
    | some b => if framed then
        ⟨0, ![(none, 0), (some (some true), 1)], none, some (some b)⟩
      else ⟨0, ![(none, 1), (some (some b), 1)], none, some none⟩
    | none => if framed then
        ⟨0, ![(none, 0), (some (some false), 1)], none, none⟩
      else ⟨0, ![(none, 0), (none, 0)], none, none⟩

/-- Remaining time from the first unread source cell. -/
@[expose] def clock (framed : Bool) (word : List Bool) : ℕ :=
  (if framed then 2 else 1) * word.length + 1

/-- Source and destination words, with explicit source offset and destination frontier. -/
@[expose] def config (input source dest : List Bool) (read : ℕ) (out : List Bool) :
    Cfg 2 Bool Unit input :=
  tapesCfg input ![source, dest] 0 ![(read : ℤ), (dest.length : ℤ)] out

private theorem step_write {input source dest : List Bool} {read : ℕ} {out : List Bool}
    {framed : Bool} {q : Option Bool} {q' : Option (Option Bool)} {b : Bool} {move : SignType}
    (ha : (machine framed).tr q (config input source dest read out).inputSymbol
      (fun i => tapeOfList (![source, dest] i)
        (![(read : ℤ), (dest.length : ℤ)] i)) =
      ⟨0, ![(none, move), (some (some b), 1)], none, q'⟩)
    (read' : ℕ) (hread : (read : ℤ) + (move : ℤ) = read') :
    (machine framed).step ((config input source dest read out).withState (some q)) =
      (config input source (dest ++ [b]) read' out).withState q' := by
  apply step_tapesCfg (a := ⟨0, ![(none, move), (some (some b), 1)], none, q'⟩)
  · simpa [config] using ha
  · rfl
  · rfl
  · intro i
    fin_cases i
    · simp
    · simpa using update_shifted_append dest b 0
  · intro i
    fin_cases i
    · exact hread
    · simp

/-- The append loop supports an already-read source prefix and an arbitrary destination prefix. -/
theorem runFrom (framed : Bool) (input pre word dest out : List Bool) :
    (machine framed).runFrom
      ((config input (pre ++ word) dest pre.length out).withState (some none)) (clock framed word) =
      (config input (pre ++ word) (dest ++ fragment framed word)
        (pre.length + word.length) out).withState none := by
  induction word generalizing pre dest with
  | nil =>
    cases framed <;>
      simp only [clock, Bool.false_eq_true, ite_false, ite_true,
        List.length_nil, Nat.mul_zero, Nat.zero_add, fragment, List.append_nil, Nat.add_zero]
    · rw [runFrom_one, step_of_state rfl]
      simp only [Action.apply, machine, Fin.isValue, Bool.false_eq_true, ↓reduceIte,
        Cfg.withState, config, tapesCfg, Pi.zero_apply, sub_zero,
        tr_ofTr, Cfg.workTapeSymbols, Matrix.cons_val_zero,
        tapeOfList_ofNat, lt_self_iff_false, not_false_eq_true, getElem?_neg, moveInputPos_zero,
        Option.toList_none, List.append_nil, Cfg.mk.injEq, and_true, true_and]
      constructor <;> funext i <;> fin_cases i <;> rfl
    · have h := step_write (framed := true) (q := none) (q' := none) (b := false)
        (move := 0) (input := input) (source := pre) (dest := dest) (read := pre.length)
        (out := out) (by simp [machine, config, tapesCfg]) pre.length (by simp)
      simpa only [runFrom_one, frame_nil] using h
  | cons b word ih =>
    have hread : tapeOfList (pre ++ b :: word) (pre.length : ℤ) = some b := by simp
    cases framed
    · have hstep := step_write (framed := false) (q := none) (q' := some none) (b := b)
        (move := 1) (input := input) (source := pre ++ b :: word) (dest := dest)
        (read := pre.length) (out := out) (by simp [machine, config, tapesCfg, hread])
        (pre.length + 1) (by simp)
      rw [show clock false (b :: word) = 1 + clock false word by simp [clock]; omega,
        runFrom_add, runFrom_one, hstep]
      simpa [config, fragment, List.append_assoc, add_assoc, add_comm, add_left_comm] using
        ih (pre ++ [b]) (dest ++ [b])
    · have htag := step_write (framed := true) (q := none) (q' := some (some b)) (b := true)
        (move := 0) (input := input) (source := pre ++ b :: word) (dest := dest)
        (read := pre.length) (out := out) (by simp [machine, config, tapesCfg, hread])
        pre.length (by simp)
      have hbit := step_write (framed := true) (q := some b) (q' := some none) (b := b)
        (move := 1) (input := input) (source := pre ++ b :: word) (dest := dest ++ [true])
        (read := pre.length) (out := out) (by simp [machine]) (pre.length + 1) (by simp)
      rw [show clock true (b :: word) = 1 + (1 + clock true word) by simp [clock]; omega,
        runFrom_add, runFrom_one, htag, runFrom_add, runFrom_one, hbit]
      simpa [config, fragment, frame_cons, List.append_assoc, add_assoc, add_comm,
        add_left_comm] using
        ih (pre ++ [b]) (dest ++ [true, b])

/-- One field append starts with its source at zero and its destination at the old right blank. -/
theorem runsBetween (framed : Bool) (input word dest out : List Bool) :
    RunsBetween (machine framed) (config input word dest 0 out)
      (config input word (dest ++ fragment framed word) word.length out)
      (clock framed word) (2 * (clock framed word + 1)) := by
  apply RunsBetween.of_runFrom
  simpa only [machine, q₀_ofTr, List.nil_append, List.length_nil, Nat.zero_add] using
    runFrom framed input [] word dest out

/-- Framed append spends one transition per emitted cell; raw append also tests the final blank. -/
theorem clock_eq_length (framed : Bool) (word : List Bool) :
    clock framed word = (fragment framed word).length + (if framed then 0 else 1) := by
  cases framed <;> simp [clock, fragment]

end Turing.MultiTapeTM.AppendWord
