/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Appending at a persistent work cursor

Appending one symbol costs one native step when the selected work head already points to the
right blank. Other tapes, their cursors, the input head, and the output are preserved. The cursor
stays at the new right blank, permitting a streamed address prefix without rescanning it.
-/

public section

namespace Turing.MultiTapeTM

/-- Write a fixed symbol at the selected cursor, move that cursor right, and halt. -/
@[expose] def appendAtCursor {k : ℕ} {Symbol : Type*} (i : Fin k) (s : Symbol) :
    MultiTapeTM k Symbol Unit :=
  .ofTr () fun _ _ _ =>
    ⟨0, fun j => if j = i then (some (some s), 1) else (none, 0), none, none⟩

/-- Appending does not copy the existing word or normalize any other work head. -/
theorem runFrom_appendAtCursor {k : ℕ} {Symbol : Type*} {input : List Symbol}
    (i : Fin k) (s : Symbol) (ip : Fin (input.length + 2))
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) (out w : List Symbol)
    (ht : tapes i = tapeOfList w) (hh : heads i = (w.length : ℤ)) :
    (appendAtCursor i s).runFrom ⟨some (), ip, tapes, heads, out⟩ 1 =
      ⟨none, ip, Function.update tapes i (tapeOfList (w ++ [s])),
        Function.update heads i ((w.length : ℤ) + 1), out⟩ := by
  rw [runFrom_one, step_of_state rfl]
  refine Cfg.ext (by simp [appendAtCursor, tr_ofTr, Action.apply]) ?_ ?_ ?_ ?_
  · simp [appendAtCursor, tr_ofTr, Action.apply]
  · funext j
    by_cases hj : j = i
    · subst j
      simp [appendAtCursor, tr_ofTr, Action.apply, ht, hh, tapeOfList_append_single]
    · simp [appendAtCursor, tr_ofTr, Action.apply, hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp [appendAtCursor, tr_ofTr, Action.apply, hh]
    · simp [appendAtCursor, tr_ofTr, Action.apply, hj]
  · simp [appendAtCursor, tr_ofTr, Action.apply]

end Turing.MultiTapeTM
