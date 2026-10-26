/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: submitted #1111 @3441fa81

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import Cslib.Foundations.Data.Fin.Tuple

/-! # Legacy existential work-tape interface

The existing machine and fixed-machine run laws are reexported from the Internal kernel.
-/
@[expose] public section
namespace Turing.MultiTapeTM
/-- A tidily computable function is computed by a machine with binary alphabet and finitely many
states that reads its input from a work tape `i` and writes its output to a different work tape
`o`, leaving every other work tape unchanged and emitting nothing. -/
theorem ComputableTidilyInTimeAndSpace.exists_onWords {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM (k + 1 + 2) Bool State)
      (i o : Fin (k + 1 + 2)), i ≠ o ∧ ∀ a, TransformsTapes tm
        (fun _ ws => ws = Function.update (fun _ => []) i (encIn a))
        (fun _ ws ws' emitted => ws' = Function.update ws o (encOut (f a)) ∧ emitted = [])
        (t a + (encOut (f a)).length + 6)
        (s a + 2 * (encIn a).length + 2 * (encOut (f a)).length + 3 * k + 18) := by
  obtain ⟨k, State, _, tm, htm⟩ := h
  exact ⟨k, _, inferInstance, tm.onWords true, Fin.natAdd (k + 1) 0, (Fin.last k).castAdd 2,
    (Fin.castAdd_ne_natAdd _ _).symm,
    fun a => (htm a).onWords true⟩

end Turing.MultiTapeTM
