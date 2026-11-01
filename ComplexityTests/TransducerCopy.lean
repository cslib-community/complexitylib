/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (copying-state API regressions)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy

/-!
# Copying-state regressions

The shared rule applies to a three-symbol alphabet with one state, unlike the Boolean,
three-state transducers that motivated it. A nonempty final word demonstrates why the empty
final-output hypothesis is necessary, including on empty input.
-/

public section

namespace ComplexityTests.TransducerCopy

open Turing.MultiTapeTM

/-- A one-state transducer copying a three-symbol alphabet, with a configurable final suffix. -/
def copier (suffix : List (Fin 3)) (h : suffix.length ≤ 2) : Transducer (Fin 3) Unit where
  q₀ := ()
  step q a := (q, [a])
  final _ := suffix
  length_step_le _ _ := by simp
  length_final_le _ := h

/-- The shared theorem handles arbitrary words over a non-Boolean alphabet. -/
theorem copies_word (w : List (Fin 3)) : (copier [] (by decide)).run () w = w :=
  Transducer.run_eq_self _ () (fun _ => rfl) rfl w

/-- Each of the three distinct symbols survives, in order. -/
theorem copies_three_symbols : (copier [] (by decide)).run () [2, 0, 1] = [2, 0, 1] :=
  copies_word _

/-- Copying transitions alone do not suffice when a final suffix is emitted. -/
theorem nonempty_final_suffix :
    (copier [2] (by decide)).run () [0, 1] = [0, 1, 2] ∧
      (copier [2] (by decide)).run () ([] : List (Fin 3)) ≠ [] := by
  decide

end ComplexityTests.TransducerCopy
