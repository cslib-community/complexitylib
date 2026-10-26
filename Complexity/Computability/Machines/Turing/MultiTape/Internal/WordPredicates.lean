/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-! # Shared finite-state word predicates

The nonempty-word transducer is shared by direct Option and unary Degree certificates. Its
machine clocks include the whole runtime input; it uses no work tapes.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.WordPredicates

/-- Emit a single Boolean indicating whether the input contains a symbol. -/
def nonemptyT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [] else [true])
  final q := if q then [] else [false]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- After the first input symbol, no further output is emitted. -/
lemma nonemptyT_run_true (w : List Bool) : nonemptyT.run true w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [] ++ nonemptyT.run true w = []
    simpa using ih

end Turing.MultiTapeTM.Internal.WordPredicates
