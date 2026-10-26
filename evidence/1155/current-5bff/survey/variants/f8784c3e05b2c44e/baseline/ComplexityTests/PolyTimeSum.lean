/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Tactic.PolyTime

/-! Tagged encodings, empty summands, and captured constructor certificates. -/

namespace ComplexityTests.PolyTimeSum

open Turing.MultiTapeTM

-- Equal empty payloads remain distinct because the tag is always present.
private def emptyUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

example : encSum emptyUnit emptyUnit (.inl ()) = [false] := rfl
example : encSum emptyUnit emptyUnit (.inr ()) = [true] := rfl
example : (encSum encUnary encBits (.inr [false, true])).length = 3 := rfl

example {α β Input : Type} (left : α ↪ List Bool) (right : β ↪ List Bool)
    (input : Input ↪ List Bool) (f : Input → α)
    (hf : ComputableTidilyInPolyTime f input left) :
    ComputableTidilyInPolyTime (fun x => Sum.inl (f x)) input (encSum left right) := by
  fail_if_success (clear hf; fun_prop)
  fun_prop

example {α β Input : Type} (left : α ↪ List Bool) (right : β ↪ List Bool)
    (input : Input ↪ List Bool) (f : Input → β)
    (hf : ComputableTidilyInPolyTime f input right) :
    ComputableTidilyInPolyTime (fun x => let value := f x; Sum.inr value)
      input (encSum left right) := by polytime

-- Neither constructor requires the other summand to be inhabited.
example (empty : Empty ↪ List Bool) : ComputableTidilyInPolyTime
    (Sum.inr : ℕ → Empty ⊕ ℕ) encUnary (encSum empty encUnary) := by fun_prop
example (empty : Empty ↪ List Bool) : ComputableTidilyInPolyTime
    (Sum.inl : ℕ → ℕ ⊕ Empty) encUnary (encSum encUnary empty) := by fun_prop

end ComplexityTests.PolyTimeSum
