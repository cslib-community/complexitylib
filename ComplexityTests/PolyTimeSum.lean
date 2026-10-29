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

-- Equal empty payloads remain distinct because the tag is always present, and constructor
-- certificates capture payloads without requiring the other summand to be inhabited.
example {α β Input : Type} (left : α ↪ List Bool) (right : β ↪ List Bool)
    (input : Input ↪ List Bool) (f : Input → α) (g : Input → β)
    (hf : ComputableInPolyTime f input left) (hg : ComputableTidilyInPolyTime g input right)
    (empty : Empty ↪ List Bool) :
    encSum emptyUnit emptyUnit (.inl ()) = [false] ∧
    encSum emptyUnit emptyUnit (.inr ()) = [true] ∧
    (encSum encUnary encBits (.inr [false, true])).length = 3 ∧
    ComputableInPolyTime (fun x => Sum.inl (f x)) input (encSum left right) ∧
    ComputableInPolyTime (fun x => let value := g x; Sum.inr value) input (encSum left right) ∧
    ComputableInPolyTime (Sum.inr : ℕ → Empty ⊕ ℕ) encUnary (encSum empty encUnary) ∧
    ComputableInPolyTime (Sum.inl : ℕ → ℕ ⊕ Empty) encUnary (encSum encUnary empty) := by
  refine ⟨rfl, rfl, rfl, ?_, .of_tidy (by polytime), by fun_prop, by fun_prop⟩
  fail_if_success (clear hf; fun_prop)
  fun_prop

end ComplexityTests.PolyTimeSum
