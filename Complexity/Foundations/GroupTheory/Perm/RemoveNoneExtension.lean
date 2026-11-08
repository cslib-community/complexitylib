/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib)

public import Complexity.Init
public import Mathlib.Logic.Equiv.Option

/-!
# Extending values over a removed permutation point

A function on the retained points extends to `Option` by assigning the removed point its
successor's value. If that point was fixed, the specified default is used. The extension is
constant on the removed step and agrees exactly with the `removeNone` successor elsewhere.
No finiteness or equality decision is required. These original identities let a Boolean
potential give zero label to a deleted dart without changing retained differences.
-/

public section

namespace Equiv.Perm

variable {α β : Type*}

/-- Extend values from retained points; a removed fixed point receives `base`. -/
@[expose] def extendRemoveNone (f : Perm (Option α)) (p : α → β) (base : β) : Option α → β
  | none => (f none).elim base p
  | some a => p a

/-- Every retained value is literally unchanged. -/
theorem extendRemoveNone_some (f : Perm (Option α)) (p : α → β) (base : β) (a : α) :
    extendRemoveNone f p base (some a) = p a := rfl

/-- The deleted step has constant extended value, including a deleted fixed point. -/
theorem extendRemoveNone_none (f : Perm (Option α)) (p : α → β) (base : β) :
    extendRemoveNone f p base none = extendRemoveNone f p base (f none) := by
  cases hf : f none <;> simp [extendRemoveNone, hf]

/-- The old successor's extended value is exactly the retained permutation successor's
value. This includes a step that previously led into the deleted point. -/
theorem extendRemoveNone_apply_some (f : Perm (Option α)) (p : α → β) (base : β) (a : α) :
    extendRemoveNone f p base (f (some a)) = p (Equiv.removeNone f a) := by
  cases hf : f (some a) with
  | none =>
    have he := Equiv.removeNone_none f hf
    rw [extendRemoveNone, ← he]
    rfl
  | some b =>
    have he := Equiv.removeNone_some f ⟨b, hf⟩
    rw [hf] at he
    rw [extendRemoveNone, Option.some.inj he]

end Equiv.Perm
