/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words

/-!
# Tagged sum encodings

A Boolean tag selects the payload encoding: `false` for the left summand and `true` for the
right summand. This permits differently encoded, possibly empty summands without padding.

## Main definitions

* `Turing.MultiTapeTM.encSum`: a tagged sum of two supplied encodings.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- Encode a sum with one tag bit followed by the corresponding payload. -/
def encSum (left : α ↪ List Bool) (right : β ↪ List Bool) : α ⊕ β ↪ List Bool :=
  ⟨Sum.elim (fun a => false :: left a) (fun b => true :: right b), by
    rintro (a | b) (c | d) h <;> simp_all⟩

@[simp]
theorem encSum_inl (left : α ↪ List Bool) (right : β ↪ List Bool) (a : α) :
    encSum left right (.inl a) = false :: left a := rfl

@[simp]
theorem encSum_inr (left : α ↪ List Bool) (right : β ↪ List Bool) (b : β) :
    encSum left right (.inr b) = true :: right b := rfl

/-- The encoding charges the selected payload and exactly one tag bit. -/
theorem length_encSum (left : α ↪ List Bool) (right : β ↪ List Bool) (value : α ⊕ β) :
    (encSum left right value).length =
      value.elim (fun a => (left a).length) (fun b => (right b).length) + 1 := by
  cases value <;> rfl

end Turing.MultiTapeTM
