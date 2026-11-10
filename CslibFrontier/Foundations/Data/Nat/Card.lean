/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib's `Mathlib/SetTheory/Cardinal/Finite.lean`, next to `Nat.card_sum`)

public import CslibFrontier.Init
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting a subtype of a sum

The elements of `β ⊕ γ` satisfying a predicate are those of `β` and those of `γ` that satisfy it
(`Nat.card_subtype_sum`); along a decomposition `α ≃ β ⊕ γ` the same count splits a subtype of
`α` (`Nat.card_subtype_eq_add_of_equiv_sum`).

## Main results

* `Nat.card_subtype_sum`: counting a subtype of a sum.
* `Nat.card_subtype_eq_add_of_equiv_sum`: counting a subtype along a decomposition into a sum.
-/

public section

namespace Nat

variable {α β γ : Type*} [Finite β] [Finite γ]

/-- The elements of `β ⊕ γ` satisfying `P` are those of `β` and those of `γ` that satisfy it. -/
theorem card_subtype_sum (P : β ⊕ γ → Prop) :
    Nat.card {x // P x} = Nat.card {b // P (.inl b)} + Nat.card {c // P (.inr c)} := by
  rw [← Nat.card_sum]
  exact Nat.card_congr Equiv.subtypeSum

/-- Counting along a decomposition `α ≃ β ⊕ γ`: the elements satisfying `P` are those coming
from `β` and those coming from `γ`. -/
theorem card_subtype_eq_add_of_equiv_sum (e : α ≃ β ⊕ γ) (P : α → Prop) :
    Nat.card {a // P a} =
      Nat.card {b // P (e.symm (.inl b))} + Nat.card {c // P (e.symm (.inr c))} :=
  (Nat.card_congr (e.subtypeEquiv (q := fun x => P (e.symm x)) fun a => by
    rw [e.symm_apply_apply])).trans (card_subtype_sum _)

end Nat
