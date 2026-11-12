/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Finset/Card.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# The larger half of a finset under a Boolean test

A Boolean test splits a finset into two parts, and one of them has at least half of its elements
(`Finset.exists_card_le_two_mul_card_filter`). Halving arguments use it to keep the larger side
at each step, such as walks down a protocol tree or the gate-by-gate cut of a threshold circuit.

## Main results

* `Finset.exists_card_le_two_mul_card_filter`: some value of the test keeps at least half.
-/

public section

namespace Finset

/-- **The larger half.** For a Boolean test `f` on a finset `s`, one of the two parts
`{a ∈ s | f a = b}` has at least half of the elements of `s`. -/
theorem exists_card_le_two_mul_card_filter {α : Type*} (s : Finset α) (f : α → Bool) :
    ∃ b : Bool, #s ≤ 2 * #(s.filter fun a => f a = b) := by
  have h := card_filter_add_card_filter_not (s := s) (fun a => f a = true)
  have hf : (s.filter fun a => ¬ f a = true) = s.filter fun a => f a = false := by
    ext a
    simp
  rw [hf] at h
  by_contra hno
  push Not at hno
  have h1 := hno true
  have h2 := hno false
  omega

end Finset
