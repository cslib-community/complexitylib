/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, binary partitions of finite sets)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# The larger part of a binary partition

Select a Boolean fiber retaining at least half the elements of a finite set.
This is shared by the index-gadget and low-discrepancy simulations.
-/

@[expose] public section

namespace Finset

/-- The larger half of `s` under the bit `f`: at least half of `s` has `f a = bigHalf s f`. -/
def bigHalf {α : Type*} (s : Finset α) (f : α → Bool) : Bool :=
  decide (#s ≤ 2 * #(s.filter fun a => f a = true))

theorem card_le_two_mul_card_filter_bigHalf {α : Type*} (s : Finset α) (f : α → Bool) :
    (#s : ℝ) ≤ 2 * #(s.filter fun a => f a = bigHalf s f) := by
  have hsum := card_filter_add_card_filter_not (s := s) (fun a => f a = true)
  unfold bigHalf
  by_cases h : #s ≤ 2 * #(s.filter fun a => f a = true)
  · simp only [h, decide_true]; exact_mod_cast h
  · simp only [h, decide_false]
    simp only [Bool.not_eq_true] at hsum
    have : #s ≤ 2 * #(s.filter fun a => f a = false) := by omega
    exact_mod_cast this

end Finset
