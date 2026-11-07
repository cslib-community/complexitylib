/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Tropical.BigOperators

/-!
# Order facts for (min,+) sums

In `MinTropical R` addition is `min`, so a sum is below each summand, and a nonempty finite sum
is attained by one of its summands. These are the facts used to read tropical matrix entries as
minima over walks.

## Main results

* `MinTropical.add_le_left`, `MinTropical.add_le_right`: `x + y ≤ x` and `x + y ≤ y`.
* `MinTropical.add_eq_or`: `x + y` is `x` or `y`.
* `MinTropical.sum_le_of_mem`: a finite sum is below each of its summands.
* `MinTropical.exists_sum_eq`: a nonempty finite sum is one of its summands.
-/

public section

namespace MinTropical

variable {R : Type*}

section LinearOrder

variable [LinearOrder R]

theorem add_le_left (x y : MinTropical R) : x + y ≤ x := by
  rw [← untrop_le_iff, untrop_add]
  exact min_le_left _ _

theorem add_le_right (x y : MinTropical R) : x + y ≤ y := by
  rw [← untrop_le_iff, untrop_add]
  exact min_le_right _ _

theorem add_eq_or (x y : MinTropical R) : x + y = x ∨ x + y = y := by
  rcases le_total x y with h | h
  · exact Or.inl (add_eq_left h)
  · exact Or.inr (add_eq_right h)

end LinearOrder

variable [LinearOrder R] [OrderTop R] {ι : Type*}

theorem sum_le_of_mem {s : Finset ι} (f : ι → MinTropical R) {a : ι} (ha : a ∈ s) :
    ∑ i ∈ s, f i ≤ f a := by
  rw [← untrop_le_iff, Finset.untrop_sum']
  exact Finset.inf_le (f := untrop ∘ f) ha

theorem exists_sum_eq {s : Finset ι} (hs : s.Nonempty) (f : ι → MinTropical R) :
    ∃ a ∈ s, ∑ i ∈ s, f i = f a := by
  obtain ⟨a, ha, h⟩ := Finset.exists_mem_eq_inf s hs (untrop ∘ f)
  refine ⟨a, ha, untrop_injective ?_⟩
  rw [Finset.untrop_sum', h]
  rfl

end MinTropical
