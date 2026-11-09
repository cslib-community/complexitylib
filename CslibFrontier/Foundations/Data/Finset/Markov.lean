/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Algebra/Order/BigOperators/Group/Finset)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Markov's inequality for finite sums

If a nonnegative function `f` on a finite set `s` is at least `m` on `{x ∈ s | p x}`, then `m`
times the cardinality of that subset is at most `∑ x ∈ s, f x`
(`Finset.mul_card_filter_le_sum`, `Finset.card_filter_mul_le_sum`).

## Main results

* `Finset.mul_card_filter_le_sum`: `m * #{x ∈ s | p x} ≤ ∑ x ∈ s, f x` for `f : α → ℕ`.
* `Finset.card_filter_mul_le_sum`: `(#{x ∈ s | p x} : R) * m ≤ ∑ x ∈ s, f x` for `0 ≤ f x`.
-/

@[expose] public section

open scoped BigOperators

namespace Finset

variable {α : Type*}

/-- **Markov's inequality** for a nonnegative `Finset` sum: if `0 ≤ f x` on `s` and `m ≤ f x`
whenever `x ∈ s` satisfies `p x`, then `#{x ∈ s | p x} * m ≤ ∑ x ∈ s, f x`. -/
theorem card_filter_mul_le_sum {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R]
    (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → R) {m : R}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hm : ∀ x ∈ s, p x → m ≤ f x) :
    (#{x ∈ s | p x} : R) * m ≤ ∑ x ∈ s, f x := by
  rw [← nsmul_eq_mul]
  exact ((s.filter p).card_nsmul_le_sum f m fun x hx =>
    hm x (mem_filter.mp hx).1 (mem_filter.mp hx).2).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset p s) fun x hx _ => hf x hx)

/-- **Markov's inequality** for a `Finset` sum: if `m ≤ f x` whenever `x ∈ s` satisfies `p x`,
then `m * #{x ∈ s | p x} ≤ ∑ x ∈ s, f x`. -/
theorem mul_card_filter_le_sum (s : Finset α) (p : α → Prop) [DecidablePred p] (f : α → ℕ)
    {m : ℕ} (hm : ∀ x ∈ s, p x → m ≤ f x) :
    m * #{x ∈ s | p x} ≤ ∑ x ∈ s, f x :=
  Nat.mul_comm _ _ ▸ s.card_filter_mul_le_sum p f (fun _ _ => Nat.zero_le _) hm

end Finset
