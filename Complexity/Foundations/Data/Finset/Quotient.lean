/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Cardinality of a quotient fiber

## Main results

* `Finset.card_filter_div_eq_le`: an injectively indexed quotient fiber has at most the divisor
  many members.

## References

Adapted from [Counting.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Counting.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Finset

/-- At most `c` elements `x` of `s` have `⌊f x / c⌋ = k`, if `f` is injective on `s`: their values
lie in `[kc, kc + c)`. -/
theorem card_filter_div_eq_le {α : Type*} (s : Finset α) {f : α → ℕ} (hf : Set.InjOn f s)
    {c : ℕ} (hc : 0 < c) (k : ℕ) : (s.filter fun x => f x / c = k).card ≤ c := by
  have hmaps : ∀ x ∈ s.filter fun x => f x / c = k, f x ∈ Finset.Ico (k * c) (k * c + c) := by
    intro x hx
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_Ico, ← Nat.succ_mul]
    exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul hc).mp (Nat.lt_succ_self _)⟩
  calc (s.filter fun x => f x / c = k).card ≤ (Finset.Ico (k * c) (k * c + c)).card :=
        Finset.card_le_card_of_injOn f hmaps (hf.mono fun x hx => (Finset.mem_filter.mp hx).1)
    _ = c := by rw [Nat.card_Ico, Nat.add_sub_cancel_left]

end Finset
