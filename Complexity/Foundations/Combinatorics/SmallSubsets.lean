/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, weighted subset counts)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Counting small subsets

The number of subsets of a finite set of size at most `d` is the corresponding truncated
sum of binomial coefficients. This identity holds for any threshold, including those above
the size of the ground set.

Weighting a subset `t` of `s` by `z ^ (#s - #t)` gives total weight `(z + 1) ^ #s`.
When `z ≥ 1`, every subset of size at most `d` has weight at least `z ^ (#s - d)`.
This gives a small-subset bound with a freely chosen integer weight.

Choosing `z = 2` and `d = #s / 3` gives the exact integral inequality
`M ^ 3 * 4 ^ #s ≤ 27 ^ #s`, where `M` counts subsets of size at most `#s / 3`.
Equivalently, the exponential base is `(27 / 4) ^ (1 / 3)`, strictly below `2`.
The integral form needs neither real powers nor an asymptotic convention.

## Main results

* `Finset.card_filter_powerset_card_le_eq_sum_choose`: count bounded-size subsets of a finset.
* `Finset.card_filter_card_le_eq_sum_choose`: the specialization to a finite type.
* `Finset.card_filter_card_le_mul_pow_le`: the weighted bound for any size threshold.
* `Finset.card_filter_card_le_third_pow_three_mul_four_pow_le`: the one-third bound.
-/

public section

namespace Finset

variable {α : Type*}

/-- Counting subsets of `s` by their cardinality gives a truncated binomial sum. Terms above
the cardinality of `s` vanish, so the threshold `D` need not be bounded by `#s`. -/
theorem card_filter_powerset_card_le_eq_sum_choose (s : Finset α) (D : ℕ) :
    #{S ∈ s.powerset | #S ≤ D} = ∑ j ∈ range (D + 1), (#s).choose j := by
  classical
  calc
    _ = ∑ j ∈ range (D + 1),
        #{S ∈ (s.powerset.filter fun T ↦ #T ≤ D) | #S = j} :=
      card_eq_sum_card_fiberwise fun S hS ↦
        mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (mem_filter.1 (mem_coe.1 hS)).2))
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [← card_powersetCard]
      congr 1
      ext S
      simp only [mem_filter, mem_powerset, mem_powersetCard]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩,
        fun h ↦ ⟨⟨h.1, h.2.le.trans (Nat.le_of_lt_succ (mem_range.1 hj))⟩, h.2⟩⟩

/-- Counting subsets of a finite type by cardinality gives a truncated binomial sum,
including thresholds above the size of the type. -/
theorem card_filter_card_le_eq_sum_choose [Fintype α] (D : ℕ) :
    #{S : Finset α | #S ≤ D} = ∑ j ∈ range (D + 1), (Fintype.card α).choose j := by
  classical
  simpa only [powerset_univ, card_univ] using
    card_filter_powerset_card_le_eq_sum_choose (univ : Finset α) D

/-- The number of subsets of `s` of size at most `d`, multiplied by the minimum weight
`z ^ (#s - d)` of such a subset, is at most the total weight `(z + 1) ^ #s`. -/
theorem card_filter_card_le_mul_pow_le (s : Finset α) (d z : ℕ) (hz : 1 ≤ z) :
    #{t ∈ s.powerset | #t ≤ d} * z ^ (#s - d) ≤ (z + 1) ^ #s := by
  classical
  have hsum := sum_pow_mul_eq_add_pow (1 : ℕ) z s
  simp only [one_pow, one_mul, add_comm 1 z] at hsum
  rw [← hsum]
  refine card_filter_mul_le_sum _ _ _ (fun _ _ ↦ Nat.zero_le _) ?_
  intro t _ ht
  exact Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left ht _)

/-- The subsets of size at most one third of the ground set have exponential base
`(27 / 4) ^ (1 / 3)`. This is an exact integer inequality, including the empty ground set. -/
theorem card_filter_card_le_third_pow_three_mul_four_pow_le (s : Finset α) :
    #{t ∈ s.powerset | #t ≤ #s / 3} ^ 3 * 4 ^ #s ≤ 27 ^ #s := by
  have h := card_filter_card_le_mul_pow_le s (#s / 3) 2 (by decide)
  have hp : 4 ^ #s ≤ (2 ^ (#s - #s / 3)) ^ 3 := by
    calc
      4 ^ #s = (2 ^ 2) ^ #s := rfl
      _ = 2 ^ (2 * #s) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ ((#s - #s / 3) * 3) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (2 ^ (#s - #s / 3)) ^ 3 := pow_mul _ _ _
  calc
    #{t ∈ s.powerset | #t ≤ #s / 3} ^ 3 * 4 ^ #s ≤
        #{t ∈ s.powerset | #t ≤ #s / 3} ^ 3 * (2 ^ (#s - #s / 3)) ^ 3 :=
      Nat.mul_le_mul_left _ hp
    _ = (#{t ∈ s.powerset | #t ≤ #s / 3} * 2 ^ (#s - #s / 3)) ^ 3 :=
      (mul_pow _ _ _).symm
    _ ≤ (3 ^ #s) ^ 3 := Nat.pow_le_pow_left h 3
    _ = (3 ^ 3) ^ #s := pow_right_comm _ _ _
    _ = 27 ^ #s := rfl

end Finset
