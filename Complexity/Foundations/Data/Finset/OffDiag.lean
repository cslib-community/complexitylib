/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib.Algebra.BigOperators.Ring.Finset)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Products of sums over the off-diagonal

The product of two finite sums over the same index set is the sum of the products at equal indices
plus the sum of the products over the ordered pairs of distinct indices
(`Finset.sum_mul_sum_eq_sum_mul_add_sum_offDiag`); in particular the square of a finite sum is the
sum of the squares plus the sum over the off-diagonal (`Finset.sq_sum_eq_sum_sq_add_sum_offDiag`).
This is how second and fourth moments of sums of pairwise or four-wise independent terms are
computed.

## Main results

* `Finset.sum_mul_sum_eq_sum_mul_add_sum_offDiag`: `(∑ x ∈ s, f x) * ∑ x ∈ s, g x =
  ∑ x ∈ s, f x * g x + ∑ p ∈ s.offDiag, f p.1 * g p.2`.
* `Finset.sq_sum_eq_sum_sq_add_sum_offDiag`: `(∑ x ∈ s, g x) ^ 2 = ∑ x ∈ s, g x ^ 2 +
  ∑ p ∈ s.offDiag, g p.1 * g p.2`.
-/

public section

open Finset

/-- The product of two finite sums over the same index set is the sum of the products at equal
indices plus the products over the ordered pairs of distinct indices. -/
theorem Finset.sum_mul_sum_eq_sum_mul_add_sum_offDiag {α R : Type*} [CommSemiring R]
    (s : Finset α) (f g : α → R) :
    (∑ x ∈ s, f x) * ∑ x ∈ s, g x = ∑ x ∈ s, f x * g x + ∑ p ∈ s.offDiag, f p.1 * g p.2 := by
  classical
  rw [Finset.sum_mul_sum, ← sum_product' (f := fun x y => f x * g y), ← diag_union_offDiag,
    sum_union (disjoint_diag_offDiag s), sum_diag]

/-- The square of a finite sum is the sum of the squares plus the products over the ordered pairs
of distinct indices. -/
theorem Finset.sq_sum_eq_sum_sq_add_sum_offDiag {α R : Type*} [CommSemiring R]
    (s : Finset α) (g : α → R) :
    (∑ x ∈ s, g x) ^ 2 = ∑ x ∈ s, g x ^ 2 + ∑ p ∈ s.offDiag, g p.1 * g p.2 := by
  rw [sq, sum_mul_sum_eq_sum_mul_add_sum_offDiag]
  simp only [sq]
