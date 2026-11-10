/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Triangle and submultiplicative bounds for weighted coefficient sums

For a weight `ν : R → S` on coefficients, the sum `p.sum fun _ a => ν a` of the weights of the
coefficients of a polynomial `p : R[X]` is an `ℓ¹`-type size of `p`. This module proves that
this size inherits the triangle inequality from a subadditive weight, and submultiplicativity
from a weight that is moreover submultiplicative. Instances are the `ℓ¹` coefficient norm
`Polynomial.coeffNorm1` of an integer polynomial (`ν = Int.natAbs`) and the bivariate norm
`Polynomial.bivariateCoeffNorm1` (`ν = Polynomial.coeffNorm1`).

## Main results

* `Polynomial.sum_add_le_of_subadditive`: the size of `p + q` is at most the sum of the sizes.
* `Polynomial.sum_mul_le_of_submultiplicative`: the size of `p * q` is at most the product of the
  sizes.
-/

public section

namespace Polynomial

open Finset

variable {R S : Type*} [Semiring R]

/-- The weighted coefficient sum of a subadditive weight is subadditive. -/
theorem sum_add_le_of_subadditive [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]
    {ν : R → S} (h0 : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b) (p q : R[X]) :
    ((p + q).sum fun _ a => ν a) ≤ (p.sum fun _ a => ν a) + q.sum fun _ a => ν a := by
  classical
  rw [sum_eq_of_subset _ (fun _ => h0) support_add,
    sum_eq_of_subset _ (fun _ => h0) (subset_union_left (s₂ := q.support)),
    sum_eq_of_subset _ (fun _ => h0) (subset_union_right (s₁ := p.support)), ← sum_add_distrib]
  exact sum_le_sum fun i _ => (coeff_add p q i).symm ▸ hadd _ _

/-- The weighted coefficient sum of a subadditive, submultiplicative weight is
submultiplicative. -/
theorem sum_mul_le_of_submultiplicative [CommSemiring S] [PartialOrder S] [IsOrderedRing S]
    {ν : R → S} (h0 : ν 0 = 0) (hadd : ∀ a b, ν (a + b) ≤ ν a + ν b)
    (hmul : ∀ a b, ν (a * b) ≤ ν a * ν b) (p q : R[X]) :
    ((p * q).sum fun _ a => ν a) ≤ (p.sum fun _ a => ν a) * q.sum fun _ a => ν a := by
  -- Expand `p * q` into the monomials `p_i q_j X^(i+j)` and apply the triangle inequality twice.
  let N : R[X] → S := fun r => r.sum fun _ a => ν a
  have hN0 : N 0 = 0 := sum_zero_index _
  have hNadd : ∀ r s, N (r + s) ≤ N r + N s := sum_add_le_of_subadditive h0 hadd
  calc N (p * q)
      = N (∑ i ∈ p.support, ∑ j ∈ q.support, monomial (i + j) (p.coeff i * q.coeff j)) := by
        rw [mul_eq_sum_sum]
        rfl
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, N (monomial (i + j) (p.coeff i * q.coeff j)) :=
        (le_sum_of_subadditive N hN0.le hNadd _ _).trans
          (sum_le_sum fun i _ => le_sum_of_subadditive N hN0.le hNadd _ _)
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, ν (p.coeff i) * ν (q.coeff j) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          (sum_monomial_index _ _ h0).trans_le (hmul _ _)
    _ = N p * N q := (sum_mul_sum _ _ _ _).symm

end Polynomial
