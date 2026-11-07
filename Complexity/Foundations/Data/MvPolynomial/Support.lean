/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate (Mathlib, polynomial support bounds)

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Support bounds for multivariate polynomials

The number of monomials in a product is at most the product of the support sizes. In particular,
multiplication by a monomial does not increase support size. These bounds hold over any
commutative semiring, allowing zero coefficients, zero divisors and cancellation.
-/

public section

namespace MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- A product has at most as many supported monomials as pairs from the two supports. -/
theorem card_support_mul_le (p q : MvPolynomial V R) :
    (p * q).support.card ≤ p.support.card * q.support.card := by
  classical
  exact (Finset.card_le_card (support_mul p q)).trans Finset.card_add_le

/-- Multiplication by a monomial does not increase support size, regardless of its coefficient. -/
theorem card_support_monomial_mul_le (m : V →₀ ℕ) (a : R) (p : MvPolynomial V R) :
    (monomial m a * p).support.card ≤ p.support.card := by
  classical
  calc
    _ ≤ (monomial m a).support.card * p.support.card := card_support_mul_le _ _
    _ ≤ 1 * p.support.card := Nat.mul_le_mul_right _
      ((Finset.card_le_card support_monomial_subset).trans_eq (Finset.card_singleton m))
    _ = _ := one_mul _

end MvPolynomial
