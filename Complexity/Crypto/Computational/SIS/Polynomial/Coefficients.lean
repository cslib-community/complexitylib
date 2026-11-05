/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.Module
public import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Ordinary-product coefficients of negacyclic multiplication

Subtracting the upper half of the ordinary polynomial product gives the existing
`negacyclicMul` coefficients. This original supporting identity works over any ring,
without a positive-dimension or nontriviality assumption. Its native multiplication client
imports this pure algebraic statement independently of the quotient interpretation.

## Main results

* `negacyclicMul_eq_coeff_mul`: the lower product coefficient minus its wrapped upper one.
-/

public section

namespace Cslib.Crypto

open Polynomial

private theorem ofCoeffList_ofFn_eq {R : Type*} [Semiring R] [DecidableEq R]
    {n : ℕ} (a : Fin n → R) :
    ofCoeffList (List.ofFn a) = Polynomial.ofFn n a := by
  ext i
  by_cases hi : i < n
  · simp [coeff_ofCoeffList, hi]
  · simp [coeff_ofCoeffList, hi, ofFn_coeff_eq_zero_of_ge a (Nat.le_of_not_gt hi)]

/-- Reduction modulo `X^n + 1` subtracts the upper half of the ordinary product.
This coefficient identity has no positive-dimension or nontrivial-ring assumption. -/
theorem negacyclicMul_eq_coeff_mul {R : Type*} [Ring R] {n : ℕ}
    (a b : Fin n → R) (i : Fin n) :
    negacyclicMul a b i =
      (ofCoeffList (List.ofFn a) * ofCoeffList (List.ofFn b)).coeff i -
        (ofCoeffList (List.ofFn a) * ofCoeffList (List.ofFn b)).coeff (n + i) := by
  classical
  rw [ofCoeffList_ofFn_eq, ofCoeffList_ofFn_eq]
  conv_rhs => rw [ofFn_eq_sum_monomial b]
  simp only [← C_mul_X_pow_eq_monomial, Finset.mul_sum, ← mul_assoc,
    finsetSum_coeff, coeff_mul_X_pow', coeff_mul_C]
  rw [← Finset.sum_sub_distrib]
  change (∑ j : Fin n, rotMatrix a i j * b j) = _
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val ≤ n + i.val := by omega
  rw [ite_eq_left hj]
  by_cases hji : j.val ≤ i.val
  · have hlo : i.val - j.val < n := by omega
    have hhi : n ≤ n + i.val - j.val := by omega
    rw [rotMatrix, Matrix.of_apply, dite_eq_left hji, ite_eq_left hji,
      ofFn_coeff_eq_val_of_lt _ hlo, ofFn_coeff_eq_zero_of_ge _ hhi]
    simp
  · have hhi : n + i.val - j.val < n := by omega
    rw [rotMatrix, Matrix.of_apply, dite_eq_right hji, ite_eq_right hji,
      ofFn_coeff_eq_val_of_lt _ hhi]
    simp [neg_mul]

end Cslib.Crypto
