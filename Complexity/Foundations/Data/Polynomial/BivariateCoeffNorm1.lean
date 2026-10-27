/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.CoeffNorm1
import Mathlib.Data.Finset.Sum

/-!
# Total `ℓ₁` Coefficient Norm of Bivariate Integer Polynomials

This module defines the total bivariate `ℓ₁` coefficient norm `Polynomial.bivariateCoeffNorm1` of a
polynomial `P : Polynomial (Polynomial ℤ)` (representing `P(T, V) ∈ ℤ[T][V]`), defined as the sum
over `s ∈ P.support` of `(P.coeff s).coeffNorm1`, and proves its basic triangle and
submultiplicativity inequalities. These bounds are used in Appendix B.2 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] to bound the coefficient size
of cleared-denominator parity-amplifier products.

## Main definitions

* `Polynomial.bivariateCoeffNorm1`: the total `ℓ₁` norm
  `∑ s ∈ P.support, (P.coeff s).coeffNorm1` of `P : Polynomial (Polynomial ℤ)`.

## Main results

* `Polynomial.coeffNorm1_coeff_le_bivariateCoeffNorm1`: every `V^s`-coefficient has `coeffNorm1`
  at most `P.bivariateCoeffNorm1`.
* `Polynomial.bivariateCoeffNorm1_add_le`, `Polynomial.bivariateCoeffNorm1_sum_le`: triangle
  inequalities for `bivariateCoeffNorm1`.
* `Polynomial.bivariateCoeffNorm1_mul_le`, `Polynomial.bivariateCoeffNorm1_prod_le`:
  submultiplicativity of `bivariateCoeffNorm1` on `Polynomial (Polynomial ℤ)`.
-/

@[expose] public noncomputable section

namespace Polynomial

open Finset

/-- The total bivariate `ℓ₁` coefficient norm `∑ s ∈ P.support, (P.coeff s).coeffNorm1` of a
polynomial `P : Polynomial (Polynomial ℤ)`. -/
def bivariateCoeffNorm1 (P : Polynomial (Polynomial ℤ)) : ℕ :=
  ∑ s ∈ P.support, (P.coeff s).coeffNorm1

/-- `bivariateCoeffNorm1 0 = 0`. -/
@[simp]
theorem bivariateCoeffNorm1_zero : bivariateCoeffNorm1 0 = 0 := by
  simp only [bivariateCoeffNorm1, support_zero, sum_empty]

/-- `bivariateCoeffNorm1 (C c) = c.coeffNorm1`. -/
@[simp]
theorem bivariateCoeffNorm1_C (c : Polynomial ℤ) :
    (C c).bivariateCoeffNorm1 = c.coeffNorm1 := by
  by_cases hc : c = 0
  · subst hc
    simp only [C_0, bivariateCoeffNorm1_zero, coeffNorm1_zero]
  · rw [bivariateCoeffNorm1, support_C hc, sum_singleton, coeff_C_zero]

/-- `bivariateCoeffNorm1 1 = 1`. -/
@[simp]
theorem bivariateCoeffNorm1_one : (1 : Polynomial (Polynomial ℤ)).bivariateCoeffNorm1 = 1 := by
  rw [← C_1, bivariateCoeffNorm1_C, coeffNorm1_one]

/-- Every `V^s`-coefficient of `P` has `coeffNorm1` at most `P.bivariateCoeffNorm1`. -/
theorem coeffNorm1_coeff_le_bivariateCoeffNorm1 (P : Polynomial (Polynomial ℤ)) (s : ℕ) :
    (P.coeff s).coeffNorm1 ≤ P.bivariateCoeffNorm1 := by
  by_cases hs : s ∈ P.support
  · exact single_le_sum (f := fun i => (P.coeff i).coeffNorm1) (fun _ _ => Nat.zero_le _) hs
  · rw [notMem_support_iff.mp hs, coeffNorm1_zero]
    exact Nat.zero_le _

/-- If `P.support ⊆ S`, then `P.bivariateCoeffNorm1 = ∑ s ∈ S, (P.coeff s).coeffNorm1`. -/
theorem bivariateCoeffNorm1_eq_sum_of_support_subset {P : Polynomial (Polynomial ℤ)}
    {S : Finset ℕ} (hS : P.support ⊆ S) :
    P.bivariateCoeffNorm1 = ∑ s ∈ S, (P.coeff s).coeffNorm1 := by
  rw [bivariateCoeffNorm1]
  refine sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.mp hs, coeffNorm1_zero]

/-- Triangle inequality for `bivariateCoeffNorm1`. -/
theorem bivariateCoeffNorm1_add_le (P Q : Polynomial (Polynomial ℤ)) :
    (P + Q).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 + Q.bivariateCoeffNorm1 := by
  classical
  let S := P.support ∪ Q.support
  have hPQ : (P + Q).support ⊆ S := support_add
  have hP : P.support ⊆ S := subset_union_left
  have hQ : Q.support ⊆ S := subset_union_right
  rw [bivariateCoeffNorm1_eq_sum_of_support_subset hPQ,
    bivariateCoeffNorm1_eq_sum_of_support_subset hP,
    bivariateCoeffNorm1_eq_sum_of_support_subset hQ, ← sum_add_distrib]
  refine sum_le_sum fun s _ => ?_
  rw [coeff_add]
  exact coeffNorm1_add_le _ _

/-- Finite-sum triangle inequality for `bivariateCoeffNorm1`. -/
theorem bivariateCoeffNorm1_sum_le {α : Type*} (s : Finset α)
    (f : α → Polynomial (Polynomial ℤ)) :
    (∑ a ∈ s, f a).bivariateCoeffNorm1 ≤ ∑ a ∈ s, (f a).bivariateCoeffNorm1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, bivariateCoeffNorm1_zero, le_rfl]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (bivariateCoeffNorm1_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Multiplying by `C c` (`c : Polynomial ℤ`) scales `bivariateCoeffNorm1` by at most
`c.coeffNorm1`. -/
theorem bivariateCoeffNorm1_C_mul_le (c : Polynomial ℤ) (P : Polynomial (Polynomial ℤ)) :
    (C c * P).bivariateCoeffNorm1 ≤ c.coeffNorm1 * P.bivariateCoeffNorm1 := by
  have hsub : (C c * P).support ⊆ P.support := by
    intro s hs
    rw [mem_support_iff, coeff_C_mul] at hs
    exact mem_support_iff.mpr (right_ne_zero_of_mul hs)
  calc
    (C c * P).bivariateCoeffNorm1
      ≤ ∑ s ∈ P.support, ((C c * P).coeff s).coeffNorm1 :=
        sum_le_sum_of_subset hsub
    _ ≤ ∑ s ∈ P.support, c.coeffNorm1 * (P.coeff s).coeffNorm1 := by
        refine sum_le_sum fun s _ => ?_
        rw [coeff_C_mul]
        exact coeffNorm1_mul_le _ _
    _ = c.coeffNorm1 * P.bivariateCoeffNorm1 := by
        rw [bivariateCoeffNorm1, mul_sum]

/-- Multiplying by `X ^ k` does not increase `bivariateCoeffNorm1`. -/
theorem bivariateCoeffNorm1_mul_X_pow_le (P : Polynomial (Polynomial ℤ)) (k : ℕ) :
    (P * X ^ k).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 := by
  rw [bivariateCoeffNorm1]
  have hsub :
      (P * X ^ k).support ⊆
        P.support.map ⟨fun i => i + k, add_left_injective k⟩ := by
    intro i hi
    rw [mem_support_iff] at hi
    rw [mem_map]
    by_cases hik : k ≤ i
    · refine ⟨i - k, ?_, by simp only [Function.Embedding.coeFn_mk]; omega⟩
      rw [mem_support_iff]
      intro h0
      apply hi
      have hi_eq : i = i - k + k := (Nat.sub_add_cancel hik).symm
      rw [hi_eq, coeff_mul_X_pow, h0]
    · exfalso
      apply hi
      rw [mul_comm, coeff_X_pow_mul']
      simp only [hik, ↓reduceIte]
  refine (sum_le_sum_of_subset hsub).trans ?_
  rw [sum_map]
  refine le_of_eq (sum_congr rfl fun i _ => ?_)
  simp only [Function.Embedding.coeFn_mk, coeff_mul_X_pow]

/-- `bivariateCoeffNorm1` is submultiplicative on `Polynomial (Polynomial ℤ)`. -/
theorem bivariateCoeffNorm1_mul_le (P Q : Polynomial (Polynomial ℤ)) :
    (P * Q).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 * Q.bivariateCoeffNorm1 := by
  have hdecomp : P * Q = ∑ i ∈ P.support, C (P.coeff i) * (Q * X ^ i) := by
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hdecomp]
  calc
    (∑ i ∈ P.support, C (P.coeff i) * (Q * X ^ i)).bivariateCoeffNorm1
      ≤ ∑ i ∈ P.support,
          (C (P.coeff i) * (Q * X ^ i)).bivariateCoeffNorm1 :=
        bivariateCoeffNorm1_sum_le _ _
    _ ≤ ∑ i ∈ P.support, (P.coeff i).coeffNorm1 * Q.bivariateCoeffNorm1 := by
        refine sum_le_sum fun i _ => ?_
        exact (bivariateCoeffNorm1_C_mul_le (P.coeff i) _).trans
          (Nat.mul_le_mul_left _ (bivariateCoeffNorm1_mul_X_pow_le Q i))
    _ = P.bivariateCoeffNorm1 * Q.bivariateCoeffNorm1 := by
        rw [← sum_mul, ← bivariateCoeffNorm1]

/-- `bivariateCoeffNorm1` of a power is at most the power of `bivariateCoeffNorm1`. -/
theorem bivariateCoeffNorm1_pow_le (P : Polynomial (Polynomial ℤ)) (n : ℕ) :
    (P ^ n).bivariateCoeffNorm1 ≤ P.bivariateCoeffNorm1 ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, bivariateCoeffNorm1_one, le_rfl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (bivariateCoeffNorm1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- `bivariateCoeffNorm1` of a finite product is at most the product of the
`bivariateCoeffNorm1`s. -/
theorem bivariateCoeffNorm1_prod_le {κ : Type*} (I : Finset κ)
    (F : κ → Polynomial (Polynomial ℤ)) :
    (∏ i ∈ I, F i).bivariateCoeffNorm1 ≤ ∏ i ∈ I, (F i).bivariateCoeffNorm1 := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [prod_empty, bivariateCoeffNorm1_one, le_rfl]
  | insert a I ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (bivariateCoeffNorm1_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

end Polynomial
