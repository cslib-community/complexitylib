/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

/-!
# Graded vanishing of the coefficients of a product

Give each factor `Q i` of a finite product of polynomials a weight `d i`, and suppose that the
`X ^ j` coefficient of `Q i` vanishes whenever `k (1 + 2 j) < d i`. Then the `X ^ t` coefficient of
`∏ i ∈ s, Q i` vanishes whenever `k (#s + 2 t) < ∑ i ∈ s, d i`. A coefficient `X ^ t` of the
product is a sum of products of coefficients `X ^ (j i)` with `∑ i, j i = t`, and each nonzero
factor coefficient has weight at most `k (1 + 2 j i)`.

This is the counting step behind the bound (D.1) in the proof of Lemma D.2 of [OpenAI2026ETH]
(p. 55), where `d i` counts the incidences of test `i` and `X` is the truncation variable `V`.

## Main results

* `Polynomial.coeff_prod_eq_zero_of_lt`: the graded vanishing of the coefficients of a product.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], proof of Lemma D.2, p. 55.
-/

public section

namespace Polynomial

open Finset

variable {κ A : Type*} [CommSemiring A]

/-- **Graded vanishing of the coefficients of a product.** Suppose the `X ^ j` coefficient of
`Q i` vanishes whenever `k (1 + 2 j) < d i`. Then the `X ^ t` coefficient of `∏ i ∈ s, Q i`
vanishes whenever `k (#s + 2 t) < ∑ i ∈ s, d i`. -/
theorem coeff_prod_eq_zero_of_lt (s : Finset κ) (Q : κ → A[X]) (d : κ → ℕ) (k : ℕ)
    (hQ : ∀ i ∈ s, ∀ j, k * (1 + 2 * j) < d i → (Q i).coeff j = 0) {t : ℕ}
    (ht : k * (#s + 2 * t) < ∑ i ∈ s, d i) : (∏ i ∈ s, Q i).coeff t = 0 := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp only [card_empty, zero_add, sum_empty, Nat.not_lt_zero] at ht
  | insert a s ha ih =>
    rw [prod_insert ha, coeff_mul]
    rw [sum_insert ha, card_insert_of_notMem ha] at ht
    refine sum_eq_zero fun uw huw => ?_
    rw [mem_antidiagonal] at huw
    by_cases hu : k * (1 + 2 * uw.1) < d a
    · rw [hQ a (mem_insert_self a s) uw.1 hu, zero_mul]
    · refine mul_eq_zero_of_right _ (ih (fun i hi => hQ i (mem_insert_of_mem hi)) ?_)
      have e₁ : k * (#s + 1 + 2 * t) = k * #s + k + 2 * (k * uw.1) + 2 * (k * uw.2) := by
        rw [← huw]
        ring
      have e₂ : k * (1 + 2 * uw.1) = k + 2 * (k * uw.1) := by ring
      have e₃ : k * (#s + 2 * uw.2) = k * #s + 2 * (k * uw.2) := by ring
      omega

end Polynomial
