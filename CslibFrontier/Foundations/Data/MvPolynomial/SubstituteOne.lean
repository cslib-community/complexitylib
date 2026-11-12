/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomials that vanish when a variable is set to one

The substitution `X j ↦ 1` removes `X j` from every monomial and keeps the coefficients
(`MvPolynomial.aeval_update_X_one_monomial`). A nonzero polynomial that it sends to zero therefore
has two monomials that differ in the exponent of `X j`. Repeating this for each variable of a
finite set `Y` shows that a nonzero polynomial sent to zero by every substitution `X j ↦ 1`,
`j ∈ Y`, has at least `2 ^ Y.card` monomials. The product `∏ j ∈ Y, (X j - 1)` attains the bound.

## Main results

* `MvPolynomial.coeff_aeval_update_X_one`: the coefficients after the substitution `X j ↦ 1`.
* `MvPolynomial.two_pow_card_le_card_support`: the bound on the number of monomials.
-/

public section

namespace MvPolynomial

open Finset

variable {σ R : Type*} [DecidableEq σ] [CommSemiring R]

/-- The substitution `X j ↦ 1` removes `X j` from a monomial. -/
theorem aeval_update_X_one_monomial (j : σ) (m : σ →₀ ℕ) (a : R) :
    aeval (Function.update (X : σ → MvPolynomial σ R) j 1) (monomial m a) =
      monomial (m.erase j) a := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod, Finsupp.prod,
    Finsupp.support_erase,
    ← Finset.prod_erase m.support (a := j) (by rw [Function.update_self, one_pow])]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi), Finsupp.erase_ne (ne_of_mem_erase hi)]

/-- The coefficient of `m'` after the substitution `X j ↦ 1` is the sum of the coefficients of the
monomials that become `m'` when `X j` is removed. -/
theorem coeff_aeval_update_X_one {Q : MvPolynomial σ R} {S : Finset (σ →₀ ℕ)}
    (hS : Q.support ⊆ S) (j : σ) (m' : σ →₀ ℕ) :
    (aeval (Function.update (X : σ → MvPolynomial σ R) j 1) Q).coeff m' =
      ∑ m ∈ S with m.erase j = m', Q.coeff m := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, coeff_sum, sum_filter]
  simp_rw [aeval_update_X_one_monomial, coeff_monomial]
  exact sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, ite_self]

/-- The combinatorial form of `two_pow_card_le_card_support`, for a set `S` of monomials with
nonzero coefficients `c`. -/
private theorem two_pow_card_le_card_aux {A : Type*} [AddCommMonoid A] (c : (σ →₀ ℕ) → A)
    (Y : Finset σ) : ∀ S : Finset (σ →₀ ℕ), S.Nonempty → (∀ m ∈ S, c m ≠ 0) →
      (∀ j ∈ Y, ∀ m', ∑ m ∈ S with m.erase j = m', c m = 0) → 2 ^ Y.card ≤ S.card := by
  induction Y using Finset.induction_on with
  | empty => exact fun S hS _ _ => hS.card_pos
  | insert j Y hj ih =>
    rintro S ⟨m₀, hm₀⟩ hc h
    -- a part of `S` cut out by a condition on the exponent of `X j` inherits the hypotheses
    have key : ∀ (P : (σ →₀ ℕ) → Prop) [DecidablePred P], (∀ i ∈ Y, ∀ m, P (m.erase i) ↔ P m) →
        ∀ m ∈ S, P m → 2 ^ Y.card ≤ (S.filter P).card := fun P _ hP m₁ hm₁ hPm₁ =>
      ih _ ⟨m₁, mem_filter.2 ⟨hm₁, hPm₁⟩⟩ (fun m hm => hc m (mem_of_mem_filter m hm))
        fun i hi m' => by
          rw [filter_filter]
          by_cases hm' : P m'
          · rw [← h i (mem_insert_of_mem hi) m']
            exact sum_congr (filter_congr fun m _ =>
              ⟨fun h => h.2, fun h => ⟨(hP i hi m).1 (h ▸ hm'), h⟩⟩) fun _ _ => rfl
          · rw [filter_eq_empty_iff.2 fun m _ (hm : P m ∧ m.erase i = m') =>
              hm' (hm.2 ▸ (hP i hi m).2 hm.1), sum_empty]
    have hP : ∀ i ∈ Y, ∀ m : σ →₀ ℕ, (m.erase i) j = m₀ j ↔ m j = m₀ j := fun i hi m => by
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hi hj).symm]
    -- the substitution `X j ↦ 1` forces a second exponent of `X j`
    obtain ⟨m₁, hm₁, hne⟩ : ∃ m₁ ∈ S, m₁ j ≠ m₀ j := by
      by_contra hcon
      push Not at hcon
      refine hc m₀ hm₀ ?_
      rw [← h j (mem_insert_self j Y) (m₀.erase j)]
      have hmem : m₀ ∈ S.filter fun m => m.erase j = m₀.erase j := mem_filter.2 ⟨hm₀, rfl⟩
      refine (sum_eq_single_of_mem m₀ hmem fun m hm hmne => ?_).symm
      rw [mem_filter] at hm
      refine absurd (Finsupp.ext fun i => ?_) hmne
      by_cases hi : i = j
      · rw [hi, hcon m hm.1]
      · simpa only [Finsupp.erase_ne hi] using DFunLike.congr_fun hm.2 i
    have h₀ := key (fun m => m j = m₀ j) hP m₀ hm₀ rfl
    have h₁ := key (fun m => ¬m j = m₀ j) (fun i hi m => not_congr (hP i hi m)) m₁ hm₁ hne
    rw [card_insert_of_notMem hj, pow_succ, mul_two,
      ← card_filter_add_card_filter_not (s := S) fun m => m j = m₀ j]
    exact Nat.add_le_add h₀ h₁

/-- A nonzero polynomial that becomes zero under each of the substitutions `X j ↦ 1`, `j ∈ Y`,
has at least `2 ^ Y.card` monomials. -/
theorem two_pow_card_le_card_support {Y : Finset σ} {Q : MvPolynomial σ R} (hQ : Q ≠ 0)
    (h : ∀ j ∈ Y, aeval (Function.update (X : σ → MvPolynomial σ R) j 1) Q = 0) :
    2 ^ Y.card ≤ Q.support.card :=
  two_pow_card_le_card_aux Q.coeff Y Q.support (support_nonempty.2 hQ)
    (fun _ => mem_support_iff.1) fun j hj m' => by
      rw [← coeff_aeval_update_X_one subset_rfl, h j hj]
      rfl

end MvPolynomial
