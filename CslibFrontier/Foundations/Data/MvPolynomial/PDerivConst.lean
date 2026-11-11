/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, polynomials annihilated by partial derivatives)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomials annihilated by partial derivatives

Over a domain of characteristic zero, a multivariate polynomial all of whose partial derivatives
vanish is constant (`MvPolynomial.eq_C_of_pderiv_eq_zero`). Over any commutative semiring,
differentiating a polynomial more often than its total degree gives zero
(`MvPolynomial.iterate_pderiv_eq_zero`), so each partial derivative is locally nilpotent.

## Main results

* `MvPolynomial.eq_C_of_pderiv_eq_zero`: all partial derivatives zero implies constant.
* `MvPolynomial.iterate_pderiv_eq_zero`: `(pderiv i)^[k] p = 0` for `k > totalDegree p`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*}

/-- Over a domain of characteristic zero, a polynomial all of whose partial derivatives vanish is
constant. -/
theorem eq_C_of_pderiv_eq_zero [CommRing R] [IsDomain R] [CharZero R] {p : MvPolynomial σ R}
    (h : ∀ i, pderiv i p = 0) : p = C (constantCoeff p) := by
  classical
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_C]
  split_ifs with hm
  · rw [← hm, constantCoeff_eq]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hne
      exact hm (Finsupp.ext fun i => (not_not.1 fun hi => hne ⟨i, hi⟩).symm)
    have hsplit : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_eq_of_ne hj]
    have hc : (pderiv i p).coeff (m - Finsupp.single i 1) = 0 := by rw [h i]; simp
    rw [coeff_pderiv, hsplit] at hc
    exact (mul_eq_zero.1 hc).resolve_right (Nat.cast_add_one_ne_zero _)

private theorem coeff_iterate_pderiv_eq_zero [CommSemiring R] (i : σ) (k : ℕ) :
    ∀ (p : MvPolynomial σ R) (m : σ →₀ ℕ), p.coeff (m + Finsupp.single i k) = 0 →
      ((pderiv i)^[k] p).coeff m = 0 := by
  induction k with
  | zero => intro p m h; simpa using h
  | succ k ih =>
    intro p m h
    rw [Function.iterate_succ_apply]
    refine ih _ _ ?_
    rw [coeff_pderiv, add_assoc, ← Finsupp.single_add, h, zero_mul]

/-- Differentiating a polynomial more often than its total degree gives zero. -/
theorem iterate_pderiv_eq_zero [CommSemiring R] (i : σ) {p : MvPolynomial σ R} {k : ℕ}
    (hk : p.totalDegree < k) : (pderiv i)^[k] p = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  refine (coeff_iterate_pderiv_eq_zero i k p m (coeff_eq_zero_of_totalDegree_lt ?_)).trans
    (by simp)
  refine hk.trans_le ?_
  calc k = Finsupp.single i k i := by simp
    _ ≤ (m + Finsupp.single i k) i := by simp
    _ ≤ ∑ j ∈ (m + Finsupp.single i k).support, (m + Finsupp.single i k) j := by
        by_cases hi : i ∈ (m + Finsupp.single i k).support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _

end MvPolynomial
