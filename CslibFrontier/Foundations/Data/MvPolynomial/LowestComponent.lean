/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, lowest homogeneous components)

public import CslibFrontier.Foundations.Data.MvPolynomial.PartialDerivatives
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Lowest homogeneous components

A polynomial `q` *starts in degree `e`* if its homogeneous components of degree less than `e`
vanish; this is the hypothesis `∀ j < e, homogeneousComponent j q = 0` of the results below. For
such a `q`, the product `r * q` also starts in degree `e`, and its component of degree `e` is the
constant coefficient of `r` times the component of `q`. Partial derivatives lower the degree of
every homogeneous component by one. Polynomials whose components in their starting degrees are
linearly independent are linearly independent. Substituting `c * y i` for the variables of a
polynomial that starts in degree `e` gives a multiple of `c ^ e`.

## Main results

* `MvPolynomial.homogeneousComponent_mul_eq_zero`, `MvPolynomial.homogeneousComponent_mul`: the
  product `r * q` starts where `q` does, with the constant coefficient of `r` as a factor.
* `MvPolynomial.homogeneousComponent_pderiv`, `MvPolynomial.homogeneousComponent_iteratedPDeriv`:
  homogeneous components of partial derivatives.
* `MvPolynomial.linearIndependent_of_homogeneousComponent`: polynomials with linearly independent
  lowest components are linearly independent.
* `MvPolynomial.aeval_mul_left_of_isHomogeneous`, `MvPolynomial.pow_dvd_aeval_mul_left`: scaling
  the point of a substitution.
-/

public section

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- A polynomial whose homogeneous components of degree less than `e` vanish has no monomial of
degree less than `e`. -/
theorem coeff_eq_zero_of_homogeneousComponent_eq_zero {q : MvPolynomial σ R} {e : ℕ}
    (hq : ∀ j < e, homogeneousComponent j q = 0) {d : σ →₀ ℕ} (hd : d.degree < e) :
    q.coeff d = 0 := by
  have h : (homogeneousComponent d.degree q).coeff d = 0 := by rw [hq _ hd]; rfl
  rwa [coeff_homogeneousComponent, ite_eq_left rfl] at h

/-- A polynomial all of whose homogeneous components vanish is zero. -/
theorem eq_zero_of_homogeneousComponent_eq_zero {q : MvPolynomial σ R}
    (hq : ∀ j, homogeneousComponent j q = 0) : q = 0 := by
  rw [← sum_homogeneousComponent q]
  exact Finset.sum_eq_zero fun j _ => hq j

/-- If the homogeneous components of `q` of degree less than `e` vanish, so do those of a
multiple of `q`. -/
theorem homogeneousComponent_mul_eq_zero {q : MvPolynomial σ R} {e : ℕ}
    (hq : ∀ j < e, homogeneousComponent j q = 0) (r : MvPolynomial σ R) {j : ℕ} (hj : j < e) :
    homogeneousComponent j (r * q) = 0 := by
  classical
  ext d
  rw [coeff_homogeneousComponent]
  change _ = 0
  split_ifs with hd
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have h := congrArg Finsupp.degree (Finset.mem_antidiagonal.1 hx)
    rw [map_add] at h
    rw [coeff_eq_zero_of_homogeneousComponent_eq_zero hq (by omega), mul_zero]
  · rfl

/-- If the homogeneous components of `q` of degree less than `e` vanish, the component of degree
`e` of `r * q` is the constant coefficient of `r` times the component of degree `e` of `q`. -/
theorem homogeneousComponent_mul {q : MvPolynomial σ R} {e : ℕ}
    (hq : ∀ j < e, homogeneousComponent j q = 0) (r : MvPolynomial σ R) :
    homogeneousComponent e (r * q) = r.coeff 0 • homogeneousComponent e q := by
  classical
  ext d
  rw [coeff_smul, coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · rw [coeff_mul, Finset.sum_eq_single (0, d)]
    · rfl
    · intro x hx hne
      have hx' := Finset.mem_antidiagonal.1 hx
      have h := congrArg Finsupp.degree hx'
      rw [map_add] at h
      have hx1 : x.1.degree ≠ 0 := fun h0 => hne (Prod.ext ((Finsupp.degree_eq_zero_iff _).1 h0)
        (by rwa [(Finsupp.degree_eq_zero_iff _).1 h0, zero_add] at hx'))
      rw [coeff_eq_zero_of_homogeneousComponent_eq_zero hq (by omega), mul_zero]
    · exact fun h => absurd (Finset.mem_antidiagonal.2 (zero_add d)) h
  · rw [smul_zero]

/-- The component of degree `j` of a partial derivative is the partial derivative of the
component of degree `j + 1`. -/
theorem homogeneousComponent_pderiv (j : ℕ) (i : σ) (q : MvPolynomial σ R) :
    homogeneousComponent j (pderiv i q) = pderiv i (homogeneousComponent (j + 1) q) := by
  ext d
  rw [coeff_homogeneousComponent, coeff_pderiv, coeff_pderiv, coeff_homogeneousComponent,
    map_add Finsupp.degree, Finsupp.degree_single]
  simp only [add_left_inj]
  split_ifs <;> simp

/-- The component of degree `j` of an iterated partial derivative of order `k` is the iterated
partial derivative of the component of degree `j + k`. -/
theorem homogeneousComponent_iteratedPDeriv {k : ℕ} (α : Fin k → σ) (j : ℕ)
    (q : MvPolynomial σ R) :
    homogeneousComponent j (iteratedPDeriv α q) =
      iteratedPDeriv α (homogeneousComponent (j + k) q) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [iteratedPDeriv_succ_apply, homogeneousComponent_pderiv, ih, iteratedPDeriv_succ_apply,
      add_right_comm, add_assoc]

/-- An iterated partial derivative of order greater than `m` kills a homogeneous polynomial of
degree `m`. -/
theorem iteratedPDeriv_homogeneousComponent_eq_zero {k m : ℕ} (hk : m < k) (α : Fin k → σ)
    (q : MvPolynomial σ R) : iteratedPDeriv α (homogeneousComponent m q) = 0 := by
  refine eq_zero_of_homogeneousComponent_eq_zero fun j => ?_
  rw [homogeneousComponent_iteratedPDeriv, homogeneousComponent_of_mem
    (homogeneousComponent_mem m q), ite_eq_right (by omega), map_zero]

section Substitution

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- Substituting `c * y i` for the variables of a monomial of degree `k` multiplies the value at
`y` by `c ^ k`. -/
theorem aeval_mul_left_monomial (c : S) (y : σ → S) (d : σ →₀ ℕ) (a : R) :
    aeval (fun i => c * y i) (monomial d a) = c ^ d.degree * aeval y (monomial d a) := by
  rw [aeval_monomial, aeval_monomial, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum,
    Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

/-- Substituting `c * y i` for the variables of a homogeneous polynomial of degree `k` multiplies
the value at `y` by `c ^ k`. -/
theorem aeval_mul_left_of_isHomogeneous {q : MvPolynomial σ R} {k : ℕ} (hq : q.IsHomogeneous k)
    (c : S) (y : σ → S) : aeval (fun i => c * y i) q = c ^ k * aeval y q := by
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_mul_left_monomial,
    not_not.1 fun h => mem_support_iff.1 hd (hq.coeff_eq_zero h)]

/-- If the homogeneous components of `q` of degree less than `k` vanish, substituting `c * y i`
for the variables gives a multiple of `c ^ k`. -/
theorem pow_dvd_aeval_mul_left {q : MvPolynomial σ R} {k : ℕ}
    (hq : ∀ j < k, homogeneousComponent j q = 0) (c : S) (y : σ → S) :
    c ^ k ∣ aeval (fun i => c * y i) q := by
  conv_rhs => rw [q.as_sum]
  rw [map_sum]
  refine Finset.dvd_sum fun d hd => ?_
  rw [aeval_mul_left_monomial]
  refine Dvd.dvd.mul_right (pow_dvd_pow _ (not_lt.1 fun h => ?_)) _
  exact mem_support_iff.1 hd (coeff_eq_zero_of_homogeneousComponent_eq_zero hq h)

end Substitution

end CommSemiring

/-- Polynomials are linearly independent if their lowest homogeneous components are: if the
components of `F i` of degree less than `e i` vanish and the components of degree `e i` of the
`F i` are linearly independent, then the `F i` are linearly independent. -/
theorem linearIndependent_of_homogeneousComponent [CommRing R] {ι : Type*}
    {F : ι → MvPolynomial σ R} {e : ι → ℕ} (hlow : ∀ i, ∀ j < e i, homogeneousComponent j (F i) = 0)
    (hF : LinearIndependent R fun i => homogeneousComponent (e i) (F i)) :
    LinearIndependent R F := by
  classical
  rw [linearIndependent_iff']
  intro t c hc i hi
  by_contra hci
  obtain ⟨i₀, hi₀, hmin⟩ := (t.filter (c · ≠ 0)).exists_min_image e
    ⟨i, Finset.mem_filter.2 ⟨hi, hci⟩⟩
  have h := congrArg (homogeneousComponent (e i₀)) hc
  rw [map_sum, map_zero] at h
  have h' : ∑ i ∈ t, (if e i = e i₀ then c i else 0) • homogeneousComponent (e i) (F i) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul]
    split_ifs with he
    · rw [he]
    · rw [zero_smul]
      by_cases hc0 : c i = 0
      · rw [hc0, zero_smul]
      · rw [hlow i _ (lt_of_le_of_ne (hmin i (Finset.mem_filter.2 ⟨hi, hc0⟩)) (Ne.symm he)),
          smul_zero]
  have h0 := linearIndependent_iff'.1 hF t _ h' i₀ (Finset.mem_filter.1 hi₀).1
  rw [ite_eq_left rfl] at h0
  exact (Finset.mem_filter.1 hi₀).2 h0

end MvPolynomial
