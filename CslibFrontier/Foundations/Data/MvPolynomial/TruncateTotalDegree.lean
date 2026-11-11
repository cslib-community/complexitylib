/-
Copyright (c) 2026 Vincent Palma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma
-/

module
-- upstream: candidate (Mathlib, total-degree truncation)

public import CslibFrontier.Init
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Truncating multivariate polynomials by total degree

`MvPolynomial.truncateTotalDegree D p` retains the monomials of `p` of total degree at most `D`.
Its linear-map interface `MvPolynomial.truncateTotalDegreeₗ D` projects onto Mathlib's submodule
`MvPolynomial.restrictTotalDegree V R D` and fixes every polynomial in that submodule.

Truncation commutes with multiplication by `p` when each monomial of the other factor either
stays below the cutoff after multiplication or starts above it. This gap criterion does not
require a domain or additive inverses.

## Main definitions

* `MvPolynomial.truncateTotalDegree`: computable truncation by total degree.
* `MvPolynomial.truncateTotalDegreeₗ`: the corresponding linear map.

## Main results

* `MvPolynomial.totalDegree_truncateTotalDegree_le`: the cutoff bounds the resulting degree.
* `MvPolynomial.truncateTotalDegree_eq_self_iff`: truncation fixes precisely the polynomials
  whose total degree is at most the cutoff.
* `MvPolynomial.range_truncateTotalDegreeₗ`: the range is the existing bounded-degree submodule.
* `MvPolynomial.truncateTotalDegree_mul_of_gap`: multiplication commutes with truncation under
  a gap in the degrees of the second factor's monomials.
-/

public section

namespace MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- Retain the monomials of total degree at most `D`. -/
def truncateTotalDegree (D : ℕ) (p : MvPolynomial V R) : MvPolynomial V R :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter fun m => m.degree ≤ D)

/-- Total-degree truncation as an `R`-linear map. -/
noncomputable def truncateTotalDegreeₗ (D : ℕ) : MvPolynomial V R →ₗ[R] MvPolynomial V R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
    Finsupp.restrictDom R R {m : V →₀ ℕ | m.degree ≤ D} ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The linear map agrees with computable truncation. -/
@[simp] theorem truncateTotalDegreeₗ_apply (D : ℕ) (p : MvPolynomial V R) :
    truncateTotalDegreeₗ D p = truncateTotalDegree D p := by rfl

/-- Truncation leaves a coefficient unchanged precisely below the cutoff. -/
@[simp] theorem coeff_truncateTotalDegree (D : ℕ) (p : MvPolynomial V R) (m : V →₀ ℕ) :
    (truncateTotalDegree D p).coeff m = if m.degree ≤ D then p.coeff m else 0 := by rfl

/-- The support of a truncation is the corresponding filtered support. -/
theorem support_truncateTotalDegree (D : ℕ) (p : MvPolynomial V R) :
    (truncateTotalDegree D p).support = p.support.filter (fun m => m.degree ≤ D) := by rfl

/-- Truncation does not increase the number of monomials. -/
theorem card_support_truncateTotalDegree_le (D : ℕ) (p : MvPolynomial V R) :
    (truncateTotalDegree D p).support.card ≤ p.support.card :=
  Finset.card_filter_le _ _

/-- Truncation has total degree at most the cutoff. -/
theorem totalDegree_truncateTotalDegree_le (D : ℕ) (p : MvPolynomial V R) :
    (truncateTotalDegree D p).totalDegree ≤ D := by
  rw [totalDegree, support_truncateTotalDegree, Finset.sup_le_iff]
  exact fun m hm => (Finset.mem_filter.mp hm).2

/-- Truncation fixes every polynomial whose total degree is at most the cutoff. -/
theorem truncateTotalDegree_eq_self {D : ℕ} {p : MvPolynomial V R} (h : p.totalDegree ≤ D) :
    truncateTotalDegree D p = p := by
  ext m
  rw [coeff_truncateTotalDegree]
  split_ifs with hm
  · rfl
  · exact (coeff_eq_zero_of_totalDegree_lt (h.trans_lt (lt_of_not_ge hm))).symm

/-- Truncation fixes precisely the polynomials whose total degree is at most the cutoff. -/
@[simp] theorem truncateTotalDegree_eq_self_iff (D : ℕ) (p : MvPolynomial V R) :
    truncateTotalDegree D p = p ↔ p.totalDegree ≤ D := by
  constructor
  · intro h
    rw [← h]
    exact totalDegree_truncateTotalDegree_le D p
  · exact truncateTotalDegree_eq_self

/-- Applying the same truncation twice has the same effect as applying it once. -/
@[simp] theorem truncateTotalDegree_idem (D : ℕ) (p : MvPolynomial V R) :
    truncateTotalDegree D (truncateTotalDegree D p) = truncateTotalDegree D p :=
  truncateTotalDegree_eq_self (totalDegree_truncateTotalDegree_le D p)

/-- The range of truncation is Mathlib's submodule of polynomials of bounded total degree. -/
theorem range_truncateTotalDegreeₗ (D : ℕ) :
    LinearMap.range (truncateTotalDegreeₗ (V := V) (R := R) D) = restrictTotalDegree V R D := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (mem_restrictTotalDegree _ _ _).2 (totalDegree_truncateTotalDegree_le D q)
  · intro hp
    exact ⟨p, truncateTotalDegree_eq_self ((mem_restrictTotalDegree _ _ _).1 hp)⟩

/-- Truncation preserves the constant polynomial `1`. -/
@[simp] theorem truncateTotalDegree_one (D : ℕ) :
    truncateTotalDegree D (1 : MvPolynomial V R) = 1 :=
  truncateTotalDegree_eq_self (by simp)

/-- Truncating zero gives zero. -/
@[simp] theorem truncateTotalDegree_zero (D : ℕ) :
    truncateTotalDegree D (0 : MvPolynomial V R) = 0 :=
  map_zero (truncateTotalDegreeₗ D)

/-- Truncation commutes with finite sums. -/
theorem truncateTotalDegree_sum {ι : Type*} (D : ℕ) (s : Finset ι)
    (p : ι → MvPolynomial V R) :
    truncateTotalDegree D (∑ i ∈ s, p i) = ∑ i ∈ s, truncateTotalDegree D (p i) :=
  map_sum (truncateTotalDegreeₗ D) p s

/-- Truncation commutes with multiplication when no monomial of the second factor can cross
the cutoff. The hypothesis uses the total degree of the first factor, so it remains sufficient
over semirings with zero divisors or cancellation of coefficients. -/
theorem truncateTotalDegree_mul_of_gap (D : ℕ) (p q : MvPolynomial V R)
    (hgap : ∀ m ∈ q.support, m.degree + p.totalDegree ≤ D ∨ D < m.degree) :
    truncateTotalDegree D (p * q) = p * truncateTotalDegree D q := by
  classical
  ext m
  rw [coeff_truncateTotalDegree, coeff_mul, coeff_mul]
  have hdeg {a b : V →₀ ℕ} (hab : (a, b) ∈ Finset.antidiagonal m) :
      m.degree = a.degree + b.degree := by
    rw [← Finset.mem_antidiagonal.mp hab, map_add]
  by_cases hm : m.degree ≤ D
  · rw [ite_eq_left hm]
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ hab
    have hb : b.degree ≤ D := by have := hdeg hab; omega
    rw [coeff_truncateTotalDegree, ite_eq_left hb]
  · rw [ite_eq_right hm]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    by_cases ha : p.coeff a = 0
    · simp [ha]
    by_cases hb : q.coeff b = 0
    · simp [hb]
    have ha' : a.degree ≤ p.totalDegree := le_totalDegree (mem_support_iff.mpr ha)
    have hgap' := hgap b (mem_support_iff.mpr hb)
    have hb' : ¬b.degree ≤ D := by have := hdeg hab; omega
    simp [hb']

end MvPolynomial
