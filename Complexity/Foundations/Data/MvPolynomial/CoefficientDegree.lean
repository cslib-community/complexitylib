/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Multivariate degree bounds for polynomial coefficients

In `Polynomial (MvPolynomial ι R)`, the outer variable is a Taylor variable `z`, and the
coefficient variables are formal `Xᵢ`. If coefficient `j` of every substituted input has
multivariate total degree at most `j`, the same is true after polynomial evaluation.

This is the algebraic closure behind equation (3.9), p24 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]. The coefficient ring can
be any commutative ring. No Taylor reconstruction, truncation or quotient identification is used.

## Main results

* `MvPolynomial.totalDegree_coeff_eval₂_le`: polynomial substitution preserves the coefficient
  degree bound.
* `MvPolynomial.totalDegree_X_le`: every formal variable `X i` has total degree at most `1`.
* `MvPolynomial.totalDegree_coeff_X_mul_map_le`: a scalar polynomial with zero constant term
  can multiply a formal variable while preserving the bound.
-/

open scoped BigOperators

namespace MvPolynomial

variable {ι κ R : Type*} [CommRing R]

private theorem coeff_degree_constant (a : R) (j : ℕ) :
    ((Polynomial.C (C a) : Polynomial (MvPolynomial ι R)).coeff j).totalDegree ≤ j := by
  by_cases hj : j = 0
  · subst j
    simp only [Polynomial.coeff_C_zero, totalDegree_C, Nat.le_refl]
  · rw [Polynomial.coeff_C_of_ne_zero hj]
    exact Nat.zero_le _

private theorem coeff_degree_add (p q : Polynomial (MvPolynomial ι R))
    (hp : ∀ j, (p.coeff j).totalDegree ≤ j) (hq : ∀ j, (q.coeff j).totalDegree ≤ j)
    (j : ℕ) : ((p + q).coeff j).totalDegree ≤ j := by
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hp j) (hq j))

private theorem coeff_degree_mul (p q : Polynomial (MvPolynomial ι R))
    (hp : ∀ j, (p.coeff j).totalDegree ≤ j) (hq : ∀ j, (q.coeff j).totalDegree ≤ j)
    (j : ℕ) : ((p * q).coeff j).totalDegree ≤ j := by
  rw [Polynomial.coeff_mul]
  apply totalDegree_finsetSum_le
  intro ab hab
  calc
    (p.coeff ab.1 * q.coeff ab.2).totalDegree ≤
        (p.coeff ab.1).totalDegree + (q.coeff ab.2).totalDegree := totalDegree_mul _ _
    _ ≤ ab.1 + ab.2 := Nat.add_le_add (hp ab.1) (hq ab.2)
    _ = j := Finset.mem_antidiagonal.mp hab

/-- If every input's coefficient `j` has total degree at most `j` in the formal variables,
then every coefficient of the substituted polynomial satisfies the same bound. Constants of
`R` are embedded as constants in both polynomial layers. -/
public theorem totalDegree_coeff_eval₂_le (p : MvPolynomial κ R)
    (Q : κ → Polynomial (MvPolynomial ι R))
    (hQ : ∀ v j, ((Q v).coeff j).totalDegree ≤ j) (j : ℕ) :
    ((eval₂ (Polynomial.C.comp C) Q p).coeff j).totalDegree ≤ j := by
  suffices h : ∀ j, ((eval₂ (Polynomial.C.comp C) Q p).coeff j).totalDegree ≤ j from h j
  induction p using MvPolynomial.induction_on with
  | C a =>
      intro j
      simpa only [eval₂_C, RingHom.coe_comp, Function.comp_apply] using
        (coeff_degree_constant (ι := ι) a j)
  | add p q hp hq =>
      intro j
      simpa only [eval₂_add] using coeff_degree_add _ _ hp hq j
  | mul_X p v hp =>
      intro j
      simpa only [eval₂_mul, eval₂_X] using coeff_degree_mul _ _ hp (hQ v) j

/-- Every formal variable `X i` has total degree at most `1`, without requiring `Nontrivial R`. -/
public theorem totalDegree_X_le {ι R : Type*} [CommSemiring R] (i : ι) :
    (X i : MvPolynomial ι R).totalDegree ≤ 1 := by
  change (monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
  exact (totalDegree_monomial_le _ _).trans (by simp)

/-- Every formal-variable occurrence in this correction carries a positive power of the outer
variable: the scalar polynomial's constant coefficient must be zero. Higher outer powers are
allowed, and no nontrivial-ring hypothesis is needed. -/
public theorem totalDegree_coeff_X_mul_map_le (i : ι) (delta : Polynomial R)
    (hzero : delta.coeff 0 = 0) (j : ℕ) :
    ((Polynomial.C (X i) * delta.map C).coeff j).totalDegree ≤ j := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  by_cases hj : j = 0
  · subst j
    simp only [hzero, map_zero, mul_zero, totalDegree_zero, Nat.le_refl]
  · calc
      (X i * C (delta.coeff j)).totalDegree ≤
          (X i : MvPolynomial ι R).totalDegree + (C (delta.coeff j)).totalDegree :=
        totalDegree_mul _ _
      _ ≤ 1 := by simpa only [totalDegree_C, add_zero] using totalDegree_X_le i
      _ ≤ j := Nat.one_le_iff_ne_zero.mpr hj

end MvPolynomial
