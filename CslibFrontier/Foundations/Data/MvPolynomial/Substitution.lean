/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, degree bound for substitution)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Total degree under substitution

Substituting polynomials of total degree at most `k` for the variables of a polynomial `P`
multiplies the total degree by at most `k` (`MvPolynomial.totalDegree_aeval_le_mul`). In
particular, an affine change of variables does not raise the total degree
(`MvPolynomial.totalDegree_aeval_le`). The same bound holds for the degree of a substitution of
univariate polynomials (`MvPolynomial.natDegree_aeval_le_mul`).

## Main results

* `MvPolynomial.totalDegree_aeval_le_mul`: substituting polynomials of degree at most `k`
  multiplies the degree by at most `k`.
* `MvPolynomial.totalDegree_aeval_le`: substituting polynomials of degree at most `1` does not raise
  the degree.
* `MvPolynomial.natDegree_aeval_le_mul`: substituting univariate polynomials of degree at most
  `k` gives a polynomial of degree at most `k` times the total degree.
* `MvPolynomial.eval_polynomial_aeval`: evaluating a substitution of univariate polynomials.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- Substituting polynomials of total degree at most `k` for the variables multiplies the total
degree by at most `k`. -/
theorem totalDegree_aeval_le_mul {g : τ → MvPolynomial σ R} {k : ℕ}
    (hg : ∀ i, (g i).totalDegree ≤ k) (P : MvPolynomial τ R) :
    (aeval g P).totalDegree ≤ P.totalDegree * k := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (g i ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i * k :=
        Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = (s.sum fun _ e => e) * k := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ P.totalDegree * k := Nat.mul_le_mul_right _ (le_totalDegree hs)

/-- Substituting polynomials of total degree at most `1` for the variables does not raise the total
degree. -/
theorem totalDegree_aeval_le {g : τ → MvPolynomial σ R} (hg : ∀ i, (g i).totalDegree ≤ 1)
    (P : MvPolynomial τ R) : (aeval g P).totalDegree ≤ P.totalDegree :=
  (totalDegree_aeval_le_mul hg P).trans_eq (Nat.mul_one _)

/-- Substituting univariate polynomials of degree at most `k` for the variables gives a
polynomial of degree at most `k` times the total degree. -/
theorem natDegree_aeval_le_mul {g : τ → Polynomial R} {k : ℕ} (hg : ∀ i, (g i).natDegree ≤ k)
    (P : MvPolynomial τ R) : (aeval g P).natDegree ≤ P.totalDegree * k := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [aeval_monomial, Finsupp.prod]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ s.support, (g i ^ s i).natDegree
      ≤ ∑ i ∈ s.support, s i * k :=
        Finset.sum_le_sum fun i _ =>
          Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))
    _ = (s.sum fun _ e => e) * k := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ P.totalDegree * k := Nat.mul_le_mul_right _ (le_totalDegree hs)

/-- Evaluating a substitution of univariate polynomials at `x` evaluates the polynomial at the
values of the substituted polynomials at `x`. -/
theorem eval_polynomial_aeval (g : τ → Polynomial R) (P : MvPolynomial τ R) (x : R) :
    Polynomial.eval x (aeval g P) = eval (fun i => Polynomial.eval x (g i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end MvPolynomial
