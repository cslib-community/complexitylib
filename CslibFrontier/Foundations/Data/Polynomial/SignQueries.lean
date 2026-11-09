/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sign-pattern counts from integer product queries

A quadratic polynomial on `{-1, 0, 1}` gives twice the indicator of a requested sign.
Multiplying these indicators expresses `2 ^ k` times a sign-pattern count as an integer
combination of `3 ^ k` product-sign queries. No division or selection of matrix rows is needed.

For a polynomial's roots, the queries and counts use `roots.toFinset`, so each distinct real
root contributes once, independently of its multiplicity. Mathlib assigns the zero polynomial
an empty root multiset. The equivalence with existence of a real root therefore requires a
nonzero polynomial.

This is a counting identity. It does not supply an algorithm for evaluating a sign query or a
time or space bound for sign determination.

## Main definitions

* `Cslib.SignQueries.signCount`: the number of points realizing a sign pattern.
* `Cslib.SignQueries.weight`: the coefficients of the quadratics giving twice the indicator of a
  sign.
* `Cslib.SignQueries.patternWeight`: the coefficient of an exponent vector in the expanded
  indicator product.
* `Cslib.SignQueries.queryPolynomial`: a product with exponents in `{0, 1, 2}`.
* `Cslib.SignQueries.signSum`: the sum of the signs of a polynomial on a finite set of points.
* `Cslib.SignQueries.tarskiQuery`: the sum of signs at distinct real roots.
* `Cslib.SignQueries.scaledRootCount`: the integer combination of root sign queries.

## Main results

* `Cslib.SignQueries.weighted_queries_eq_count`: the finite sign-pattern counting identity.
* `Cslib.SignQueries.scaledRootCount_eq`: its specialization to distinct real roots.
* `Cslib.SignQueries.scaledRootCount_pos_iff`: for a nonzero polynomial, a positive scaled
  count is equivalent to existence of a root realizing the requested sign pattern.

## References

Adapted from LeanCanny/Algebra/ScaledSignQueries.lean in [LeanCanny2026].
-/

@[expose] public section

namespace Cslib.SignQueries

open Polynomial
open scoped BigOperators

/-- The coefficient of `X ^ e` in the quadratic that gives twice the indicator of sign `s`.
The three quadratics are `2 - 2 * X ^ 2`, `X ^ 2 - X`, and `X ^ 2 + X`. -/
def weight (s : SignType) (e : Fin 3) : ℤ :=
  match s, e.val with
  | .zero, 0 => 2
  | .zero, 2 => -2
  | .neg, 1 => -1
  | .neg, 2 => 1
  | .pos, 1 => 1
  | .pos, 2 => 1
  | _, _ => 0

/-- Evaluating a sign's quadratic at another sign gives twice the equality indicator. -/
private theorem weight_indicator (s t : SignType) :
    (∑ e : Fin 3, weight s e * (t : ℤ) ^ e.val) = if t = s then 2 else 0 := by
  cases s <;> cases t <;> decide

/-- There are `3 ^ k` exponent choices for a family of `k` polynomials. -/
theorem query_count {J : Type*} [Fintype J] [DecidableEq J] :
    Fintype.card (J → Fin 3) = 3 ^ Fintype.card J := by
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- The coefficient assigned to an exponent vector when expanding the indicator product. -/
def patternWeight {J : Type*} [Fintype J] (σ : J → SignType) (e : J → Fin 3) : ℤ :=
  ∏ i, weight (σ i) (e i)

/-- Expanding the product of the sign quadratics gives the scaled pattern indicator. -/
private theorem product_indicator {J : Type*} [Fintype J] [DecidableEq J] (σ t : J → SignType) :
    (∑ e : J → Fin 3, patternWeight σ e * ∏ i, (t i : ℤ) ^ (e i).val) =
      if t = σ then 2 ^ Fintype.card J else 0 := by
  classical
  calc
    _ = ∑ e : J → Fin 3, ∏ i, weight (σ i) (e i) * (t i : ℤ) ^ (e i).val := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ∏ i, ∑ e : Fin 3, weight (σ i) e * (t i : ℤ) ^ e.val :=
      (Fintype.prod_sum (fun (i : J) (e : Fin 3) => weight (σ i) e * (t i : ℤ) ^ e.val)).symm
    _ = ∏ i, if t i = σ i then (2 : ℤ) else 0 := by simp only [weight_indicator]
    _ = _ := by
      by_cases h : t = σ
      · subst t
        simp
      · rw [ite_eq_right h]
        obtain ⟨i, hi⟩ : ∃ i, t i ≠ σ i := by
          simpa only [funext_iff, not_forall] using h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])

/-- The sum of the signs of `q` on a finite set of real points. -/
noncomputable def signSum (Z : Finset ℝ) (q : ℝ[X]) : ℤ :=
  ∑ x ∈ Z, (SignType.sign (q.eval x) : ℤ)

open Classical in
/-- The number of points in `Z` at which every polynomial has its requested sign. -/
noncomputable def signCount {J : Type*} (Z : Finset ℝ) (Q : J → ℝ[X])
    (σ : J → SignType) : ℕ :=
  (Z.filter fun x => ∀ i, SignType.sign ((Q i).eval x) = σ i).card

/-- The product query polynomial, with each input polynomial raised to `0`, `1`, or `2`. -/
noncomputable def queryPolynomial {R : Type*} [CommSemiring R] {J : Type*} [Fintype J]
    (Q : J → R[X]) (e : J → Fin 3) : R[X] :=
  ∏ i, Q i ^ (e i).val

/-- The sign of a query polynomial is the product of the corresponding powers of signs. -/
private theorem sign_eval_queryPolynomial {J : Type*} [Fintype J]
    (Q : J → ℝ[X]) (e : J → Fin 3) (x : ℝ) :
    (SignType.sign ((queryPolynomial Q e).eval x) : ℤ) =
      ∏ i, (SignType.sign ((Q i).eval x) : ℤ) ^ (e i).val := by
  let φ : ℝ →*₀ ℤ := SignType.castHom.comp signHom
  change φ ((queryPolynomial Q e).eval x) = ∏ i, φ ((Q i).eval x) ^ (e i).val
  simp only [queryPolynomial, Polynomial.eval_prod, Polynomial.eval_pow, map_prod, map_pow]

/-- The weighted product-sign queries equal `2 ^ k` times the number of matching points. -/
theorem weighted_queries_eq_count {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset ℝ) (Q : J → ℝ[X]) (σ : J → SignType) :
    (∑ e : J → Fin 3, patternWeight σ e * signSum Z (queryPolynomial Q e)) =
      2 ^ Fintype.card J * (signCount Z Q σ : ℤ) := by
  classical
  simp only [signSum, Finset.mul_sum, sign_eval_queryPolynomial]
  rw [Finset.sum_comm]
  simp_rw [product_indicator]
  have heq (x : ℝ) : (fun i => SignType.sign ((Q i).eval x)) = σ ↔
      ∀ i, SignType.sign ((Q i).eval x) = σ i := funext_iff
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, signCount]
  rw [mul_comm]
  congr 1
  apply congrArg (fun s : Finset ℝ => (s.card : ℤ))
  ext x
  simp only [Finset.mem_filter]

/-- The Tarski query of `q` at the distinct real roots of `p`.
For `p = 0`, this is zero by Mathlib's root-multiset convention. -/
noncomputable def tarskiQuery (p q : ℝ[X]) : ℤ := signSum p.roots.toFinset q

/-- The weighted sum of product-sign queries for roots realizing a sign pattern. -/
noncomputable def scaledRootCount {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) : ℤ :=
  ∑ e : J → Fin 3, patternWeight σ e * tarskiQuery p (queryPolynomial Q e)

/-- The scaled count is `2 ^ k` times the number of distinct matching real roots. -/
theorem scaledRootCount_eq {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ[X]) (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount p Q σ = 2 ^ Fintype.card J * (signCount p.roots.toFinset Q σ : ℤ) :=
  weighted_queries_eq_count p.roots.toFinset Q σ

/-- The zero polynomial's scaled count is zero, since its root multiset is empty. -/
@[simp] theorem scaledRootCount_zero_left {J : Type*} [Fintype J] [DecidableEq J]
    (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount 0 Q σ = 0 := by
  rw [scaledRootCount_eq]
  simp [signCount]

/-- For a nonzero polynomial, a positive count means a real root realizes the sign pattern. -/
theorem signCount_roots_pos_iff {J : Type*}
    (p : ℝ[X]) (hp : p ≠ 0) (Q : J → ℝ[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : ℝ, p.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i := by
  classical
  simp only [signCount, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Multiset.mem_toFinset,
    Polynomial.mem_roots hp, Polynomial.IsRoot.def]

/-- For a nonzero polynomial, the integer combination of sign queries is positive exactly
when a real root realizes the requested sign pattern. -/
theorem scaledRootCount_pos_iff {J : Type*} [Fintype J] [DecidableEq J]
    (p : ℝ[X]) (hp : p ≠ 0) (Q : J → ℝ[X]) (σ : J → SignType) :
    0 < scaledRootCount p Q σ ↔
      ∃ x : ℝ, p.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i := by
  rw [scaledRootCount_eq,
    mul_pos_iff_of_pos_left (by positivity : (0 : ℤ) < 2 ^ Fintype.card J), Int.natCast_pos,
    signCount_roots_pos_iff p hp]

end Cslib.SignQueries
