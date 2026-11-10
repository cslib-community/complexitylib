/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Foundations.FieldTheory.Finite.UnitSum
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Monomials on lines of a finite field

Over a finite field `K` with `q` elements, the values of a polynomial of degree below `q - 1`
sum to zero (`FiniteField.sum_eval_eq_zero_of_natDegree_lt`). The restriction of a monomial
`∏ i, X i ^ e i` to an affine line can have degree up to `∑ i, e i`, but in characteristic two a
Frobenius twist lowers it. For `q = 2 ^ (r + s)`, substitute `x = y ^ 2 ^ r` and split
`e = e % 2 ^ s + 2 ^ s * (e / 2 ^ s)`; since `y ^ q = y`, the restriction becomes a polynomial in
`y` of degree at most `∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s)`; for `e i < q` this is the
total of the `(r + s)`-digit binary exponents rotated cyclically by `s` digits. When it is below
`q - 1` the line sum vanishes (`sum_prod_add_mul_pow_eq_zero`). No form of Lucas's theorem is
used.

## Main results

* `Cslib.LineCode.HighRate.sum_prod_add_mul_pow_eq_zero`: monomials with small rotated degree sum
  to zero on every affine line.

## References

* Adapted from MassProduction/HighRate/LineParity.lean,
  MassProduction/HighRate/PolynomialSupport.lean and MassProduction/LowDegree.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

public section

namespace Cslib.LineCode.HighRate

open Finset Polynomial

variable {K : Type*} [Field K] [Fintype K]

/-- **Frobenius twist.** Let `K` have `2 ^ (r + s)` elements. If the exponents `e i`, rotated by
`s` binary digits, have total `∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s)` below
`Fintype.card K - 1`, then the values of the monomial `∏ i, X i ^ e i` on the affine line
`x ↦ u + x • v` sum to zero. -/
theorem sum_prod_add_mul_pow_eq_zero [CharP K 2] {ι : Type*} [Fintype ι] {r s : ℕ}
    (hK : Fintype.card K = 2 ^ (r + s)) (u v : ι → K) (e : ι → ℕ)
    (he : ∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s) < Fintype.card K - 1) :
    ∑ x : K, ∏ i, (u i + x * v i) ^ e i = 0 := by
  -- Substitute `x = y ^ 2 ^ r`, a bijection with inverse `x ↦ x ^ 2 ^ s`.
  have hbij : Function.Bijective fun y : K => y ^ 2 ^ r := by
    refine Finite.injective_iff_bijective.mp
      (Function.LeftInverse.injective (g := fun y : K => y ^ 2 ^ s) fun y => ?_)
    change (y ^ 2 ^ r) ^ 2 ^ s = y
    rw [← pow_mul, ← pow_add, ← hK, FiniteField.pow_card]
  let P : K[X] := ∏ i, (C (u i) + C (v i) * X ^ 2 ^ r) ^ (e i % 2 ^ s) *
    (C (u i ^ 2 ^ s) + C (v i ^ 2 ^ s) * X) ^ (e i / 2 ^ s)
  have hP (y : K) : ∏ i, (u i + y ^ 2 ^ r * v i) ^ e i = P.eval y := by
    simp only [P, eval_prod, eval_mul, eval_pow, eval_add, eval_C, eval_X]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_lhs => rw [← Nat.mod_add_div (e i) (2 ^ s), pow_add, pow_mul, add_pow_char_pow,
      mul_pow, ← pow_mul, ← pow_add, ← hK, FiniteField.pow_card]
    ring
  have hdeg : P.natDegree ≤ ∑ i, (2 ^ r * (e i % 2 ^ s) + e i / 2 ^ s) := by
    refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine natDegree_mul_le.trans (add_le_add ?_ ?_)
    · refine (natDegree_pow_le_of_le _ ?_).trans (mul_comm _ _).le
      rw [natDegree_C_add]
      exact natDegree_C_mul_X_pow_le _ _
    · refine (natDegree_pow_le_of_le _ ?_).trans (mul_one _).le
      rw [natDegree_C_add]
      exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  rw [← hbij.sum_comp]
  simp only [hP]
  exact FiniteField.sum_eval_eq_zero_of_natDegree_lt (hdeg.trans_lt he)

end Cslib.LineCode.HighRate
