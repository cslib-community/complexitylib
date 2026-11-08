/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.List.GetD

/-!
# Polynomials as lists of their low coefficients

Mathlib's `Polynomial.ofCoeffList` builds a polynomial from its coefficients, the constant
coefficient first. This file evaluates such a polynomial by Horner's rule on the list
(`Polynomial.evalCoeffList`), bounds its degree by the length of the list less one, lists the first
`n` coefficients of a polynomial (`Polynomial.coeffsBelow`), which give the polynomial back when
its degree is less than `n`. An interactive verifier receives polynomials in this form.

Splitting a list splits the polynomial: `l₁ ++ l₂` gives
`ofCoeffList l₁ + X ^ l₁.length * ofCoeffList l₂` (`Polynomial.ofCoeffList_append`). Padding with
zeros does not change it (`Polynomial.ofCoeffList_takeD_of_length_le`), and the zero-padded first
`m + k` coefficients split into the first `m` and the next `k` (`Polynomial.ofCoeffList_takeD_add`).
Divide-and-conquer multiplication of coefficient lists uses these splits.

## Main definitions

* `Polynomial.evalCoeffList`: Horner evaluation of a coefficient list.
* `Polynomial.coeffsBelow`: the coefficients of `X ^ 0`, …, `X ^ (n - 1)`.

## Main results

* `Polynomial.eval_ofCoeffList`: evaluation is Horner's rule.
* `Polynomial.natDegree_ofCoeffList_le`: the degree is at most the length of the list less one.
* `Polynomial.ofCoeffList_coeffsBelow`: low coefficients determine a polynomial of small degree.
* `Polynomial.ofCoeffList_append`: concatenation is a shifted sum.
* `Polynomial.ofCoeffList_takeD_of_length_le`, `Polynomial.ofCoeffList_takeD_add`: zero padding and
  splitting a padded prefix.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- The value at `z` of the polynomial with coefficient list `l`, the constant coefficient first,
by Horner's rule. -/
def evalCoeffList (z : R) (l : List R) : R := l.foldr (fun a acc => a + z * acc) 0

/-- The empty coefficient list evaluates to `0`. -/
@[simp] theorem evalCoeffList_nil (z : R) : evalCoeffList z [] = 0 := rfl

/-- Horner's step: `a :: l` evaluates to `a + z * evalCoeffList z l`. -/
@[simp] theorem evalCoeffList_cons (z a : R) (l : List R) :
    evalCoeffList z (a :: l) = a + z * evalCoeffList z l := rfl

/-- The value of the polynomial with coefficient list `l` is given by Horner's rule. -/
theorem eval_ofCoeffList {R : Type*} [CommSemiring R] (z : R) (l : List R) :
    (ofCoeffList l).eval z = evalCoeffList z l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [ofCoeffList_cons, eval_add, eval_C, eval_mul, eval_X, ih,
      evalCoeffList_cons]

/-- The polynomial with coefficient list `l` has degree at most `l.length - 1`. -/
theorem natDegree_ofCoeffList_le (l : List R) : (ofCoeffList l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_ofCoeffList, List.getD_eq_default _ _ (by omega)]

/-- The coefficients of `X ^ 0`, …, `X ^ (n - 1)` of a polynomial, in this order. -/
def coeffsBelow (P : R[X]) (n : ℕ) : List R := (List.range n).map P.coeff

/-- `coeffsBelow P n` has length `n`. -/
@[simp] theorem length_coeffsBelow (P : R[X]) (n : ℕ) : (P.coeffsBelow n).length = n := by
  simp only [coeffsBelow, List.length_map, List.length_range]

/-- The first `n` coefficients of a polynomial of degree less than `n` give the polynomial back. -/
theorem ofCoeffList_coeffsBelow {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    ofCoeffList (P.coeffsBelow n) = P := by
  ext i
  rw [coeff_ofCoeffList, coeffsBelow]
  by_cases hi : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Concatenating coefficient lists shifts the second polynomial past the first. -/
theorem ofCoeffList_append (l₁ l₂ : List R) :
    ofCoeffList (l₁ ++ l₂) = ofCoeffList l₁ + X ^ l₁.length * ofCoeffList l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, ofCoeffList_cons, ih, List.length_cons, pow_succ', mul_add,
      mul_assoc, add_assoc]

/-- Peeling the constant coefficient, with `0` for the empty list. -/
theorem ofCoeffList_eq_C_headD_add_X_mul_tail (l : List R) :
    ofCoeffList l = C (l.headD 0) + X * ofCoeffList l.tail := by
  cases l <;> simp [ofCoeffList_cons]

/-- A list of zeros is the zero polynomial. -/
@[simp] theorem ofCoeffList_replicate_zero (n : ℕ) :
    ofCoeffList (List.replicate n (0 : R)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, ofCoeffList_zero_cons, ih, mul_zero]

/-- Padding a coefficient list with zeros does not change the polynomial. -/
theorem ofCoeffList_takeD_of_length_le {l : List R} {n : ℕ} (h : l.length ≤ n) :
    ofCoeffList (l.takeD n 0) = ofCoeffList l := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only [List.length_cons] at h; omega⟩
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    simp only [List.takeD_succ, List.head?_cons, Option.getD_some, List.tail_cons,
      ofCoeffList_cons, ih h]

/-- The zero-padded first `m + k` coefficients split into the first `m` and the next `k`. -/
theorem ofCoeffList_takeD_add (l : List R) (m k : ℕ) :
    ofCoeffList (l.takeD (m + k) 0) =
      ofCoeffList (l.takeD m 0) + X ^ m * ofCoeffList ((l.drop m).takeD k 0) := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, List.takeD_succ, List.takeD_succ, ofCoeffList_cons, ofCoeffList_cons,
      ih, List.drop_tail, pow_succ']
    simp only [mul_add, mul_assoc, add_assoc]

end Polynomial
