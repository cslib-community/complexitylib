/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite differences of polynomials

Evaluating a univariate polynomial `P : R[X]` of degree at most `n` at `x` is determined by its
values at `x + 1, …, x + n + 1` via the `(n + 1)`-th forward difference vanishing identity:
$$\sum_{j=0}^{n+1} (-1)^j \binom{n+1}{j} P(x + j) = 0,$$
and in particular at `x = 0`:
$$P(0) = \sum_{r=0}^{n} (-1)^r \binom{n+1}{r+1} P(r + 1).$$
Unlike Lagrange interpolation over a field, these identities require no division and hold over any
commutative ring (including `ℤ`).

## Main results

* `Polynomial.natDegree_sub_comp_X_add_one_lt`: forward differencing `P - P.comp (X + 1)` strictly
  reduces positive `natDegree`.
* `Polynomial.sum_neg_one_pow_choose_eval_eq_zero`: vanishing of the `(n + 1)`-th binomial
  difference for `P.natDegree ≤ n`.
* `Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ`: recovering `P.eval 0` over any
  commutative ring from `P.eval 1, …, P.eval (n + 1)`.
-/

public section

namespace Polynomial

open Finset

variable {R : Type*} [CommRing R]

private theorem coeff_X_add_one_pow_self (d : ℕ) :
    ((X + (1 : R[X])) ^ d).coeff d = 1 := by
  rw [add_pow]
  simp only [mul_one, one_pow, ← lcoeff_apply, map_sum]
  rw [Finset.sum_eq_single d]
  · simp [coeff_X_pow]
  · intro i _ hne
    rw [lcoeff_apply, ← Nat.cast_comm, coeff_natCast_mul, coeff_X_pow]
    simp [hne.symm]
  · intro h
    simp at h

/-- Forward differencing `P - P.comp (X + 1)` vanishes on coefficients of degree at least
`P.natDegree`. -/
theorem coeff_sub_comp_X_add_one_eq_zero {P : R[X]} {k : ℕ} (hk : P.natDegree ≤ k) :
    (P - P.comp (X + 1)).coeff k = 0 := by
  have hX1 : (X + (1 : R[X])).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp [natDegree_X_le, natDegree_one])
  have hdeg : (P.comp (X + 1)).natDegree ≤ P.natDegree :=
    (natDegree_comp_le (p := P) (q := X + 1)).trans (by simpa using Nat.mul_le_mul_left _ hX1)
  by_cases hgt : P.natDegree < k
  · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt hgt,
      coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hgt), sub_zero]
  · obtain rfl : k = P.natDegree := le_antisymm (not_lt.mp hgt) hk
    have hcoeff : ∀ i ∈ range (P.natDegree + 1),
        (C (P.coeff i) * (X + 1) ^ i).coeff P.natDegree =
          if i = P.natDegree then P.coeff P.natDegree else 0 := by
      intro i hi
      rw [mem_range] at hi
      split_ifs with heq
      · subst heq
        rw [coeff_C_mul, coeff_X_add_one_pow_self, mul_one]
      · have hlt : i < P.natDegree := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) heq
        refine coeff_eq_zero_of_natDegree_lt ((natDegree_C_mul_le _ _).trans_lt ?_)
        have hpow : ((X + (1 : R[X])) ^ i).natDegree ≤ i :=
          (natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left i hX1)
        exact hpow.trans_lt hlt
    have hcomp : (P.comp (X + 1)).coeff P.natDegree = P.coeff P.natDegree := by
      nth_rw 1 [as_sum_range_C_mul_X_pow P]
      rw [sum_comp, ← lcoeff_apply, map_sum]
      simp_rw [lcoeff_apply, mul_comp, C_comp, pow_comp, X_comp]
      rw [sum_congr rfl hcoeff]
      simp
    rw [coeff_sub, hcomp, sub_self]

/-- Forward differencing strictly decreases positive polynomial `natDegree`. -/
theorem natDegree_sub_comp_X_add_one_lt {P : R[X]} (hP : 0 < P.natDegree) :
    (P - P.comp (X + 1)).natDegree < P.natDegree := by
  have hle : (P - P.comp (X + 1)).natDegree ≤ P.natDegree - 1 :=
    natDegree_le_iff_coeff_eq_zero.mpr fun k hk =>
      coeff_sub_comp_X_add_one_eq_zero (by omega)
  omega

/-- Forward differencing on a polynomial of degree at most `n + 1` leaves degree at most `n`. -/
theorem natDegree_sub_comp_X_add_one_le {n : ℕ} {P : R[X]} (hP : P.natDegree ≤ n + 1) :
    (P - P.comp (X + 1)).natDegree ≤ n := by
  by_cases h0 : P.natDegree = 0
  · rw [eq_C_of_natDegree_le_zero (by omega : P.natDegree ≤ 0)]
    simp
  · exact Nat.le_of_lt_succ ((natDegree_sub_comp_X_add_one_lt (Nat.pos_of_ne_zero h0)).trans_le hP)

/-- **Vanishing of the `(n + 1)`-th finite difference**: for any polynomial `P : R[X]` of degree
at most `n`, `∑ j = 0 .. n + 1, (-1) ^ j * choose (n + 1) j * P(x + j) = 0`. -/
theorem sum_neg_one_pow_choose_eval_eq_zero :
    ∀ {n : ℕ} (P : R[X]), P.natDegree ≤ n → ∀ x : R,
      ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j) = 0
  | 0, P, hP, x => by
    rw [eq_C_of_natDegree_le_zero hP]
    simp [sum_range_succ]
  | n + 1, P, hP, x => by
    have ihQ := sum_neg_one_pow_choose_eval_eq_zero (P - P.comp (X + 1))
      (natDegree_sub_comp_X_add_one_le hP) x
    have hsplit :
        ∑ j ∈ range (n + 3), (-1 : R) ^ j * ((n + 2).choose j : R) * P.eval (x + j) =
          ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j) -
            ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) *
              P.eval ((x + 1) + j) := by
      rw [sum_range_succ']
      have hpasc :
          ∑ k ∈ range (n + 2),
              (-1 : R) ^ (k + 1) * ((n + 2).choose (k + 1) : R) * P.eval (x + ↑(k + 1)) =
            (∑ k ∈ range (n + 2),
                (-1 : R) ^ (k + 1) * ((n + 1).choose (k + 1) : R) * P.eval (x + ↑(k + 1))) -
              ∑ k ∈ range (n + 2),
                (-1 : R) ^ k * ((n + 1).choose k : R) * P.eval ((x + 1) + k) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [Nat.choose_succ_succ (n + 1) k, show x + ↑(k + 1) = x + 1 + ↑k by push_cast; ring]
        push_cast
        rw [pow_succ']
        ring
      rw [hpasc]
      have hfirst :
          (∑ k ∈ range (n + 2),
              (-1 : R) ^ (k + 1) * ((n + 1).choose (k + 1) : R) * P.eval (x + ↑(k + 1))) +
            (-1 : R) ^ 0 * ((n + 2).choose 0 : R) * P.eval (x + ↑0) =
            ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j) := by
        rw [sum_range_succ (fun k =>
          (-1 : R) ^ (k + 1) * ((n + 1).choose (k + 1) : R) * P.eval (x + ↑(k + 1))) (n + 1)]
        have hzero : (n + 1).choose (n + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hzero, Nat.cast_zero, mul_zero, zero_mul, add_zero]
        rw [sum_range_succ' (fun j => (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j))
          (n + 1)]
        simp [add_comm]
      rw [← hfirst]
      ring_nf
    rw [hsplit, ← sum_sub_distrib]
    refine (sum_congr rfl fun j _ => ?_).trans ihQ
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one]
    ring_nf

/-- **Zero-evaluation finite-difference identity**: over any commutative ring `R`, a polynomial
`P : R[X]` of degree at most `n` satisfies
`P.eval 0 = ∑ r ∈ range (n + 1), (-1) ^ r * ((n + 1).choose (r + 1)) * P.eval (r + 1)`. -/
theorem eval_zero_eq_sum_neg_one_pow_choose_eval_succ {n : ℕ} {P : R[X]} (hP : P.natDegree ≤ n) :
    P.eval 0 = ∑ r ∈ range (n + 1),
      (-1 : R) ^ r * ((n + 1).choose (r + 1) : R) * P.eval ((r : R) + 1) := by
  have h := sum_neg_one_pow_choose_eval_eq_zero P hP 0
  rw [sum_range_succ'] at h
  simp only [Nat.cast_zero, add_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul] at h
  have heq :
      ∑ r ∈ range (n + 1),
          (-1 : R) ^ (r + 1) * ((n + 1).choose (r + 1) : R) * P.eval (↑(r + 1)) =
        - ∑ r ∈ range (n + 1),
            (-1 : R) ^ r * ((n + 1).choose (r + 1) : R) * P.eval ((r : R) + 1) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [show ((r + 1 : ℕ) : R) = (r : R) + 1 by push_cast; ring, pow_succ']
    ring
  simp only [zero_add] at h
  rw [heq, add_comm] at h
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h)

end Polynomial
