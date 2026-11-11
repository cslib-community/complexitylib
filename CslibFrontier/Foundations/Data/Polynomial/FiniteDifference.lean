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
import Mathlib.Algebra.Group.ForwardDiff
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

* `Polynomial.sum_neg_one_pow_choose_eval_eq_zero`: vanishing of the `(n + 1)`-th binomial
  difference for `P.natDegree ≤ n`, derived from Mathlib's
  `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` and `fwdDiff_iter_eq_sum_shift`.
* `Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ`: recovering `P.eval 0` over any
  commutative ring from `P.eval 1, …, P.eval (n + 1)`.
-/

public section

namespace Polynomial

open Finset

variable {R : Type*} [CommRing R]

/-- **Vanishing of the `(n + 1)`-th finite difference**: for any polynomial `P : R[X]` of degree
at most `n`, `∑ j = 0 .. n + 1, (-1) ^ j * choose (n + 1) j * P(x + j) = 0`. -/
theorem sum_neg_one_pow_choose_eval_eq_zero {n : ℕ} (P : R[X]) (hP : P.natDegree ≤ n) (x : R) :
    ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j) = 0 := by
  have hzero : (_root_.fwdDiff (1 : R))^[n + 1] P.eval x = 0 :=
    congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_of_le hP)) x
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  have hsum :
      ∑ j ∈ range (n + 2), (-1 : R) ^ j * ((n + 1).choose j : R) * P.eval (x + j) =
        (-1 : R) ^ (n + 1) *
          ∑ j ∈ range (n + 2),
            ((-1 : ℤ) ^ (n + 1 - j) * ↑((n + 1).choose j)) • P.eval (x + j • (1 : R)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjle : j ≤ n + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hsign : (-1 : R) ^ j = (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1 - j) :=
      calc (-1 : R) ^ j
          = (-1 : R) ^ j * ((-1 : R) * (-1 : R)) ^ (n + 1 - j) := by simp
        _ = (-1 : R) ^ (j + (n + 1 - j)) * (-1 : R) ^ (n + 1 - j) := by
          rw [mul_pow, ← mul_assoc, ← pow_add]
        _ = (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1 - j) := by
          rw [Nat.add_sub_of_le hjle]
    rw [zsmul_eq_mul, nsmul_one, hsign]
    push_cast
    ring
  rw [hsum, hzero, mul_zero]

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
