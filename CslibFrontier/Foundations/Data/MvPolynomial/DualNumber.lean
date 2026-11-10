/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, the multivariate analogue of `Polynomial.aeval_add_of_sq_eq_zero`)

public import CslibFrontier.Init
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Multivariate polynomials at dual numbers

Evaluating a multivariate polynomial at dual numbers computes its first-order Taylor expansion:
the real part of `P(z + ε v)` is `P(z)` (`MvPolynomial.fst_aeval_dualNumber`) and its dual part is
`∑_a ∂_a P(z) v_a` (`MvPolynomial.snd_aeval_dualNumber`). This is the multivariate analogue of
`Polynomial.aeval_add_of_sq_eq_zero`.

## Main results

* `MvPolynomial.fst_aeval_dualNumber`: the real part of a polynomial at dual numbers.
* `MvPolynomial.snd_aeval_dualNumber`: Taylor expansion over the dual numbers.
-/

public section

open TrivSqZeroExt
open scoped DualNumber

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The real part of a polynomial at dual numbers is its value at the real parts. -/
theorem fst_aeval_dualNumber (P : MvPolynomial σ R) (u : σ → R[ε]) :
    (aeval u P).fst = eval (fun a => (u a).fst) P :=
  comp_aeval_apply u (fstHom R R R) P

/-- **Taylor expansion over the dual numbers.** The dual part of `P(z + ε v)` is
`∑_a ∂_a P(z) v_a`. -/
theorem snd_aeval_dualNumber [Fintype σ] (P : MvPolynomial σ R) (u : σ → R[ε]) :
    (aeval u P).snd = ∑ a, eval (fun b => (u b).fst) (pderiv a P) * (u a).snd := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [algebraMap_eq_inl]
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    have hX (a : σ) :
        eval (fun b => (u b).fst) (pderiv a (X i : MvPolynomial σ R)) =
          (Pi.single i 1 : σ → R) a := by
      by_cases h : a = i <;> simp [h, Ne.symm]
    rw [map_mul, aeval_X, DualNumber.snd_mul, fst_aeval_dualNumber, hP, Finset.sum_mul]
    simp only [pderiv_mul, map_add, map_mul, eval_X, hX, add_mul, Finset.sum_add_distrib,
      Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [add_comm]
    exact congrArg (· + _) (Finset.sum_congr rfl fun a _ => mul_right_comm _ _ _)

end MvPolynomial
