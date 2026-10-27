/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.MvPolynomial.CoefficientDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-! Concrete checks of the diagonal coefficient-degree bound, including sharpness,
cancellation, captured constants and failure without the zero-constant condition. -/

namespace JetCoefficientDegreeTests

private noncomputable def input {R : Type*} [CommRing R] (a : R) :
    Polynomial (MvPolynomial (Fin 1) R) :=
  Polynomial.C (MvPolynomial.C a) + Polynomial.C (MvPolynomial.X 0) * Polynomial.X

private theorem input_degree {R : Type*} [CommRing R] (a : R) (j : ℕ) :
    ((input a).coeff j).totalDegree ≤ j := by
  by_cases h0 : j = 0
  · subst j
    simp [input]
  · have hX : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R).totalDegree ≤ 1 := by
      change (MvPolynomial.monomial (Finsupp.single 0 1) (1 : R)).totalDegree ≤ 1
      exact (MvPolynomial.totalDegree_monomial_le _ _).trans (by simp)
    by_cases h1 : j = 1
    · simpa [input, h1] using hX
    · simp only [input, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_C_mul_X, h0, h1, ite_false, zero_add,
        MvPolynomial.totalDegree_zero, Nat.zero_le]

private theorem input_sq {R : Type*} [CommRing R] (a : R) :
    (input a) ^ 2 = Polynomial.C ((MvPolynomial.C a) ^ 2) +
      Polynomial.C (2 * MvPolynomial.C a * MvPolynomial.X (0 : Fin 1)) * Polynomial.X +
      Polynomial.C ((MvPolynomial.X (0 : Fin 1)) ^ 2) * Polynomial.X ^ 2 := by
  simp only [input, map_mul, map_pow, map_ofNat]
  ring

-- The baseline is fixed in the formal variables, but may depend on the original full assignment.
example (a : (Fin 2 → Bool) → ℤ) (x : Fin 2 → Bool) (j : ℕ) :
    ((MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (fun _ : Unit => input (a x))
      ((MvPolynomial.X () : MvPolynomial Unit ℤ) ^ 2)).coeff j).totalDegree ≤ j := by
  exact MvPolynomial.totalDegree_coeff_eval₂_le _ _ (fun _ k => input_degree (a x) k) j

-- The second coefficient attains degree two, so the bound cannot be made constant in j.
example : (((input (1 : ℤ)) ^ 2).coeff 2).totalDegree = 2 := by
  have hc : ((input (1 : ℤ)) ^ 2).coeff 2 = (MvPolynomial.X (0 : Fin 1)) ^ 2 := by
    rw [input_sq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow]
    simp
  rw [hc, MvPolynomial.totalDegree_X_pow]

-- Constants can be signed; the zeroth coefficient has no formal-variable dependence.
example (a : ℤ) : ((input a) ^ 2).coeff 0 = MvPolynomial.C (a * a) := by
  simp [input, pow_two, Polynomial.mul_coeff_zero]

-- Every positive outer order is allowed, not just corrections linear in the outer variable.
example : ((Polynomial.C (MvPolynomial.X (0 : Fin 1)) *
    (Polynomial.X ^ 3 : Polynomial ℤ).map MvPolynomial.C).coeff 3) = MvPolynomial.X 0 := by
  simp

example (j : ℕ) :
    ((Polynomial.C (MvPolynomial.X (0 : Fin 1)) *
      (Polynomial.X ^ 3 : Polynomial ℤ).map MvPolynomial.C).coeff j).totalDegree ≤ j := by
  exact MvPolynomial.totalDegree_coeff_X_mul_map_le _ _ (by simp) j

-- In characteristic two the degree-one cross coefficient cancels; no characteristic-zero
-- argument or division by factorials is part of the coefficient-degree theorem.
example : ((input (1 : ZMod 2)) ^ 2).coeff 1 = 0 := by
  have htwo : (2 : MvPolynomial (Fin 1) (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (MvPolynomial.C (σ := Fin 1)) (show (2 : ZMod 2) = 0 by decide)
  rw [input_sq]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  simp [htwo]

-- The trivial ring instantiation must not require Nontrivial merely to bound a formal X.
example (j : ℕ) :
    ((Polynomial.C (MvPolynomial.X (0 : Fin 1)) *
      (Polynomial.X : Polynomial (ZMod 1)).map MvPolynomial.C).coeff j).totalDegree ≤ j := by
  exact MvPolynomial.totalDegree_coeff_X_mul_map_le _ _ (by simp) j

-- If a formal variable carries a nonzero constant correction, coefficient zero has degree one.
example : ¬(((Polynomial.C (MvPolynomial.X (0 : Fin 1)) *
    (Polynomial.C (1 : ℤ)).map MvPolynomial.C).coeff 0).totalDegree ≤ 0) := by
  simp

-- Empty input variables and empty formal-variable types are both permitted.
example (p : MvPolynomial (Fin 0) ℤ) (j : ℕ) :
    ((MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (fun v : Fin 0 => Fin.elim0 v)
      p : Polynomial (MvPolynomial (Fin 0) ℤ)).coeff j).totalDegree ≤ j := by
  exact MvPolynomial.totalDegree_coeff_eval₂_le _ _ (fun v => Fin.elim0 v) j

end JetCoefficientDegreeTests
