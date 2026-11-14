/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABP

/-!
# Quasipolynomial hitting sets for ROABPs

The polynomial `X 1 ^ 2 * X 0` over the rationals is computed by the width-one program with
layers `(X ^ 2)` for the variable `1` and `(X)` for the variable `0`, read in the order `1, 0`.
So it is nonzero at a point of the hitting set for width one and degree two, which is built
without knowing this order.
-/

public section

namespace CslibFrontierTests.ROABPHittingSet

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The layers `(X)` for the variable `0` and `(X ^ 2)` for the variable `1`. -/
noncomputable def layers : Fin 2 → Matrix (Fin 1) (Fin 1) (Polynomial ℚ) :=
  fun i => Matrix.of fun _ _ => Polynomial.X ^ (i.val + 1)

/-- `X 1 ^ 2 * X 0` is computed by a width-one program with layers of degree at most two in the
order `1, 0`. -/
theorem isROABP_X_sq_mul_X : IsROABP 1 2 (X 1 ^ 2 * X 0 : MvPolynomial (Fin 2) ℚ) := by
  refine ⟨[1, 0], layers, 0, 0, by decide, fun i _ _ => ?_, ?_⟩
  · rw [layers, Matrix.of_apply, Polynomial.natDegree_X_pow]
    omega
  · simp [roabpProd, layers, Matrix.mul_apply]

/-- The hitting set contains a point where `X 1 ^ 2 * X 0` is nonzero. -/
theorem exists_eval_ne_zero :
    ∃ a ∈ roabpHittingSet ℚ 2 1 2, eval a (X 1 ^ 2 * X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 :=
  isHittingSet_roabpHittingSet _ isROABP_X_sq_mul_X
    (mul_ne_zero (pow_ne_zero 2 (X_ne_zero 1)) (X_ne_zero 0))

/-- The prime of the construction for two variables, width one and degree two is at most `22`. -/
example : roabpPrime 2 1 2 ≤ 22 := roabpPrime_le 2 1 2

end CslibFrontierTests.ROABPHittingSet
