/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Permanent
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete checks for the permanent's VNP witness

The two-column witness has signed values `0`, `-10`, `-21` and `60` on the four selectors for
`!![2, 3; 5, 7]`, summing to `29`. Its circuit is checked on a nontrivial selector. The empty
matrix and characteristic two test the boundary cases of the ring-general Ryser identity.
-/

namespace ComplexityTests.PermanentVNP

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

example : booleanSum 0 (ryserPoly ℤ 0) = 1 := by
  simp [ryserPoly]

example : aeval (![2, 3, 5, 7, 0, 0] : Fin 6 → ℤ) (ryserPoly ℤ 2) = 0 := by
  norm_num [ryserPoly, Fin.prod_univ_two, Fin.sum_univ_two, finProdFinEquiv,
    Fin.natAdd, Fin.castAdd]

example : aeval (![2, 3, 5, 7, 1, 0] : Fin 6 → ℤ) (ryserPoly ℤ 2) = -10 := by
  norm_num [ryserPoly, Fin.prod_univ_two, Fin.sum_univ_two, finProdFinEquiv,
    Fin.natAdd, Fin.castAdd]

example : aeval (![2, 3, 5, 7, 0, 1] : Fin 6 → ℤ) (ryserPoly ℤ 2) = -21 := by
  norm_num [ryserPoly, Fin.prod_univ_two, Fin.sum_univ_two, finProdFinEquiv,
    Fin.natAdd, Fin.castAdd]

example : aeval (![2, 3, 5, 7, 1, 1] : Fin 6 → ℤ) (ryserPoly ℤ 2) = 60 := by
  norm_num [ryserPoly, Fin.prod_univ_two, Fin.sum_univ_two, finProdFinEquiv,
    Fin.natAdd, Fin.castAdd]

example : aeval (![2, 3, 5, 7] : Fin 4 → ℤ) (booleanSum 2 (ryserPoly ℤ 2)) = 29 := by
  rw [booleanSum_ryserPoly, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_two, Matrix.permanent_succ_row_zero, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_one, Fin.sum_univ_one]
  norm_num [Matrix.permanent, genericMatrix, finProdFinEquiv]

example : ∃ c : Circuit (arithSignature ℤ) 6 1, c.size ≤ 21 ∧
    c.eval (arithInterpretation ℤ) ![2, 3, 5, 7, 1, 0] 0 = -10 := by
  obtain ⟨c, hc, hs⟩ := exists_circuit_ryserPoly (R := ℤ) 2
  refine ⟨c, hs, ?_⟩
  rw [← c.eval_polynomial, hc]
  norm_num [ryserPoly, Fin.prod_univ_two, Fin.sum_univ_two, finProdFinEquiv,
    Fin.natAdd, Fin.castAdd]

-- In characteristic two the sign factor becomes `1`; membership still concerns formal
-- polynomials, and the Boolean sum has the expected two distinct permutation monomials.
example : booleanSum 2 (ryserPoly (ZMod 2) 2) =
    X (0 : Fin 4) * X 3 + X 1 * X 2 := by
  rw [booleanSum_ryserPoly, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_two, Matrix.permanent_succ_row_zero, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_one, Fin.sum_univ_one]
  simp [Matrix.permanent, genericMatrix, finProdFinEquiv]

example : aeval (![1, 1, 1, 1] : Fin 4 → ZMod 2)
    (booleanSum 2 (ryserPoly (ZMod 2) 2)) = 0 := by
  rw [booleanSum_ryserPoly, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_two, Matrix.permanent_succ_row_zero, Matrix.permanent_succ_row_zero,
    Fin.sum_univ_one, Fin.sum_univ_one]
  norm_num [Matrix.permanent, genericMatrix, finProdFinEquiv]
  decide

end ComplexityTests.PermanentVNP
