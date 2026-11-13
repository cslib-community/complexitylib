/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.Discrepancy.Spectral
import CslibFrontier.Probability.PMF
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Rectangular and empty cases, a zero-bit cube, and the nilpotent spectral-radius obstruction. -/

namespace CslibFrontierTests.SpectralDiscrepancy

open Cslib Cslib.Communication Cslib.Probability Cslib.BitString Finset
open scoped Matrix.Norms.L2Operator

private def obstruction : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i _ => if i = 0 then 1 else -1

-- Its characteristic polynomial has only the zero root, but a rectangle sum is positive.
example : obstruction * obstruction = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, obstruction]

example : obstruction.charpoly = Polynomial.X ^ 2 := by
  norm_num [Matrix.charpoly_fin_two, Matrix.trace, Matrix.det_fin_two,
    Fin.sum_univ_two, obstruction]

example : |∑ i ∈ ({0} : Finset (Fin 2)), ∑ j ∈ ({0} : Finset (Fin 2)), obstruction i j| /
    (Fintype.card (Fin 2) * Fintype.card (Fin 2)) = (1 : ℝ) / 4 := by
  norm_num [obstruction]

private def rowFunction (i _j : Fin 2) : Bool := decide (i = 1)

example : signMatrix ℝ rowFunction = obstruction := by
  ext i j
  fin_cases i <;> norm_num [signMatrix_apply, rowFunction, obstruction]

-- A non-square 1-by-2 matrix yields a quantitative lower bound on its norm.
private def rectangular : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ => 1

example : (2 : ℝ) ≤ ‖rectangular‖ * √2 := by
  have h := Matrix.abs_sum_sum_le_l2_opNorm rectangular univ univ
  simpa [rectangular] using h

-- The raw matrix estimate permits an empty index type; no uniform PMF is requested here.
example (M : Matrix Empty (Fin 2) ℝ) :
    |∑ i, ∑ j, M i j| ≤ ‖M‖ * √(Fintype.card Empty) * √2 :=
  Matrix.abs_sum_sum_le_l2_opNorm M univ univ

-- An empty rectangle in a nonempty matrix has zero signed sum.
example (M : Matrix (Fin 2) (Fin 2) ℝ) :
    |∑ i ∈ (∅ : Finset (Fin 2)), ∑ j, M i j| ≤
      ‖M‖ * √((∅ : Finset (Fin 2)).card : ℝ) * √(Fintype.card (Fin 2)) :=
  Matrix.abs_sum_sum_le_l2_opNorm M ∅ univ

private abbrev Word0 := Fin 0 → Bool

-- The constant function on the zero-bit cube attains discrepancy one.
example : discrepancy (PMF.uniformOfFintype (Word0 × Word0)) (fun _ _ => false) = 1 := by
  have hM : signMatrix ℝ (fun (_ _ : Word0) => false) = 1 := by
    ext x y
    simp [signMatrix_apply, Matrix.one_apply, Subsingleton.elim x y]
  have hu := discrepancy_bitString_le_l2_opNorm (fun (_ _ : Word0) => false)
  have hl := abs_sum_le_discrepancy (PMF.uniformOfFintype (Word0 × Word0))
    (fun _ _ => false) univ univ
  have hlow : 1 ≤ discrepancy (PMF.uniformOfFintype (Word0 × Word0)) (fun _ _ => false) := by
    simpa only [signVal_false, mul_one, ← Fintype.sum_prod_type', PMF.sum_toReal, abs_one]
      using hl
  norm_num [hM, Word0] at hu
  exact le_antisymm hu hlow

end CslibFrontierTests.SpectralDiscrepancy
