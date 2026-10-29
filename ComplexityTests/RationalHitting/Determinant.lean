/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Determinant

/-!
# Regression tests for the list determinant program

Concrete values of `detRows`, checked by the kernel and compiled: nonsingular and singular inputs,
dimension zero and a ragged input. The correctness theorem is instantiated, and used to compute a
`Matrix.det`; the stage bounds are instantiated on a concrete input, so their hypotheses are
satisfiable; and the polynomial-time certificate `detRows_polytime` is checked directly and under
`fun_prop` composition.
-/

namespace ComplexityTests.RationalHitting.Determinant

open Turing MultiTapeTM
open Cslib.Circuits.Rational

/-! ### Concrete values -/

example : detRows [[2, 1], [1, 3]] = 5 := by decide +kernel
example : detRows [[1, 2], [3, 4]] = -2 := by decide +kernel
example : detRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]] = 24 := by decide +kernel
-- A singular matrix.
example : detRows [[1, 2, 3], [4, 5, 6], [7, 8, 9]] = 0 := by decide +kernel
-- Dimension zero.
example : detRows [] = 1 := by decide +kernel
-- A ragged input is padded with zeros and truncated to the number of rows: `!![1, 2; 3, 0]`.
example : detRows [[1, 2, 99], [3]] = -6 := by decide +kernel

/-- info: [5, -2, 24, 0, 1, -6, 1] -/
#guard_msgs in
#eval [detRows [[2, 1], [1, 3]], detRows [[1, 2], [3, 4]],
  detRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]], detRows [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
  detRows [], detRows [[1, 2, 99], [3]],
  detRows (rowsOf (1 : Matrix (Fin 4) (Fin 4) ℤ))]

/-! ### Correctness -/

example : (ofRows [[2, 1], [1, 3]]).det = 5 := by
  rw [← detRows_eq_det_ofRows]
  decide +kernel

-- The list program computes a `Matrix.det` in the kernel.
example : (!![2, -1, 0; 1, 3, 2; 0, 1, 4] : Matrix (Fin 3) (Fin 3) ℤ).det = 24 := by
  rw [← detRows_eq]
  decide +kernel

example : detRows [[1, 2, 99], [3]] = (!![1, 2; 3, 0] : Matrix (Fin 2) (Fin 2) ℤ).det :=
  detRows_eq_det_of_rowEntry _ rfl fun i j => by fin_cases i <;> fin_cases j <;> decide +kernel

/-! ### Size bounds -/

-- The hypotheses of the stage bounds hold on a concrete input.
example (k i j : ℕ) :
    (rowEntry (stagesRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]] k) i j).natAbs <
      2 ^ (3 + k * (1 + 3 + 3)) :=
  natAbs_rowEntry_stagesRows_lt (natAbs_rowEntry_lt (by decide +kernel)) k i j

example (k : ℕ) {row : List ℤ} (hrow : row ∈ stagesRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]] k)
    {z : ℤ} (hz : z ∈ row) : intBits z ≤ 3 + k * (1 + 3 + 3) + 1 :=
  intBits_le_of_mem_stagesRows (by decide +kernel) k hrow hz

-- The final stage of that input and its bit lengths.
/-- info: ([[24, 0, 0], [0, 0, 0], [0, 0, 0]], [[6, 1, 1], [1, 1, 1], [1, 1, 1]]) -/
#guard_msgs in
#eval (stagesRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]] 2,
  (stagesRows [[2, -1, 0], [1, 3, 2], [0, 1, 4]] 2).map (·.map intBits))

example : intBits 0 = 1 ∧ intBits 1 = 2 ∧ intBits (-5) = 4 := by decide +kernel

/-! ### Polynomial-time certificate -/

-- The registered certificate composes under `fun_prop`.
example : ComputableInPolyTime
    (fun p : List (List ℤ) × List (List ℤ) => detRows p.1 * detRows p.2)
    (encPair (encList (encList encIntBin)) (encList (encList encIntBin))) encIntBin := by
  fun_prop

example : ComputableInPolyTime (List.map detRows)
    (encList (encList (encList encIntBin))) (encList encIntBin) := by
  fun_prop

end ComplexityTests.RationalHitting.Determinant
