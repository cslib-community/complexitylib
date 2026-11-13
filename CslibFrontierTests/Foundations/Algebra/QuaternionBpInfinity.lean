/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Algebra.Quaternion.BpInfinity

/-! Checked clients for the `B_{p,∞}` quaternion algebra presentation and reduced norm. -/

namespace Cslib.BpInfinity

open scoped Quaternion

example : i 3 * i 3 = (-1 : BpInfinity 3) := by simp

example : j 3 * j 3 = (-3 : BpInfinity 3) := by simp

example : i 3 * j 3 = k 3 ∧ j 3 * i 3 = -k 3 := by simp

example :
    reducedNorm ((1 : BpInfinity 3) + (2 : ℚ) • i 3 + (3 : ℚ) • j 3 + (4 : ℚ) • k 3) =
      80 := by
  rw [i_eq_mk, j_eq_mk, k_eq_mk]
  rw [show
    (1 : BpInfinity 3) + (2 : ℚ) • QuaternionAlgebra.mk 0 1 0 0 +
        (3 : ℚ) • QuaternionAlgebra.mk 0 0 1 0 +
        (4 : ℚ) • QuaternionAlgebra.mk 0 0 0 1 =
      QuaternionAlgebra.mk 1 2 3 4 by ext <;> norm_num]
  norm_num

example :
    reducedNorm (QuaternionAlgebra.mk 1 2 3 4 : BpInfinity 3) = 80 := by
  norm_num

example :
    0 < reducedNorm (QuaternionAlgebra.mk 1 2 3 4 : BpInfinity 3) := by
  apply reducedNorm_pos (by norm_num)
  intro h
  have := congrArg QuaternionAlgebra.re h
  norm_num at this

end Cslib.BpInfinity
