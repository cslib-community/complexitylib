/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShiftSet

/-!
# Concentrating shifts

The monomial `X 0 * X 1` has no constant term, and split rank one across each of its variables.
Some shift from the explicit set built from the constant colouring gives it one.
-/

public section

namespace CslibFrontierTests.ConcentratingShift

open Cslib Cslib.Circuits.Arithmetic MvPolynomial

/-- Split rank one of `X 0 * X 1` across any single variable. -/
theorem splitRankLE_X_mul_X (Y : Finset (Fin 2)) (hY : Y.card = 1) :
    SplitRankLE (Y : Set (Fin 2)) 1 (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) := by
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hY
  fin_cases j
  · exact ⟨fun _ => X 0, fun _ => X 1, fun _ => X_mem_supported.2 (by simp),
      fun _ => X_mem_supported.2 (by simp), by simp⟩
  · exact ⟨fun _ => X 1, fun _ => X 0, fun _ => X_mem_supported.2 (by simp),
      fun _ => X_mem_supported.2 (by simp), by simp [mul_comm]⟩

/-- Some shift from the explicit set gives `X 0 * X 1` a constant term. -/
theorem exists_shift_X_mul_X_constant :
    ∃ a ∈ concentratingShifts ℚ ({fun _ => 0} : Finset (Fin 2 → Fin 1)),
      ∃ m ∈ (shift a (X 0 * X 1 : MvPolynomial (Fin 2) ℚ)).support, m.support.card < 1 := by
  refine exists_mem_concentratingShifts
    (fun S hS => ⟨_, Finset.mem_singleton_self _, ?_⟩) (w := 1) (by norm_num)
    (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)) (fun i => ?_) splitRankLE_X_mul_X
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hS
    simp
  · refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_X, degreeOf_X]
    fin_cases i <;> simp

end CslibFrontierTests.ConcentratingShift
