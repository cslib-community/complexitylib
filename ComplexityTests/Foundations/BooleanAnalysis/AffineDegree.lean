/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.AffineDegree

/-!
# Tests: multiplying by an affine function raises the degree

An instance of Lemma 5.2 of [ImpagliazzoPudlakSgall1999] on three coordinates, and a failure of
its conclusion on two coordinates, where `2 * deg r < n` does not hold: `(1 - x₀ - x₁)(x₀ - x₁)`
vanishes on the cube although `x₀ - x₁` has degree one.
-/

namespace ComplexityTests.AffineDegree

open Finset Cslib.BitString

/-- `x₀ - x₁` on the cube. -/
noncomputable def diff : (Fin 2 → Bool) → ℚ := fun x => bitVal ℚ (x 0) - bitVal ℚ (x 1)

/-- `x₀` on the three-dimensional cube. -/
noncomputable def firstBit : (Fin 3 → Bool) → ℚ := fun x => bitVal ℚ (x 0)

theorem firstBit_ne_zero : firstBit ≠ 0 := fun h => by
  have := congrFun h fun _ => true
  simp only [firstBit, bitVal_true, Pi.zero_apply, one_ne_zero] at this

theorem totalDegree_bit0 : totalDegree firstBit = 1 := by
  refine le_antisymm (totalDegree_le_of_mem_lowDegree (bitVal_mem_lowDegree 0)) ?_
  by_contra h
  have h0 : firstBit ∈ lowDegree ℚ (Fin 3) 0 := totalDegree_le_iff_mem_lowDegree.1 (by omega)
  have := subsetMobius_eq_zero_of_mem_lowDegree h0 (S := {0}) (by simp)
  rw [subsetMobius, show ({0} : Finset (Fin 3)).powerset = {∅, {0}} by decide] at this
  simp [firstBit] at this

/-- **An instance of the lemma**: on three coordinates, `(3/2 - x₀ - x₁ - x₂) · x₀` has degree
two. -/
example :
    totalDegree ((fun x : Fin 3 → Bool => 3 / 2 - ∑ i, 1 * bitVal ℚ (x i)) * firstBit) = 2 := by
  rw [totalDegree_affine_mul (fun _ => one_ne_zero) (3 / 2)
    (fun j hj _ => Nat.cast_ne_zero.2 (by omega)) firstBit_ne_zero (by rw [totalDegree_bit0]; simp),
    totalDegree_bit0]

theorem diff_ne_zero : diff ≠ 0 := fun h => by
  have := congrFun h ![true, false]
  simp only [diff, Matrix.cons_val_zero, Matrix.cons_val_one, bitVal_true, bitVal_false,
    sub_zero, Pi.zero_apply, one_ne_zero] at this

/-- **The bound `2 * deg r < n` is needed**: `(1 - x₀ - x₁)(x₀ - x₁)` vanishes on the cube, so
multiplying the degree-one function `x₀ - x₁` on two coordinates by an affine function with
nonzero coefficients does not raise its degree. -/
example : (fun x : Fin 2 → Bool => 1 - ∑ i, 1 * bitVal ℚ (x i)) * diff = 0 ∧ diff ≠ 0 := by
  refine ⟨funext fun x => ?_, diff_ne_zero⟩
  simp only [Pi.mul_apply, Pi.zero_apply, Fin.sum_univ_two, one_mul, diff]
  cases x 0 <;> cases x 1 <;> norm_num

end ComplexityTests.AffineDegree
