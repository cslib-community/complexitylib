/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.BooleanAnalysis.Variance

/-! # Variance on a small cube

The conjunction of two bits is `true` on one of the four inputs, so its relative distances to
the constants `false` and `true` are `1 / 4` and `3 / 4`; read as signs, its variance is
`4 · 1/4 · 3/4 = 3 / 4`, between twice and four times the distance `1 / 4` to the nearer
constant, so both bounds of O'Donnell's Proposition 1.15 apply with room to spare. A character
of a nonempty set has covariance one with itself.
-/

namespace ComplexityTests.BooleanAnalysisVariance

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- The conjunction is `true` on exactly one of the four inputs. -/
theorem hammingDist_and₂_false : hammingDist and₂ (fun _ => false) = 1 := by decide

/-- The conjunction is `false` on three of the four inputs. -/
theorem hammingDist_and₂_true : hammingDist and₂ (fun _ => true) = 3 := by decide

/-- The conjunction, read as signs, has variance `3 / 4`. -/
theorem variance_and₂ :
    𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 = 3 / 4 := by
  rw [expect_sub_expect_sq_signVal_eq_four_mul, hammingDist_and₂_false, hammingDist_and₂_true,
    Fintype.card_fin]
  norm_num

-- Proposition 1.15 holds strictly for the conjunction: `2 · 1/4 < 3/4 < 4 · 1/4`.
example :
    2 * min ((hammingDist and₂ (fun _ => false) : ℝ) / 2 ^ Fintype.card (Fin 2))
        (hammingDist and₂ (fun _ => true) / 2 ^ Fintype.card (Fin 2)) <
      𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 ∧
    𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 <
      4 * min ((hammingDist and₂ (fun _ => false) : ℝ) / 2 ^ Fintype.card (Fin 2))
        (hammingDist and₂ (fun _ => true) / 2 ^ Fintype.card (Fin 2)) := by
  rw [variance_and₂, hammingDist_and₂_false, hammingDist_and₂_true, Fintype.card_fin]
  norm_num

-- A character of a nonempty set has covariance one with itself.
example (S : Finset (Fin 3)) (hS : S ≠ ∅) :
    𝔼 x, (chi ℝ S x - 𝔼 y, chi ℝ S y) * (chi ℝ S x - 𝔼 y, chi ℝ S y) = 1 := by
  rw [expect_sub_expect_mul_sub_expect_eq_sum]
  simp only [fourierCoeff_chi, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp [hS]

end ComplexityTests.BooleanAnalysisVariance
