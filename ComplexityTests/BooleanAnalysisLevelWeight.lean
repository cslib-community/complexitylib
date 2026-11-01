/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.BooleanAnalysis.SpectralSample
import Complexity.Foundations.Data.Finset.Expect

/-! # Fourier weight by degree on a small cube

The conjunction of two bits, read as signs, has mean `1 / 2`, so its Fourier weight at degree
zero is `1 / 4`; the weights at degrees one and two make up the remaining `3 / 4`, and its
spectral sample is empty with probability `1 / 4`. A character's degree part is itself at its own
degree and zero at every other.
-/

namespace ComplexityTests.BooleanAnalysisLevelWeight

open Cslib Cslib.BitString Finset

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- The conjunction, read as signs, has Fourier weight `1 / 4` at degree zero. -/
theorem levelWeight_zero_and₂ : levelWeight 0 (fun x => signVal (and₂ x)) = 1 / 4 := by
  rw [levelWeight_zero]
  simp only [Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num [and₂]

-- The weights at degrees one and two make up the rest of the unit total weight.
example : levelWeight 1 (fun x => signVal (and₂ x)) + levelWeight 2 (fun x => signVal (and₂ x)) =
    3 / 4 := by
  have h := sum_levelWeight_signVal and₂
  simp only [Fintype.card_fin, sum_range_succ, sum_range_zero, zero_add,
    levelWeight_zero_and₂] at h
  linarith

-- The spectral sample of the conjunction is empty with probability `1 / 4`.
example : (spectralSample and₂).map card 0 = ENNReal.ofReal (1 / 4) := by
  rw [spectralSample_map_card_apply, levelWeight_zero_and₂]

-- A character is its own degree part at its degree, and has no part at any other degree.
example (S : Finset (Fin 3)) (T : Finset (Fin 3)) :
    fourierCoeff (levelPart #S (chi ℝ S)) T = fourierCoeff (chi ℝ S) T ∧
    ∀ k ≠ #S, fourierCoeff (levelPart k (chi ℝ S)) T = 0 := by
  refine ⟨?_, fun k hk => ?_⟩
  · rw [fourierCoeff_levelPart, fourierCoeff_chi]
    split_ifs with h₁ h₂ <;> simp_all
  · rw [fourierCoeff_levelPart, fourierCoeff_chi]
    split_ifs with h₁ h₂ <;> simp_all

end ComplexityTests.BooleanAnalysisLevelWeight
