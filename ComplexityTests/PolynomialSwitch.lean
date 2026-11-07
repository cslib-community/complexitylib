/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Analysis.SpecialFunctions.PolynomialSwitch
import Mathlib.Tactic.NormNum

/-!
# Tests for rational polynomial switches and fourth-root bounds

These examples evaluate the transition on rational inputs, transport an exact value to the real
switch, and use the global fourth-root bounds with concrete thresholds. They concern the `s = 4`
adaptation in issue #1721, not the pinned preprint's `s = 8` choice.
-/

namespace ComplexityTests.PolynomialSwitch

open Cslib
open scoped NNReal

-- The first-quarter value tests the interior polynomial, rather than only its plateau values.
example : polynomialTransition4 (1 / 4 : ℚ) = 289 / 4096 := by
  norm_num [polynomialTransition4, transitionPolynomial4]

example : polynomialTransition4 (3 / 4 : ℚ) = 3807 / 4096 := by
  norm_num [polynomialTransition4, transitionPolynomial4]

-- A translated and rescaled interval retains the exact rational transition.
example : polynomialSwitch4 (2 : ℚ) 6 3 = 289 / 4096 := by
  norm_num [polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

example : polynomialSwitch4 (2 : ℚ) 6 4 = 1 / 2 := by
  norm_num [polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

example : polynomialSwitch4 (2 : ℚ) 6 (-10) = 0 ∧ polynomialSwitch4 (2 : ℚ) 6 10 = 1 := by
  norm_num [polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

-- The real analysis uses exactly the same values as the rational arithmetic.
example : polynomialSwitch4 (2 : ℝ) 6 3 = 289 / 4096 := by
  have h : polynomialSwitch4 (2 : ℚ) 6 3 = 289 / 4096 := by
    norm_num [polynomialSwitch4, polynomialTransition4, transitionPolynomial4]
  have hc := polynomialSwitch4_ratCast (2 : ℚ) 6 3
  rw [h] at hc
  norm_num at hc ⊢
  exact hc

-- A zero-width interval is defined by field division by zero, without a false endpoint law.
example (t : ℚ) : polynomialSwitch4 2 2 t = 0 := by
  simp [polynomialSwitch4, polynomialTransition4]

-- Reflection is an identity for every real input, including both plateaus.
example (t : ℝ) :
    1 - polynomialTransition4 t = polynomialTransition4 (1 - t) :=
  one_sub_polynomialTransition4 t

-- The fourth-root perturbation estimate remains valid across the lower transition endpoint.
example : ∃ K : ℝ≥0, ∀ t : ℝ,
    |polynomialSwitch4 2 6 t ^ (4⁻¹ : ℝ)| ≤ K * |t - 2| := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_polynomialSwitch4_root 2 6
  refine ⟨K, fun t => ?_⟩
  have h := hK.dist_le_mul t 2
  rw [polynomialSwitch4_of_le (by norm_num : (2 : ℝ) < 6) le_rfl,
    Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0)] at h
  simpa only [Real.dist_eq, sub_zero] using h

-- The complementary root has the corresponding bound at the upper transition endpoint.
example : ∃ K : ℝ≥0, ∀ t : ℝ,
    |(1 - polynomialSwitch4 2 6 t) ^ (4⁻¹ : ℝ)| ≤ K * |t - 6| := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_one_sub_polynomialSwitch4_root 2 6
  refine ⟨K, fun t => ?_⟩
  have h := hK.dist_le_mul t 6
  rw [polynomialSwitch4_of_ge (by norm_num : (2 : ℝ) < 6) le_rfl, sub_self,
    Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0)] at h
  simpa only [Real.dist_eq, sub_zero] using h

end ComplexityTests.PolynomialSwitch
