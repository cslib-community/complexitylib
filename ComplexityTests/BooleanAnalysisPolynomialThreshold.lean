/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.BooleanAnalysis.PolynomialThreshold
import Complexity.Foundations.Data.BitString.Threshold

/-! # Polynomial threshold functions on small cubes

The majority of three bits is the sign of `χ_{0} + χ_{1} + χ_{2}`, so it is a linear threshold
function, and by Chow's theorem it is the only Boolean function with its Fourier coefficients of
degree at most one. The parity of two bits has all its Fourier weight on the set of both bits, so
by Theorem 5.10 it is not a linear threshold function.

The conjunction of two bits is the book's `sgn(x₁ + x₂)` with `sgn(0) = 1`, a polynomial with
zeros over the family `{{0}, {1}}`. Theorem 5.10 in the form that allows zeros applies, and is
tight: its two coefficients have absolute value `1 / 2`. But no polynomial over that family without
zeros has the conjunction as its sign, so `IsPTFOn` is narrower than the book's notion for a family
not containing `∅`.
-/

namespace ComplexityTests.BooleanAnalysisPolynomialThreshold

open Cslib Cslib.BitString Finset

/-- The majority of three bits, written out. -/
def maj₃ (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

/-- The library's majority of three bits is the written-out one. -/
theorem majority_three_eq : majority 3 = maj₃ := by
  funext x
  revert x
  decide

/-- The majority of three bits is a linear threshold function: the sign of
`χ_{0} + χ_{1} + χ_{2}`. -/
theorem isPTF_one_majority_three : IsPTF 1 (majority 3) := by
  rw [majority_three_eq, isPTF_iff]
  refine ⟨fun x => chi ℝ {0} x + chi ℝ {1} x + chi ℝ {2} x, fun S hS => ?_, fun x => ?_⟩
  · have hne (i : Fin 3) : ({i} : Finset (Fin 3)) ≠ S := fun h => by subst h; simp at hS
    simp only [fourierCoeff_add, fourierCoeff_chi, hne, ↓reduceIte, add_zero]
  · cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> norm_num [maj₃, chi, h₀, h₁, h₂]

-- Chow's theorem: a Boolean function with the coefficients of degree at most one of the majority
-- is the majority.
example (g : (Fin 3 → Bool) → Bool)
    (hg : ∀ S : Finset (Fin 3), #S ≤ 1 →
      fourierCoeff (fun x => signVal (g x)) S = fourierCoeff (fun x => signVal (majority 3 x)) S) :
    g = majority 3 :=
  isPTF_one_majority_three.eq_of_fourierCoeff_eq hg

-- The parity of two bits is not a linear threshold function.
example : ¬ IsPTF 1 (parityOn ({0, 1} : Finset (Fin 2))) := by
  intro h
  have h₁ := IsPTFOn.one_le_sum_abs_fourierCoeff h
  have h₀ : ∑ S ∈ ({S | #S ≤ 1} : Finset (Finset (Fin 2))),
      |fourierCoeff (fun x => signVal (parityOn ({0, 1} : Finset (Fin 2)) x)) S| = 0 := by
    refine sum_eq_zero fun S hS => ?_
    have hS' : S ≠ {0, 1} := by
      rintro rfl
      simp at hS
    simp [fourierCoeff_signVal_parityOn, hS']
  linarith

-- Every Boolean function of two bits is a polynomial threshold function of degree at most two.
example : IsPTF 2 (parityOn ({0, 1} : Finset (Fin 2))) := by
  simpa using isPTF_card (parityOn ({0, 1} : Finset (Fin 2)))

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- The polynomial `χ_{0} + χ_{1}`, which vanishes where the two bits differ. -/
noncomputable def p₀₁ (x : Fin 2 → Bool) : ℝ :=
  chi ℝ {0} x + chi ℝ {1} x

-- Theorem 5.10 with zeros allowed: the conjunction is the sign of `χ_{0} + χ_{1}` where that is
-- nonzero, so its coefficients on `{0}` and `{1}` have absolute values summing to at least one.
example : 1 ≤ ∑ S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
    |fourierCoeff (fun x => signVal (and₂ x)) S| := by
  refine one_le_sum_abs_fourierCoeff_of_nonneg_mul (p := p₀₁) (fun S hS => ?_) ?_ fun x => ?_
  · have h₀ : ({0} : Finset (Fin 2)) ≠ S := fun h => hS (by simp [← h])
    have h₁ : ({1} : Finset (Fin 2)) ≠ S := fun h => hS (by simp [← h])
    change fourierCoeff (fun x => chi ℝ {0} x + chi ℝ {1} x) S = 0
    simp only [fourierCoeff_add, fourierCoeff_chi, h₀, h₁, ↓reduceIte, add_zero]
  · intro h
    have := congrFun h (fun _ => false)
    norm_num [p₀₁, chi] at this
  · cases h₀ : x 0 <;> cases h₁ : x 1 <;> norm_num [p₀₁, and₂, chi, h₀, h₁]

-- But no polynomial over `{{0}, {1}}` that vanishes nowhere has the conjunction as its sign: it
-- would be `a χ_{0} + b χ_{1}` with `a - b > 0` and `b - a > 0`.
example : ¬ IsPTFOn ({{0}, {1}} : Finset (Finset (Fin 2))) and₂ := by
  rintro ⟨p, hpT, hp⟩
  have hexp (x : Fin 2 → Bool) :
      p x = fourierCoeff p {0} * chi ℝ {0} x + fourierCoeff p {1} * chi ℝ {1} x := by
    rw [← sum_fourierCoeff_mul_chi p x,
      ← sum_subset (subset_univ {{0}, {1}}) fun S _ hS => by rw [hpT S hS, zero_mul],
      sum_pair (by decide)]
  have h₁ := hp ![false, true]
  have h₂ := hp ![true, false]
  rw [hexp] at h₁ h₂
  norm_num [and₂, chi] at h₁ h₂
  linarith

end ComplexityTests.BooleanAnalysisPolynomialThreshold
