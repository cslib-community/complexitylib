/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.BooleanAnalysis.Majority
public import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin

/-! # Majority and the degree-one coefficients on three bits

On three bits `𝔼 |x₁ + x₂ + x₃| = 3 / 2`, so the degree-one Fourier coefficients of the majority
sum to `3 / 2` and the expected number of voters agreeing with the majority outcome is `9 / 4`.
The first dictator is not a majority function: at `(1, -1, -1)` it disagrees with the sign of the
sum, so its degree-one coefficients sum to strictly less. Being monotone, it has total influence
at most that of the majority. On two bits, where ties occur, both the majority, which breaks ties
towards `true`, and the strict majority, which breaks them towards `false`, are majority functions,
so the maximizer is not unique for even `n`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisMajority

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- On three bits the expected absolute value of the sum of the signs is `3 / 2`. -/
theorem expect_abs_sum_signVal_three :
    𝔼 x : BitString 3, |∑ i, signVal (x i)| = 3 / 2 := by
  simp only [Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique,
    Fin.sum_univ_three, show (2 : Fin 3) = (1 : Fin 2).succ from rfl, Fin.cons_succ, Fin.cons_one,
    Fin.cons_zero]
  norm_num [abs_of_nonneg, abs_of_nonpos]

-- The degree-one coefficients of the majority of three bits sum to `3 / 2`.
example : ∑ i, fourierCoeff (fun x => signVal (majority 3 x)) {i} = 3 / 2 := by
  rw [sum_fourierCoeff_singleton_majority, expect_abs_sum_signVal_three]

-- The expected number of voters agreeing with the majority of three is `3 / 2 + 3 / 4 = 9 / 4`.
example : 𝔼 x : BitString 3, (#{i | x i = majority 3 x} : ℝ) = 9 / 4 := by
  rw [expect_card_agree, sum_fourierCoeff_singleton_majority, expect_abs_sum_signVal_three,
    Fintype.card_fin]
  norm_num

-- The first dictator is not a majority function, so its degree-one coefficients do not reach
-- `𝔼 |x₁ + x₂ + x₃|`.
example : ∑ i, fourierCoeff (fun x : BitString 3 => signVal (x 0)) {i} ≠
    𝔼 x : BitString 3, |∑ i, signVal (x i)| := by
  rw [Ne, sum_fourierCoeff_singleton_signVal_eq_iff]
  intro h
  have := h ![false, true, true]
  norm_num [Fin.sum_univ_three] at this

-- Being monotone, the first dictator has total influence at most that of the majority.
example : totalInfluence (fun x : BitString 3 => signVal (x 0)) ≤
    totalInfluence (fun x => signVal (majority 3 x)) :=
  totalInfluence_le_majority_of_monotone (f := fun x => x 0) fun _ _ h => h 0

/-- The majority of two bits is their disjunction. -/
theorem majority_two_eq : majority 2 = fun x => x 0 || x 1 := by
  funext x
  revert x
  decide

/-- The strict majority of two bits is their conjunction. -/
theorem strictMajority_two_eq : strictMajority 2 = fun x => x 0 && x 1 := by
  funext x
  revert x
  decide

-- On two bits, both the majority and the strict majority are majority functions: they agree with
-- the sign of `x₁ + x₂` off the ties, and disagree with each other on the ties.
example : (∀ x : BitString 2, 0 ≤ signVal (majority 2 x) * ∑ i, signVal (x i)) ∧
    (∀ x : BitString 2, 0 ≤ signVal (strictMajority 2 x) * ∑ i, signVal (x i)) ∧
    majority 2 ≠ strictMajority 2 := by
  refine ⟨signVal_majority_mul_sum_signVal_nonneg, fun x => ?_, ?_⟩
  · rw [strictMajority_two_eq, Fin.sum_univ_two]
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> norm_num [h₀, h₁]
  · rw [majority_two_eq, strictMajority_two_eq]
    intro h
    have := congrFun h ![true, false]
    simp at this

end CslibFrontierTests.BooleanAnalysisMajority
