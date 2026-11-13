/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorDimension
import CslibFrontier.Foundations.Data.Nat.Choose.MultinomialMax

/-!
# Tests for the dimension and trials of the base-`r` reduction

* The balanced multinomial bound at `r = 3`, `m = 2`: `3 ^ 6 (2!) ^ 3 ≤ 7 ^ 3 6!`.
* `r ^ d (r!)^{d/r} ≤ (d + 1) ^ r #P` at `r = d = 3`: `162 ≤ 64 · 36`.
* For `A = {1, 2}`, `B = {3, 5}`, `c = 4` (`|a + b - 4| ≤ 3`, so `n = 4`, `L = 1`) and `r = 2`, the
  dimension index is `4` (`d = 8`): it satisfies the condition and `3` does not, computed.
* `vaverage_miss_le_vDim` instantiated for this input with `k = 1` and threshold `s = 0`.
-/

namespace CslibFrontierTests.Algorithms.Lean.VectorDimension

open Finset Nat Cslib.Algorithms.Lean.SubsetConvThreeSum

example : 3 ^ (3 * 2) * (2 !) ^ 3 ≤ (3 * 2 + 1) ^ 3 * (3 * 2)! :=
  Nat.pow_mul_pow_factorial_le 3 2

example : 3 ^ 3 * (3 !) ^ (3 / 3) ≤ (3 + 1) ^ 3 * #(balancedPairs 3 3) :=
  pow_mul_le_card_balancedPairs (by norm_num) (dvd_refl 3)

/-- The condition holds at index `4` and fails at `3`. -/
example : vDimCond 2 4 1 4 ∧ ¬ vDimCond 2 4 1 3 := by decide

/-- So the dimension index is `4`. -/
example : vDimIndex 2 4 1 = 4 := by
  have hspec := vDimIndex_spec (by norm_num : 2 ≤ 2) 4 1
  have hle : vDimIndex 2 4 1 ≤ 4 := by
    by_contra h
    exact vDimIndex_min (r := 2) (by norm_num) 4 1 (j := 4) (by omega) (by decide)
  interval_cases h : vDimIndex 2 4 1
  · exact absurd hspec.1 (by norm_num)
  all_goals first | rfl | exact absurd hspec (by decide)

theorem bound_four : ∀ ab ∈ ([1, 2] : List ℕ).toFinset ×ˢ ([3, 5] : List ℕ).toFinset,
    (((ab.1 + ab.2 : ℕ) : ℤ) - 4).natAbs ≤ 3 := by decide

/-- The end-to-end bound for this input. -/
example :
    let d := vDim 2 #(([1, 2] : List ℕ).toFinset ×ˢ ([3, 5] : List ℕ).toFinset) (Nat.log 2 3)
    let e := Nat.clog 2 (2 ^ d)
    (∑ q ∈ primeWindow e, missProbOf (fun q σ => vtrialM 2 d 0 (p := q) σ) (vTrials 1 e 2 d)
        [1, 2] [3, 5] [4, 6, 9] 4 q) / #(primeWindow e) ≤ 1 / 20 + Real.exp (-(1 : ℕ)) :=
  vaverage_miss_le_vDim (le_refl 2) (a := 1) (b := 3) (by simp) (by simp) rfl (by simp) bound_four
    (Nat.zero_le _)

end CslibFrontierTests.Algorithms.Lean.VectorDimension
