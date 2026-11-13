/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorParameters

/-!
# Tests for the balanced-pair count and the number of trials

* `#balancedPairs 3 3 = 36`, computed by kernel reduction over the `27 ^ 2` pairs and by
  `card_balancedPairs` as `3! / (1!)^3 · (3!)^1`.
* `#balancedVecs 2 3 = 0`, by `balancedVecs_eq_empty` (`2 ∤ 3`) and by computation.
* `vTrials 1 5 3 3 = 152`, and `4 ^ 7 < 3 · 36 · 152` (`lt_three_mul_card_mul_vTrials`).
* `vaverage_miss_le_exp` for `A = {1, 2}`, `B = {3, 5}`, `c = 4 ∈ C`, `r = d = 3`, `e = 5`
  (`27 ≤ 32`): with `152` trials and a uniform prime of `[32, 64)`, the miss probability is at
  most `#bad / #window + exp (-1)`.
-/

namespace CslibFrontierTests.Algorithms.Lean.BalancedCount

open Finset Nat Cslib.Algorithms.Lean.SubsetConvThreeSum

/-- The exact count, computed. -/
example : #(balancedPairs 3 3) = 36 := by decide +kernel

/-- The exact count, from `card_balancedPairs`. -/
example : #(balancedPairs 3 3) = 36 := by
  rw [card_balancedPairs (by norm_num) (dvd_refl 3)]
  decide

/-- No balanced vectors when `r ∤ d`, by the theorem and by computation. -/
example : balancedVecs 2 3 = ∅ := balancedVecs_eq_empty (by decide)

example : #(balancedVecs 2 3) = 0 := by decide +kernel

/-- The number of trials for `k = 1`, `e = 5`, `r = d = 3`. -/
example : vTrials 1 5 3 3 = 152 := by decide

/-- `vTrials` is large enough: `4 ^ 7 < 3 · #P · 152`. -/
example : 1 * 4 ^ (5 + 2) < 3 * #(balancedPairs 3 3) * vTrials 1 5 3 3 :=
  lt_three_mul_card_mul_vTrials (by norm_num) (dvd_refl 3)

/-- The miss envelope with `vTrials 1 5 3 3` trials. -/
example :
    (∑ q ∈ primeWindow 5, missProbOf (fun q σ => vtrialM 3 3 1 (p := q) σ) (vTrials 1 5 3 3)
        [1, 2] [3, 5] [4, 6, 9] 4 q) / #(primeWindow 5) ≤
      (#(badPrimesOf 5 ((3 !) ^ (3 / 3)) 4 [1, 2] [3, 5]) : ℝ) / #(primeWindow 5) +
        Real.exp (-(1 : ℕ)) :=
  vaverage_miss_le_exp (by norm_num) (dvd_refl 3) (by decide) (by norm_num) (a := 1) (b := 3)
    (by simp) (by simp) rfl (by simp) ⟨37, by decide⟩

end CslibFrontierTests.Algorithms.Lean.BalancedCount
