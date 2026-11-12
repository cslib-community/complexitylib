/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Corollary
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the expected cost and Corollary 2.4

* The max-term bounds of `CslibFrontier.Foundations.Data.Nat.Choose.MaxTerm` at `a = 2`, `b = 3`:
  `5 ^ 5 = 3125 ≤ 6 · 10 · 4 · 27 = 6480` and `10 · 4 · 27 = 1080 ≤ 3125`; both sides are
  computed.
* The counts behind `E |C*|` at `p = 5`, `d = 2`: each target value is hit by `(p - 1) p = 20`
  seeds, and summed over all `100` seeds, a query list of length `3` has `3 · 1 · 20 = 60` ranked
  targets with `k = 2`, by `sum_length_rankedTargets` and by kernel reduction.
* `corollary_2_4` is instantiated: its constants exist for `κ = 1`.
-/

namespace CslibFrontierTests.Algorithms.Lean.SubsetConvThreeSumCorollary

open Finset Cslib.Algorithms.Lean.SubsetConvThreeSum

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

example : (2 + 3) ^ (2 + 3) ≤ (2 + 3 + 1) * ((2 + 3).choose 2 * 2 ^ 2 * 3 ^ 3) :=
  Nat.pow_le_succ_mul_choose_mul_pow_mul_pow 2 3

example : (2 + 3) ^ (2 + 3) = 3125 ∧ (2 + 3 + 1) * ((2 + 3).choose 2 * 2 ^ 2 * 3 ^ 3) = 6480 := by
  decide

example : (∑ j ∈ range (2 + 1), (10 : ℕ).choose j) * (2 ^ 2 * 8 ^ 8) ≤ 10 ^ 10 :=
  Nat.sum_choose_mul_pow_mul_pow_le_pow (by norm_num)

/-- Each target value below `5` is hit by `20` seeds. -/
example : #((seeds 5).filter fun s => s.target 7 = 3) = 20 := by
  rw [card_seeds_target 7 (by norm_num)]

/-- The same count by kernel reduction. -/
example : #((seeds 5).filter fun s => s.target 7 = 3) = 20 := by decide +kernel

/-- Summed over all seeds, three queries have `3 · (2 choose 2) · 20 = 60` ranked targets. -/
example : ∑ s ∈ seeds 5, ([1, 2, 3].filter fun c => decide (Ranked 2 2 (s.target c))).length =
    60 := by
  rw [sum_length_rankedTargets (by norm_num)]; rfl

/-- The constants of Corollary 2.4 exist for `κ = 1`. -/
example : ∃ K : ℝ, 0 < K := by
  obtain ⟨K, hK, -⟩ := corollary_2_4 1
  exact ⟨K, hK⟩

end CslibFrontierTests.Algorithms.Lean.SubsetConvThreeSumCorollary
