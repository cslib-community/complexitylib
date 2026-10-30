/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Data.Finset.KthLargest
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the `k`-th largest value
-/

namespace ComplexityTests.KthLargest

open Finset

/-- The values `3, 1, 2, 0`. -/
private def h : Fin 4 → ℚ := ![3, 1, 2, 0]

private theorem filter_two_lt : (univ.filter fun x => (2 : ℚ) < h x) = {0} := by
  decide

private theorem filter_two_le : (univ.filter fun x => (2 : ℚ) ≤ h x) = {0, 2} := by
  decide

private theorem filter_zero_lt : (univ.filter fun x => (0 : ℚ) < h x) = {0, 1, 2} := by
  decide

-- The second largest of `3, 1, 2, 0` is `2`: two values are at least `2`, one exceeds it.
example : kthLargest 2 univ h = 2 := by
  refine le_antisymm (not_lt.mp fun hlt => ?_) ?_
  · have := (lt_kthLargest_iff (by norm_num) (by norm_num)).mp hlt
    rw [filter_two_lt, card_singleton] at this
    omega
  · rw [le_kthLargest_iff (by norm_num) (by norm_num), filter_two_le]
    rfl

-- Only three values are positive, so the padded fourth largest is `0`.
example : kthLargest 4 univ h = 0 := by
  refine le_antisymm (not_lt.mp fun hlt => ?_) kthLargest_nonneg
  have := (lt_kthLargest_iff (by norm_num) le_rfl).mp hlt
  rw [filter_zero_lt] at this
  exact absurd this (by decide)

-- Values above a nonnegative bound bound the order statistic.
example (k : ℕ) : kthLargest k univ h ≤ 3 :=
  kthLargest_le (by norm_num) fun x _ => by fin_cases x <;> norm_num [h]

end ComplexityTests.KthLargest
