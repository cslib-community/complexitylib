/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Nat.MasterTheoremAsymptotics
import Complexity.Algorithms.Lean.Query.Arith.Karatsuba.Cost
import Cslib.Algorithms.Lean.MergeSort.MergeSort

/-!
# Tests for the master theorem

Each case of the master theorem applied to a concrete recurrence: cslib's merge-sort comparison
count (case 2), Karatsuba's multiplication count (case 1 with `d = 0`), a Strassen-shaped
recurrence (case 1, `O(n ^ log₂ 7)`), a binary-search recurrence (case 2 with `d = 0`) and a
base-`3` recurrence (case 3). A function that violates the hypothesis shows it is not vacuous.
-/

namespace ComplexityTests.MasterTheorem

open Nat

/-! ### Merge sort: case 2 -/

theorem mergeSort_bound : DivideConquerBound Cslib.Algorithms.Lean.TimeM.timeMergeSortRec
    2 2 1 0 fun n => 1 * n ^ 1 := by
  refine ⟨fun n hn => ?_, fun n hn S hS => ?_⟩
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
      simp [Cslib.Algorithms.Lean.TimeM.timeMergeSortRec]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have e : Cslib.Algorithms.Lean.TimeM.timeMergeSortRec (k + 2) =
        Cslib.Algorithms.Lean.TimeM.timeMergeSortRec ((k + 2) / 2) +
          Cslib.Algorithms.Lean.TimeM.timeMergeSortRec ((k + 2 - 1) / 2 + 1) + (k + 2) := by
      rw [Cslib.Algorithms.Lean.TimeM.timeMergeSortRec]
    have h1 := hS ((k + 2) / 2) (by omega)
    have h2 := hS ((k + 2 - 1) / 2 + 1) (by omega)
    rw [e, pow_one, one_mul]
    omega

/-- Merge sort makes at most `2 n ⌈log₂ n⌉` comparisons. cslib's `timeMergeSortRec_le` has the
sharper `n ⌈log₂ n⌉`; the generic theorem loses the factor `b` from `b ^ ⌈log_b n⌉ ≤ b n`. -/
example (n : ℕ) (hn : n ≠ 0) :
    Cslib.Algorithms.Lean.TimeM.timeMergeSortRec n ≤ 2 * n * clog 2 n := by
  have := mergeSort_bound.le_mul_pow_mul_clog (by norm_num) (by norm_num) le_rfl (by norm_num) hn
  simp only [pow_one, one_mul, zero_add] at this
  linarith

example : (fun n => (Cslib.Algorithms.Lean.TimeM.timeMergeSortRec n : ℝ)) =O[Filter.atTop]
    fun n => (n : ℝ) ^ 1 * Real.log n :=
  mergeSort_bound.isBigO_pow_mul_log (by norm_num) le_rfl (by norm_num)

/-! ### Karatsuba: case 1 with `d = 0` -/

/-- The multiplication count `M(n) = M(⌊n/2⌋) + 2 M(⌈n/2⌉)` of Karatsuba's algorithm. Both
subproblems have size at most `⌈n/2⌉`, so it is a case-1 instance with `a = 3` and `f = 0`. -/
theorem mulCount_bound : DivideConquerBound Cslib.Query.Karatsuba.mulCount 3 2 1 1
    fun n => 0 * n ^ 0 := by
  refine ⟨fun n hn => ?_, fun n hn S hS => ?_⟩
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · simp only [Cslib.Query.Karatsuba.mulCount_zero, Nat.zero_le]
    · simp only [Cslib.Query.Karatsuba.mulCount_one, le_refl]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [Cslib.Query.Karatsuba.mulCount]
    simp only [zero_mul, add_zero]
    have h1 := hS ((k + 2) / 2) (by omega)
    have h2 := hS (k + 2 - (k + 2) / 2) (by omega)
    omega

/-- The generic theorem recovers `Karatsuba.mulCount_le_pow_clog`. -/
example (n : ℕ) : Cslib.Query.Karatsuba.mulCount n ≤ 3 ^ clog 2 n := by
  have := mulCount_bound.sub_mul_le_pow_clog (by norm_num) (by norm_num) le_rfl n
  norm_num at this
  omega

example : (fun n => (Cslib.Query.Karatsuba.mulCount n : ℝ)) =O[Filter.atTop]
    fun n => (n : ℝ) ^ Real.logb 2 3 := by
  simpa using mulCount_bound.isBigO_rpow (by norm_num) le_rfl (by norm_num)

/-! ### A Strassen-shaped recurrence: case 1 -/

/-- `T(n) = 7 T(⌈n/2⌉) + n²`, `T(0) = 0`, `T(1) = 1`. -/
def strassenT : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 7 * strassenT ((n + 3) / 2) + (n + 2) ^ 2
termination_by n => n
decreasing_by omega

example : strassenT 4 = 93 := by simp [strassenT]

theorem strassenT_bound : DivideConquerBound strassenT 7 2 1 1 fun n => 1 * n ^ 2 := by
  refine ⟨fun n hn => ?_, fun n hn S hS => ?_⟩
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [strassenT]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [strassenT]
    have h1 := hS ((k + 3) / 2) (by omega)
    simp only [one_mul]
    omega

/-- `3 T(n) ≤ 7 · 7 ^ ⌈log₂ n⌉`. -/
example (n : ℕ) : 3 * strassenT n ≤ 7 * 7 ^ clog 2 n := by
  have := strassenT_bound.sub_mul_le_pow_clog (by norm_num) (by norm_num) le_rfl n
  norm_num at this
  omega

/-- `T(n) ≤ (7/3) · 7 · n ^ log₂ 7` for `n ≠ 0`. -/
example (n : ℕ) (hn : n ≠ 0) :
    (strassenT n : ℝ) ≤ (1 + 4 / 3) * 7 * (n : ℝ) ^ Real.logb 2 7 := by
  have := strassenT_bound.le_mul_rpow (by norm_num) le_rfl (by norm_num) hn
  norm_num at this ⊢
  linarith

example : (fun n => (strassenT n : ℝ)) =O[Filter.atTop] fun n => (n : ℝ) ^ Real.logb 2 7 := by
  simpa using strassenT_bound.isBigO_rpow (by norm_num) le_rfl (by norm_num)

/-! ### Binary search: case 2 with `d = 0` -/

/-- `T(n) = T(⌈n/2⌉) + 1`, `T(0) = T(1) = 0`. -/
def bsT : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => bsT ((n + 3) / 2) + 1
termination_by n => n
decreasing_by omega

theorem bsT_bound : DivideConquerBound bsT 1 2 1 0 fun n => 1 * n ^ 0 := by
  refine ⟨fun n hn => ?_, fun n hn S hS => ?_⟩
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [bsT]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [bsT]
    have h1 := hS ((k + 3) / 2) (by omega)
    simp only [pow_zero, one_mul]
    omega

example (n : ℕ) (hn : n ≠ 0) : bsT n ≤ clog 2 n := by
  simpa using bsT_bound.le_mul_pow_mul_clog le_rfl (by norm_num) le_rfl (by norm_num) hn

/-! ### Base `3`: case 3 -/

/-- `T(n) = 2 T(⌈n/3⌉) + n`, `T(0) = 0`, `T(1) = 1`. -/
def t3 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * t3 ((n + 4) / 3) + (n + 2)
termination_by n => n
decreasing_by omega

theorem t3_bound : DivideConquerBound t3 2 3 1 1 fun n => 1 * n ^ 1 := by
  refine ⟨fun n hn => ?_, fun n hn S hS => ?_⟩
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [t3]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [t3]
    have h1 := hS ((k + 4) / 3) (by omega)
    simp only [pow_one, one_mul]
    omega

/-- `T(n) ≤ 12 n` for `n ≠ 0`. -/
example (n : ℕ) (hn : n ≠ 0) : t3 n ≤ 12 * n := by
  have := t3_bound.pow_sub_mul_le_mul_pow (by norm_num) (by norm_num) le_rfl hn
  norm_num at this
  omega

example : (fun n => (t3 n : ℝ)) =O[Filter.atTop] fun n => (n : ℝ) ^ 1 :=
  t3_bound.isBigO_pow (by norm_num) (by norm_num) le_rfl (by norm_num)

/-! ### The hypothesis is not vacuous -/

/-- `n²` does not satisfy `T n ≤ T(⌈n/2⌉)`: at `n = 2` it would give `4 ≤ 1`. -/
example : ¬ DivideConquerBound (fun n => n ^ 2) 1 2 1 1 fun n => 0 * n ^ 0 := by
  intro h
  have := h.step 2 (by norm_num) 1 fun m hm =>
    (Nat.pow_le_pow_left (by omega : m ≤ 1) 2).trans (by norm_num)
  norm_num at this

/-! ### Supporting lemmas -/

example : (clog 3 9 : ℝ) ≤ 2 * Real.logb 3 9 := clog_le_two_mul_logb (by norm_num) (by norm_num)

end ComplexityTests.MasterTheorem
