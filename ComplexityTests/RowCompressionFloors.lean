/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Floors
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Concrete small-floor schedules

Check the explicit halving slacks and nonzero floors, including the empty schedule. A two-group
compression execution with zero raw increments acquires a positive default; its no-overflow
property is checked directly, then the floor sum controls its actual compression loss.
-/

namespace ComplexityTests.RowCompressionFloors

open Finset Cslib.RowCompression

example : dyadicSlack 3 0 = 4 ∧ dyadicSlack 3 1 = 2 ∧ dyadicSlack 3 2 = 1 := by
  norm_num [dyadicSlack]

example : dyadicFloor 1 3 0 = 1 / 1099511627776 ∧
    dyadicFloor 1 3 1 = 1 / 1048576 ∧ dyadicFloor 1 3 2 = 1 / 1024 := by
  norm_num [dyadicFloor, dyadicSlack]

-- Actual nonzero previous floors satisfy the hundredth-of-current-floor estimate.
example : 6 * (dyadicFloor 1 3 0 + dyadicFloor 1 3 1) ≤ dyadicFloor 1 3 2 / 100 := by
  norm_num [dyadicFloor, dyadicSlack]

-- The total-sum theorem includes a schedule with no groups.
example : (∑ i ∈ range 0, dyadicFloor (2 / 3) 0 i) = 0 := by simp

-- The scale need not be one, and the number of groups is arbitrary.
example (m : ℕ) : 6 * ∑ i ∈ range m, dyadicFloor (2 / 3) m i ≤ 1 / 150 := by
  have h := six_sum_range_dyadicFloor_le_scale (η := 2 / 3) (by norm_num) m
  norm_num at h
  exact h

private def initial : State (Fin 1) := { defaultValue := 0, row := fun _ => ![0, 0] }

private noncomputable def run : ℕ → State (Fin 1) :=
  iterate univ (fun _ => 2) (fun _ => 1) (dyadicFloor 1 2) (fun _ => 0) initial

private theorem first_state : (run 1).defaultValue = 1 / 1048576 ∧
    (run 1).row = fun _ => defaultEntry (1 / 1048576) := by
  constructor
  · norm_num [run, iterate, advance, initial, dyadicFloor, dyadicSlack, newDefault, threshold,
      kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · funext y ν
    fin_cases y
    fin_cases ν <;>
      norm_num [run, iterate, advance, initial, dyadicFloor, dyadicSlack, newDefault, threshold,
        kthLargest, entrySize, update, updateEntry, radius, defaultEntry, Fin.univ_succ,
        filter_insert, filter_singleton]

private theorem no_overflow (i : ℕ) (hi : i < 2) :
    stepThreshold univ (fun _ => 2) (fun _ => 1) (dyadicFloor 1 2) (fun _ => 0) initial i ≤
      dyadicFloor 1 2 i := by
  interval_cases i
  · norm_num [stepThreshold, inputRow, iterate, initial, dyadicFloor, dyadicSlack, threshold,
      kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · change threshold univ 2 (dyadicFloor 1 2 1) (run 1).defaultValue ((run 1).row + 0) ≤
      dyadicFloor 1 2 1
    rw [first_state.1, first_state.2, add_zero]
    norm_num [dyadicFloor, dyadicSlack, threshold, kthLargest, entrySize, defaultEntry,
      Fin.univ_succ, filter_insert, filter_singleton]

-- The new numerical schedule closes the small-total-loss premise for a real execution.
example (y : Fin 1) (ν : Fin 2) : |(run 2).row y ν| ≤ 1 / 100 := by
  have h := abs_iterate_sub_uncompressed_le_of_no_overflow 2 no_overflow y ν
  have hsum := six_sum_range_dyadicFloor_le_scale (η := 1) (by norm_num) 2
  have h' := h.trans hsum
  fin_cases ν <;> simpa [uncompressedRow, initial, run] using h'

-- There are three updates left including group one, but only two strictly after it.
example : dyadicSlack 4 1 = 4 ∧ (28 : ℝ) ^ (4 - 1) ≤ 28 * (4 + 1) ^ 5 := by
  constructor
  · norm_num [dyadicSlack]
  · simpa [dyadicSlack] using propagation_le_dyadicSlack (m := 4) (i := 1) (by norm_num)

end ComplexityTests.RowCompressionFloors
