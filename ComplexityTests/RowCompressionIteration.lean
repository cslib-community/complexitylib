/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Iteration
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Iterated compression with genuine increments and loss

The first group adds ten and preserves it. The second subtracts ten, after which compression
introduces the new default four. Both thresholds equal their floors. Reducing the first capacity
from two to one produces an overflow, so the no-overflow hypothesis is not automatic.
-/

namespace ComplexityTests.RowCompressionIteration

open Finset Cslib.RowCompression

private def initial : State (Fin 1) := { defaultValue := 0, row := fun _ => ![0, 0] }

private def increments (i : ℕ) : Fin 1 → Fin 2 → ℝ :=
  fun _ => if i = 0 then ![10, 0] else ![-10, 0]

private def floors (i : ℕ) : ℝ := if i = 0 then 1 else 4

private noncomputable def run : ℕ → State (Fin 1) :=
  iterate univ (fun _ => 2) (fun _ => 1) floors increments initial

private theorem first_state : (run 1).defaultValue = 3 ∧ (run 1).row 0 = ![10, 0] := by
  constructor
  · norm_num [run, iterate, advance, initial, increments, floors, newDefault, threshold,
      kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · funext ν
    fin_cases ν <;>
      norm_num [run, iterate, advance, initial, increments, floors, newDefault, threshold,
        kthLargest, entrySize, update, updateEntry, radius, defaultEntry, Fin.univ_succ,
        filter_insert, filter_singleton]

private theorem second_state : (run 2).defaultValue = 4 ∧ (run 2).row 0 = ![4, 0] := by
  have hrow : (run 1).row = fun _ => (![10, 0] : Fin 2 → ℝ) := by
    funext y
    fin_cases y
    exact first_state.2
  change (advance univ 2 1 4 (increments 1) (run 1)).defaultValue = 4 ∧
    (advance univ 2 1 4 (increments 1) (run 1)).row 0 = ![4, 0]
  simp only [advance, first_state.1, hrow]
  constructor
  · norm_num [increments, newDefault, threshold, kthLargest, entrySize, Fin.univ_succ,
      filter_insert, filter_singleton]
  · funext ν
    fin_cases ν <;>
      norm_num [increments, newDefault, threshold, kthLargest, entrySize, update, updateEntry,
        radius, defaultEntry, Fin.univ_succ, filter_insert, filter_singleton]

-- Compression has introduced a nonzero loss, although the raw increments cancel.
example : (run 2).row 0 0 - uncompressedRow increments initial.row 2 0 0 = 4 := by
  rw [second_state.2]
  norm_num [uncompressedRow, initial, increments, sum_range_succ]

private theorem no_overflow (i : ℕ) (hi : i < 2) :
    stepThreshold univ (fun _ => 2) (fun _ => 1) floors increments initial i ≤ floors i := by
  interval_cases i
  · norm_num [stepThreshold, inputRow, iterate, initial, increments, floors, threshold,
      kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · change threshold univ 2 4 (run 1).defaultValue ((run 1).row + increments 1) ≤ 4
    have hrow : (run 1).row = fun _ => (![10, 0] : Fin 2 → ℝ) := by
      funext y
      fin_cases y
      exact first_state.2
    rw [first_state.1, hrow]
    norm_num [increments, threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert,
      filter_singleton]

-- The derived prefix-loss theorem applies to an actual nonzero-loss execution.
example (ν : Fin 2) : |(run 2).row 0 ν - uncompressedRow increments initial.row 2 0 ν| ≤ 30 := by
  have h := abs_iterate_sub_uncompressed_le_of_no_overflow 2 no_overflow 0 ν
  norm_num [floors, sum_range_succ] at h
  exact h

-- An undersized capacity causes overflow already at the first group.
example : ¬ stepThreshold univ (fun _ => 1) (fun _ => 1) floors increments initial 0 ≤
    floors 0 := by
  norm_num [stepThreshold, inputRow, iterate, initial, increments, floors, threshold,
    kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]

private noncomputable def perturbed : State (Fin 1) :=
  { defaultValue := 1 / 10, row := fun _ => ![1 / 10, 1 / 10] }

-- The polynomial propagation estimate applies to genuinely different full initial states.
example (y : Fin 1) (ν : Fin 2) :
    |(run 2).row y ν -
      (iterate univ (fun _ => 2) (fun _ => 1) floors increments perturbed 2).row y ν| ≤
        512 / 5 := by
  have h := iterate_stability_of_pow_le (s := univ) (n := fun _ => 2) (K := fun _ => 1)
    (ρ := floors) (Δ := increments) (a := initial) (b := perturbed) (δ := 1 / 10)
    (by norm_num) (by norm_num [initial, perturbed])
    (fun y _ ν => by fin_cases ν <;> norm_num [initial, perturbed]) 2 3
    (by intros; norm_num) (by intros; norm_num) (by norm_num)
  have hy := h.2 y (mem_univ y) ν
  norm_num at hy
  exact hy

end ComplexityTests.RowCompressionIteration
