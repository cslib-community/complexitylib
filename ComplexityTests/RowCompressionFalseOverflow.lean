/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for charging false overflows

An actual two-group run first compresses a zero row to a nonzero default, then receives a negative
first-channel increment at one endpoint and a positive second-channel increment at another.
The first overflow is group one. Neither true target is heavy, and the charge is verified using
the actual raw prefix, despite the nonzero preceding compression loss.
-/

namespace ComplexityTests.RowCompressionFalseOverflow

open Finset Cslib.RowCompression

-- A negative first channel can cause the light-target error just as a positive one can.
example : (1 / 2 : ℝ) ≤ clippedError (1 / 4) 0 ![-2, 0] := by
  apply half_floor_le_clippedError (w := ![-2, 0]) (by norm_num) le_rfl
    (by norm_num) le_rfl rfl
  · intro ν
    norm_num
  · norm_num [entrySize]

-- The second-channel case does not rely on the first coordinate being large.
example : (1 / 2 : ℝ) ≤ clippedError 0 0 ![0, -2] := by
  apply half_floor_le_clippedError (w := ![0, -2]) (by norm_num) le_rfl
    le_rfl (by norm_num) rfl
  · intro ν
    norm_num
  · norm_num [entrySize]

private def initial : State (Fin 2) := { defaultValue := 0, row := 0 }

private noncomputable def increments (i : ℕ) (y : Fin 2) : Fin 2 → ℝ :=
  if i = 0 then 0 else if y = 0 then ![-1 / 512, 0] else ![0, 1 / 512]

private noncomputable def run : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 1) (dyadicFloor 1 2) increments initial

private theorem first_state : (run 1).defaultValue = 1 / 1048576 ∧
    (run 1).row = fun _ => defaultEntry (1 / 1048576) := by
  constructor
  · norm_num [run, iterate, advance, initial, increments, dyadicFloor, dyadicSlack,
      newDefault, threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · funext y ν
    fin_cases y <;> fin_cases ν <;>
      norm_num [run, iterate, advance, initial, increments, dyadicFloor, dyadicSlack,
        newDefault, threshold, kthLargest, entrySize, update, updateEntry, radius, defaultEntry,
        Fin.univ_succ, filter_insert, filter_singleton]

private theorem first_overflow :
    IsFirstOverflow univ (fun _ => 2) (fun _ => 1) (dyadicFloor 1 2) increments initial 1 := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num [stepThreshold, inputRow, iterate, initial, increments, dyadicFloor, dyadicSlack,
      threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · change dyadicFloor 1 2 1 < threshold univ 2 (dyadicFloor 1 2 1)
      (run 1).defaultValue ((run 1).row + increments 1)
    rw [first_state.1, first_state.2]
    have hlarge : ∀ y ∈ (univ : Finset (Fin 2)), dyadicFloor 1 2 1 <
        entrySize (defaultEntry (1 / 1048576) + increments 1 y) := by
      intro y _
      fin_cases y <;> norm_num [increments, dyadicFloor, dyadicSlack, entrySize, defaultEntry]
    have hcard : 2 ≤ #{y ∈ (univ : Finset (Fin 2)) | dyadicFloor 1 2 1 <
        entrySize (defaultEntry (1 / 1048576) + increments 1 y)} := by
      rw [filter_eq_self.mpr hlarge]
      norm_num
    have hrank := (lt_kthLargest_iff (by norm_num : 0 < 2)
      (dyadicFloor_nonneg (by norm_num : (0 : ℝ) ≤ 1) 2 1)).mpr hcard
    exact hrank.trans_le ((le_max_right _ _).trans (le_max_right _ _))

-- There is genuine preloss at the previous group, so the zero-loss case is insufficient.
example : (run 1).row 0 0 - uncompressedRow increments initial.row 1 0 0 = 1 / 1048576 := by
  rw [first_state.2]
  norm_num [uncompressedRow, increments, initial, defaultEntry]

-- First-overflow events are disjoint for this concrete run as well.
example (j : ℕ)
    (hj : IsFirstOverflow univ (fun _ => 2) (fun _ => 1) (dyadicFloor 1 2) increments initial j) :
    j = 1 := hj.unique first_overflow

-- The actual moment theorem applies, discharging every earlier-threshold and light-target premise.
example : 1 ≤ (2 : ℝ) ^ (4 + 1) / (2 * dyadicFloor 1 2 1 ^ 4) *
    ∑ y : Fin 2, clippedError 0 0 (uncompressedRow increments initial.row 2 y) ^ 4 := by
  apply one_le_sum_clippedError_pow_of_firstOverflow_dyadic (truth := fun _ => 0)
    (by norm_num) le_rfl rfl 2 1 (by norm_num) (by norm_num) first_overflow
  · intro y _
    exact le_rfl
  · intro y _ _
    rfl
  · norm_num [dyadicFloor, dyadicSlack]

-- Both endpoints contribute exactly (1/512)^4; the error is measured before compression.
example : (∑ y : Fin 2,
    clippedError 0 0 (uncompressedRow increments initial.row 2 y) ^ 4) = 1 / 34359738368 := by
  norm_num [uncompressedRow, increments, initial, clippedError, Fin.sum_univ_two, sum_range_succ]

example : (2 : ℝ) ^ (4 + 1) / (2 * dyadicFloor 1 2 1 ^ 4) *
    ∑ y : Fin 2, clippedError 0 0 (uncompressedRow increments initial.row 2 y) ^ 4 = 512 := by
  norm_num [uncompressedRow, increments, initial, clippedError, dyadicFloor, dyadicSlack,
    Fin.sum_univ_two, sum_range_succ]

end ComplexityTests.RowCompressionFalseOverflow
