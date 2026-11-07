/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Preloss
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Weighted compression preloss examples

A two-group calculation has actual nonzero compression loss, satisfies the small-floor and
no-overflow hypotheses, and invokes the weighted theorem. Other examples check saturation,
negative raw first coordinates, and exact targets with zero error.
-/

namespace ComplexityTests.RowCompressionPreloss

open Finset Cslib.RowCompression

private def zeroState : State (Fin 1) := ⟨0, fun _ => ![0, 0]⟩

private noncomputable def floors (i : ℕ) : ℝ := if i = 0 then 1 / 100 else 1 / 10

private theorem no_overflow (i : ℕ) (hi : i < 2) :
    stepThreshold univ (fun _ => 1) (fun _ => 1) floors (fun _ => 0) zeroState i ≤
      floors i := by
  interval_cases i <;>
    norm_num [stepThreshold, inputRow, iterate, advance, zeroState, floors, threshold,
      newDefault, update, updateEntry, radius, entrySize, defaultEntry, kthLargest, Fin.univ_succ]

-- Two genuine compression changes: the raw prefix stays zero while the stored row becomes 0.1.
example : (iterate univ (fun _ => 1) (fun _ => 1) floors (fun _ => 0) zeroState 2).row 0 0 =
    1 / 10 := by
  norm_num [iterate, advance, zeroState, floors, threshold, newDefault, update, updateEntry,
    radius, entrySize, defaultEntry, kthLargest, Fin.univ_succ]

-- The theorem applies to this concrete schedule; its weighted right side is 24·(0.01+0.1)/2.
example (ν : Fin 2) :
    |(iterate univ (fun _ => 1) (fun _ => 1) floors (fun _ => 0) zeroState 2).row 0 ν -
      uncompressedRow (fun _ => 0) zeroState.row 2 0 ν| ≤ 33 / 25 := by
  have h := abs_iterate_sub_uncompressed_le_weighted (s := univ) (n := fun _ => 1)
    (K := fun _ => 1) (ρ := floors) (Δ := fun _ => 0) (a := zeroState)
    (η := 1) (d := 1) (v := 0) (by norm_num) le_rfl 2 no_overflow
    (by intro i hi; interval_cases i <;> norm_num [floors])
    (by intro i hi; interval_cases i <;> norm_num [floors, sum_range_succ]) 0 ν
  norm_num [floors, uncompressedRow, zeroState, clippedError, sum_range_succ] at h
  simpa [uncompressedRow, zeroState] using h

-- Relative error saturates at one, and either channel can attain the maximum.
example : clippedError 1 0 (![-4, 0] : Fin 2 → ℝ) = 1 ∧
    clippedError 1 0 (![1, 2] : Fin 2 → ℝ) = 1 := by
  norm_num [clippedError]

-- Exact targets above the sensitivity floor force zero compression change in both coordinates.
example (d v : ℝ) (hd : 1 ≤ d) (w : Fin 1 → Fin 2 → ℝ)
    (hw : w 0 = ![d, v]) (hno : threshold univ 2 (1 / 10) 0 w ≤ 1 / 10) (ν : Fin 2) :
    update univ 2 1 (1 / 10) 0 w 0 ν = w 0 ν := by
  have h := abs_update_sub_le_mul_clippedError (K := 1) (η := 1) (d := d) (v := v)
    (raw := ![d, v]) (by norm_num) hd hno (by norm_num)
    (by rw [hw]; norm_num) ν
  have he : clippedError d v (![d, v] : Fin 2 → ℝ) = 0 := by simp [clippedError]
  rw [he, mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

-- The explicit dyadic schedule discharges all small-floor conditions, even with a real change.
example :
    |(iterate univ (fun _ => 1) (fun _ => 1) (dyadicFloor 1 1)
        (fun _ => 0) zeroState 1).row 0 0 -
      uncompressedRow (fun _ => 0) zeroState.row 1 0 0| ≤ 3 / 256 := by
  have h := abs_iterate_sub_uncompressed_le_weighted_dyadic (s := univ)
    (n := fun _ => 1) (K := fun _ => 1) (Δ := fun _ => 0) (a := zeroState)
    (η := 1) (d := 1) (v := 0) (by norm_num) le_rfl 1 1 le_rfl
    (by
      intro i hi
      interval_cases i
      norm_num [stepThreshold, inputRow, iterate, zeroState, dyadicFloor, dyadicSlack,
        threshold, kthLargest, entrySize, Fin.univ_succ]) 0 0
  norm_num [dyadicFloor, dyadicSlack, uncompressedRow, zeroState, clippedError] at h ⊢
  exact h

end ComplexityTests.RowCompressionPreloss
