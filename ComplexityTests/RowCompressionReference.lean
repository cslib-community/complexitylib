/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Reference
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Stationary reference examples

In the first example the padded rank is above the flat region and stays exactly `1/2`, while a
zero row entry moves to the new default `3/8`. In the second example the padded rank itself
moves from zero to `1/8`, inside the flat region. A nonzero gated output is preserved in both.
-/

namespace ComplexityTests.RowCompressionReference

open Finset Cslib.RowCompression

private theorem univ_three : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide

private noncomputable def highRow : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![1 / 2, 0], ![0, 0]]

private theorem high_rank : firstRank univ 2 0 highRow = 1 / 2 := by
  have hle : kthLargest 2 univ (fun y => highRow y 0) ≤ 1 / 2 := by
    refine not_lt.mp fun hlt => ?_
    have hcard := (lt_kthLargest_iff (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hlt
    have hsupport : ({y | (1 / 2 : ℝ) < highRow y 0} : Finset (Fin 3)) = {0} := by
      ext y
      fin_cases y <;> norm_num [highRow]
    rw [hsupport] at hcard
    norm_num at hcard
  have hge : (1 / 2 : ℝ) ≤ kthLargest 2 univ (fun y => highRow y 0) := by
    apply (le_kthLargest_iff (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
    have hsupport : ({y | (1 / 2 : ℝ) ≤ highRow y 0} : Finset (Fin 3)) = {0, 1} := by
      ext y
      fin_cases y <;> norm_num [highRow]
    rw [hsupport]
    norm_num
  unfold firstRank
  rw [le_antisymm hle hge]
  norm_num

private theorem high_threshold : threshold univ 3 (1 / 8) 0 highRow = 1 / 8 := by
  have hr : kthLargest 3 univ (fun y => entrySize (highRow y)) = 0 := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) kthLargest_nonneg
    have hcard := (lt_kthLargest_iff (by norm_num) le_rfl).mp hlt
    have hsupport : ({y | 0 < entrySize (highRow y)} : Finset (Fin 3)) = {0, 1} := by
      ext y
      fin_cases y <;> norm_num [entrySize, highRow]
    rw [hsupport] at hcard
    norm_num at hcard
  norm_num [threshold, hr]

private theorem high_default : newDefault univ 3 2 (1 / 8) 0 highRow = 3 / 8 := by
  change max (threshold univ 3 (1 / 8) 0 highRow)
    (min (firstRank univ 2 0 highRow) (3 * threshold univ 3 (1 / 8) 0 highRow)) = _
  rw [high_threshold, high_rank]
  norm_num

private theorem high_update : update univ 3 2 (1 / 8) 0 highRow =
    ![![10, 0], ![1 / 2, 0], ![3 / 8, 0]] := by
  unfold update
  rw [high_threshold, high_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, highRow]

private theorem high_first (y : Fin 3) (_hy : y ∈ (univ : Finset (Fin 3))) :
    -(1 / 4 : ℝ) ≤ highRow y 0 := by
  fin_cases y <;> norm_num [highRow]

private theorem high_second (y : Fin 3) (_hy : y ∈ (univ : Finset (Fin 3))) :
    |highRow y 1| ≤ (1 / 4 : ℝ) := by
  fin_cases y <;> norm_num [highRow]

-- The rank theorem applies to a row whose default and some actual entries really move.
example : firstRank univ 2 (newDefault univ 3 2 (1 / 8) 0 highRow)
    (update univ 3 2 (1 / 8) 0 highRow) = 1 / 2 := by
  have h := reference_firstRank_eq (η := 1 / 4) (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)
    (by norm_num : 0 < (2 : ℕ)) (by norm_num : (2 : ℕ) ≤ 3) high_first high_second
    (by rw [high_rank]; norm_num)
  exact h.trans high_rank

example : update univ 3 2 (1 / 8) 0 highRow 2 0 ≠ highRow 2 0 := by
  rw [high_update]
  norm_num [highRow]

private noncomputable def rowOutput (x v r : ℝ) : ℝ :=
  if x ≤ 4 then 0 else if 1 ≤ r then 0 else x + v + max (1 / 4) r

private theorem output_entry (x v r : ℝ) (hx : x ≤ 4) : rowOutput x v r = 0 := by
  simp [rowOutput, hx]

private theorem output_gate (x v r : ℝ) (hr : 1 ≤ r) : rowOutput x v r = 0 := by
  simp [rowOutput, hr]

private theorem output_flat (x v q r : ℝ) (hq : q ∈ Set.Icc 0 (1 / 4 : ℝ))
    (hr : r ∈ Set.Icc 0 (1 / 4 : ℝ)) : rowOutput x v q = rowOutput x v r := by
  have hq' : ¬1 ≤ q := by linarith [hq.2]
  have hr' : ¬1 ≤ r := by linarith [hr.2]
  simp only [rowOutput, hq', hr', ↓reduceIte, max_eq_left hq.2, max_eq_left hr.2]

private noncomputable def initial : State (Fin 3) := { defaultValue := 0, row := highRow }

-- An arbitrary number of zero-increment updates preserves the nonzero output 10.5.
example (j : ℕ) :
    let a := iterate univ (fun _ => 3) (fun _ => 2) (fun _ => 1 / 8) (fun _ => 0) initial j
    rowOutput (a.row 0 0) (a.row 0 1) (firstRank univ 2 a.defaultValue a.row) = 21 / 2 := by
  have h := reference_iterate_output_eq (s := univ) (n := fun _ => 3) (K := 2)
    (ρ := fun _ => 1 / 8) (a := initial) (η := 1 / 4) (H := rowOutput) (g := 1) (e := 4)
    (by norm_num) (by norm_num) high_first high_second (by norm_num) (by norm_num)
    output_entry output_gate output_flat j (by intros; norm_num) (by intros; norm_num) 0
    (mem_univ 0)
  refine h.trans ?_
  change rowOutput 10 0 (firstRank univ 2 0 highRow) = 21 / 2
  rw [high_rank]
  norm_num [rowOutput]

private def lowRow : Fin 3 → Fin 2 → ℝ := ![![10, 0], ![0, 0], ![0, 0]]

private theorem low_rank : firstRank univ 2 0 lowRow = 0 := by
  norm_num [firstRank, kthLargest, lowRow, univ_three, filter_insert, filter_image,
    filter_singleton]

private theorem low_threshold : threshold univ 3 (1 / 8) 0 lowRow = 1 / 8 := by
  norm_num [threshold, kthLargest, lowRow, entrySize, univ_three, filter_insert,
    filter_image, filter_singleton]

private theorem low_default : newDefault univ 3 2 (1 / 8) 0 lowRow = 1 / 8 := by
  change max (threshold univ 3 (1 / 8) 0 lowRow)
    (min (firstRank univ 2 0 lowRow) (3 * threshold univ 3 (1 / 8) 0 lowRow)) = _
  rw [low_threshold, low_rank]
  norm_num

private theorem low_update : update univ 3 2 (1 / 8) 0 lowRow =
    ![![10, 0], ![1 / 8, 0], ![1 / 8, 0]] := by
  unfold update
  rw [low_threshold, low_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, lowRow]

-- A low padded rank may change; the theorem requires only flat output dependence there.
example : firstRank univ 2 (newDefault univ 3 2 (1 / 8) 0 lowRow)
    (update univ 3 2 (1 / 8) 0 lowRow) = 1 / 8 ∧ firstRank univ 2 0 lowRow = 0 := by
  refine ⟨le_antisymm ?_ ?_, low_rank⟩
  · have h := reference_firstRank_le (s := univ) (n := 3) (K := 2) (ρ := 1 / 8) (z := 0)
      (w := lowRow) (η := 1 / 8) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (fun y _ => by fin_cases y <;> norm_num [lowRow])
      (fun y _ => by fin_cases y <;> norm_num [lowRow])
    simpa only [low_rank, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 8)] using h
  · have h := default_le_firstRank (s := univ) (K := 2)
      (z := newDefault univ 3 2 (1 / 8) 0 lowRow) (w := update univ 3 2 (1 / 8) 0 lowRow)
    simpa only [low_default] using h

example : rowOutput (update univ 3 2 (1 / 8) 0 lowRow 0 0)
    (update univ 3 2 (1 / 8) 0 lowRow 0 1)
    (firstRank univ 2 (newDefault univ 3 2 (1 / 8) 0 lowRow)
      (update univ 3 2 (1 / 8) 0 lowRow)) = 41 / 4 := by
  have h := reference_update_output_eq (s := univ) (n := 3) (K := 2) (ρ := 1 / 8) (z := 0)
    (w := lowRow) (η := 1 / 4) (H := rowOutput) (g := 1) (e := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun y _ => by fin_cases y <;> norm_num [lowRow])
    (fun y _ => by fin_cases y <;> norm_num [lowRow])
    (by norm_num) (by norm_num) output_entry output_gate output_flat 0 (mem_univ 0)
  refine h.trans ?_
  rw [low_rank]
  norm_num [rowOutput, lowRow]

end ComplexityTests.RowCompressionReference
