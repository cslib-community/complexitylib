/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomFalseOverflow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Actual polynomial output error on a false first overflow

The same Boolean environment controls retention and the signed increments. On `true`, the
real compression update raises the default to `1/8192` and erases a negative second channel.
Both true targets are zero, so its first overflow is false. Its final preparation output is
one at the first endpoint, while the true output is zero. The masked fourth moment is exactly
`1/2`; the normalized single-group and finite-union bounds apply to that nonzero error.
-/

namespace ComplexityTests.PolynomialAtomFalseOverflow

open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators

private def source (_σ : Bool) (x : Fin 2) : Prop := x = 0

private def retained (σ : Bool) (y : Fin 2) : Prop := σ = true ∨ y = 0

private instance (σ : Bool) (x : Fin 2) : Decidable (source σ x) :=
  inferInstanceAs (Decidable (x = 0))

private instance (σ : Bool) (y : Fin 2) : Decidable (retained σ y) :=
  inferInstanceAs (Decidable (σ = true ∨ y = 0))

private theorem source_set (σ : Bool) : ({x | source σ x} : Finset (Fin 2)) = {0} := by
  change (univ.filter fun x : Fin 2 => x = 0) = {0}
  decide

private theorem retained_true : ({y | retained true y} : Finset (Fin 2)) = univ := by
  ext y
  simp [retained]

private theorem retained_false : ({y | retained false y} : Finset (Fin 2)) = {0} := by
  ext y
  simp [retained]

private def initial : State (Fin 2) := { defaultValue := 0, row := 0 }

private noncomputable def incoming : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![1 / 8192, -1 / 16384]]

private noncomputable def increments (σ : Bool) (_x : Fin 2) (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if σ = true ∧ i = 0 then incoming else 0

private noncomputable def actual (σ : Bool) (x : Fin 2) : State (Fin 2) :=
  iterate {y | retained σ y} (fun _ => 2) (fun _ => 2) (dyadicFloor (1 / 16) 1)
    (increments σ x) initial 1

private theorem rank_two (v : Fin 2 → ℝ) (h0 : v 0 = 1) (h1 : v 1 = 1 / 8192) :
    kthLargest 2 univ v = 1 / 8192 := by
  apply le_antisymm
  · refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 8192)).mp hlt
    have hs : ({y | (1 / 8192 : ℝ) < v y} : Finset (Fin 2)) = {0} := by
      ext y
      fin_cases y <;> norm_num [h0, h1]
    rw [hs] at hc
    norm_num at hc
  · apply (le_kthLargest_iff (by norm_num) (by norm_num : (0 : ℝ) < 1 / 8192)).mpr
    have hs : ({y | (1 / 8192 : ℝ) ≤ v y} : Finset (Fin 2)) = univ := by
      ext y
      fin_cases y <;> norm_num [h0, h1]
    rw [hs]
    norm_num

private theorem incoming_threshold :
    threshold univ 2 (dyadicFloor (1 / 16) 1 0) 0 incoming = 1 / 8192 := by
  unfold threshold
  rw [rank_two (fun y => entrySize (incoming y)) (by norm_num [incoming, entrySize])
    (by norm_num [incoming, entrySize])]
  norm_num [dyadicFloor, dyadicSlack]

private theorem incoming_default :
    newDefault univ 2 2 (dyadicFloor (1 / 16) 1 0) 0 incoming = 1 / 8192 := by
  unfold newDefault
  rw [incoming_threshold, rank_two (fun y => incoming y 0) (by norm_num [incoming])
    (by norm_num [incoming])]
  norm_num

private theorem actual_true (x : Fin 2) : actual true x =
    { defaultValue := 1 / 8192, row := ![![1, 0], ![1 / 8192, 0]] } := by
  unfold actual
  rw [retained_true]
  have hin : initial.row + increments true x 0 = incoming := by simp [initial, increments]
  change advance univ 2 2 (dyadicFloor (1 / 16) 1 0) (increments true x 0) initial = _
  unfold advance
  rw [hin]
  change State.mk (newDefault univ 2 2 (dyadicFloor (1 / 16) 1 0) 0 incoming)
    (update univ 2 2 (dyadicFloor (1 / 16) 1 0) 0 incoming) = _
  rw [incoming_default]
  congr 1
  unfold update
  rw [incoming_threshold, incoming_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, incoming]

private def falseEvent (σ : Bool) (x : Fin 2) : Prop :=
  IsFirstOverflow {y | retained σ y} (fun _ => 2) (fun _ => 2)
      (dyadicFloor (1 / 16) 1) (increments σ x) initial 0 ∧
    ¬ heavyCountEvent retained univ (fun _ => 0) (dyadicFloor (1 / 16) 1 0) 2 σ

private theorem falseEvent_iff (σ : Bool) (x : Fin 2) : falseEvent σ x ↔ σ = true := by
  cases σ
  · unfold falseEvent
    rw [retained_false]
    norm_num [IsFirstOverflow, stepThreshold, inputRow, initial, increments,
      dyadicFloor, dyadicSlack, threshold, kthLargest, entrySize]
  · unfold falseEvent
    rw [retained_true]
    have hin : inputRow univ (fun _ => 2) (fun _ => 2) (dyadicFloor (1 / 16) 1)
        (increments true x) initial 0 = incoming := by simp [inputRow, initial, increments]
    have ht : stepThreshold univ (fun _ => 2) (fun _ => 2) (dyadicFloor (1 / 16) 1)
        (increments true x) initial 0 = 1 / 8192 := by
      unfold stepThreshold
      rw [hin]
      exact incoming_threshold
    norm_num [IsFirstOverflow, ht, heavyCountEvent, dyadicFloor, dyadicSlack]

-- Both the actual compression change and the false-overflow classification are nontrivial.
example (x : Fin 2) : falseEvent true x ∧ ¬ falseEvent false x ∧
    (actual true x).defaultValue = 1 / 8192 ∧
    uncompressedRow (increments true x) initial.row 1 1 1 = -1 / 16384 ∧
    (actual true x).row 1 1 = 0 := by
  rw [actual_true]
  norm_num [falseEvent_iff, uncompressedRow, increments, incoming, initial]

private theorem actual_rank (x : Fin 2) :
    firstRank univ 2 (actual true x).defaultValue (actual true x).row = 1 / 8192 := by
  rw [actual_true]
  unfold firstRank
  rw [rank_two (fun y => (![![1, 0], ![1 / 8192, 0]] : Fin 2 → Fin 2 → ℝ) y 0)
    (by norm_num) (by norm_num)]
  norm_num

private theorem actual_error_true (x y : Fin 2) :
    PolynomialAtomRow.preparation.stateRootError 1 univ 2 (actual true x) ⟨0, 0⟩ y =
      if y = 0 then 1 else 0 := by
  unfold PolynomialAtomRow.stateRootError
  rw [actual_rank, actual_true]
  have htrue : PolynomialAtomRow.preparation.eval 1 0
      (firstRank (univ : Finset (Fin 2)) 2 0 0) = 0 :=
    polynomialPrepRow4_eq_zero_of_entry_le (by norm_num) (by norm_num)
  simp only [Pi.zero_apply, htrue, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_zero]
  change polynomialPrepRow4 1 _ (1 / 8192) ^ (4⁻¹ : ℝ) = _
  rw [polynomialPrepRow4_of_rank_le (by norm_num) (by norm_num)]
  fin_cases y
  · rw [polynomialPrepCutoff4_eq_one (by norm_num) (by norm_num)]
    norm_num
  · rw [polynomialPrepCutoff4_eq_zero (by norm_num) (by norm_num)]
    norm_num

open Classical in
private noncomputable def maskedError (σ : Bool) (x y : Fin 2) : ℝ :=
  if falseEvent σ x then PolynomialAtomRow.preparation.stateRootError 1 {y | retained σ y}
    2 (actual σ x) ⟨0, 0⟩ y else 0

private theorem maskedError_eq (σ : Bool) (x y : Fin 2) :
    maskedError σ x y = if σ = true ∧ y = 0 then 1 else 0 := by
  cases σ <;> simp [maskedError, falseEvent_iff, retained, actual_error_true]

-- The exact normalized output moment is positive; it is not an empty-mask application.
example : rowNormPow 4 1 1 source retained maskedError = 1 / 2 := by
  norm_num [rowNormPow, source_set, retained, maskedError_eq, expect_eq_sum_div_card,
    sum_filter, Fintype.sum_bool, Fin.sum_univ_two]

private noncomputable def prefixError (σ : Bool) (x y : Fin 2) : ℝ :=
  clippedError 0 0 (uncompressedRow (increments σ x) initial.row 1 y)

-- Apply the specified-group theorem with every truth, default, and floor hypothesis discharged.
example : rowNormPow 4 1 1 source retained maskedError ≤
    (64 * 2 / (2 * dyadicFloor (1 / 16) 1 0 ^ 4)) *
      rowNormPow 4 1 1 source retained prefixError := by
  have h := PolynomialAtomRow.preparation.rowNormPow_falseFirstOverflow_le
      (θ := 1) (η := 1 / 16) (N := 1) (u := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      source retained (fun _ => 2) 2 (by norm_num) 1 0 (by norm_num) (by norm_num)
      increments (fun _ _ => initial) (fun _ _ _ => 0)
      (by intros; rfl) (by intros; exact le_rfl) (by intros; rfl)
  dsimp only at h
  convert h using 1
  · congr 1
    funext σ x y
    simp only [maskedError, falseEvent, actual, Pi.zero_apply, Pi.zero_def]
    congr 1
  · rfl

-- The raw error moment is measured before the negative second channel is erased.
example : rowNormPow 4 1 1 source retained prefixError = (1 + (1 / 8192 : ℝ) ^ 4) / 2 := by
  norm_num [rowNormPow, source_set, retained, prefixError, uncompressedRow, increments, incoming,
    initial, clippedError, expect_eq_sum_div_card, sum_filter, Fintype.sum_bool, Fin.sum_univ_two]

-- The union theorem gives the same normalization, with the actual prefix at `j + 1`.
open Classical in
example :
    rowNormPow 4 1 1 source retained (fun σ x y =>
      if ∃ j < 1,
        IsFirstOverflow {y | retained σ y} (fun _ => 2) (fun _ => 2)
            (dyadicFloor (1 / 16) 1) (increments σ x) initial j ∧
          ¬ heavyCountEvent retained univ (fun _ => 0) (dyadicFloor (1 / 16) 1 j) 2 σ
      then PolynomialAtomRow.preparation.stateRootError 1 {y | retained σ y}
        2 (actual σ x) ⟨0, 0⟩ y else 0) ≤
      ∑ j ∈ range 1, (64 * 2 / (2 * dyadicFloor (1 / 16) 1 j ^ 4)) *
        rowNormPow 4 1 1 source retained (fun σ x y =>
          clippedError 0 0 (uncompressedRow (increments σ x) initial.row (j + 1) y)) :=
  PolynomialAtomRow.preparation.rowNormPow_falseFirstOverflowBefore_le
    (θ := 1) (η := 1 / 16) (N := 1) (u := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    source retained (fun _ => 2) 2 (by norm_num) 1 (by intros; norm_num)
    increments (fun _ _ => initial) (fun _ _ _ => 0)
    (by intros; rfl) (by intros; exact le_rfl) (by intros; rfl)

-- The finite-union result also admits an empty horizon without a capacity premise.
open Classical in
example :
    rowNormPow 4 1 1 source retained (fun σ x y =>
      if ∃ j < 0,
        IsFirstOverflow {y | retained σ y} (fun _ => 0) (fun _ => 2)
            (dyadicFloor (1 / 16) 0) (increments σ x) initial j ∧
          ¬ heavyCountEvent retained univ (fun _ => 0) (dyadicFloor (1 / 16) 0 j) 0 σ
      then PolynomialAtomRow.preparation.stateRootError 1 {y | retained σ y}
        2 initial ⟨0, 0⟩ y else 0) ≤
      ∑ j ∈ range 0, (64 * 2 / (0 * dyadicFloor (1 / 16) 0 j ^ 4)) *
        rowNormPow 4 1 1 source retained (fun σ x y =>
          clippedError 0 0 (uncompressedRow (increments σ x) initial.row (j + 1) y)) :=
  PolynomialAtomRow.preparation.rowNormPow_falseFirstOverflowBefore_le
    (θ := 1) (η := 1 / 16) (N := 1) (u := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    source retained (fun _ => 0) 2 (by norm_num) 0 (by simp)
    increments (fun _ _ => initial) (fun _ _ _ => 0)
    (by intros; rfl) (by intros; exact le_rfl) (by intros; rfl)

end ComplexityTests.PolynomialAtomFalseOverflow
