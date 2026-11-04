/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.PolynomialAtomRows.FirstOverflow
import Complexity.Foundations.Analysis.RowCompression.PreloadedIteration
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Actual polynomial relative-stability regressions

The small-count example has one true entry above the sentinel, a second entry perturbed across
the preparation support boundary, and a low entry with a negative second channel. An actual
first overflow raises the default and erases that signed channel. Its polynomial root output
error is strictly positive, yet every post-addition raw error is at most `10⁻⁷`. The preceding
global prefix has large error, so the tail-only indexing of the theorem is essential.

The same calculation also exercises an error envelope above one. Further examples distinguish
gate closure by a large retained rank from persistent closure after the default becomes large.
-/

namespace ComplexityTests.PolynomialAtomRelative

open Finset Cslib Cslib.RowCompression

private noncomputable def truth : Fin 3 → Fin 2 → ℝ := ![![1000, 0], ![1 / 2, 0], ![0, 0]]

private noncomputable def raw : Fin 3 → Fin 2 → ℝ :=
  ![![1000, -1 / 40000000], ![1 / 2 + 1 / 100000000, 0],
    ![1 / 10000000, -1 / 20000000]]

private def initial : State (Fin 3) := ⟨0, 0⟩

private noncomputable def increments (i : ℕ) : Fin 3 → Fin 2 → ℝ :=
  if i = 0 then raw else 0

private noncomputable def actual : State (Fin 3) :=
  iterate univ (fun _ => 3) (fun _ => 3) (dyadicFloor (1 / 20000) 1) increments initial 1

private noncomputable def reference : State (Fin 3) :=
  stationaryContinuation univ (fun _ => 3) 3 (dyadicFloor (1 / 20000) 1)
    increments initial truth 0 1

private theorem rank_three {v : Fin 3 → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (h0 : u < v 0) (h1 : u < v 1) (h2 : v 2 = u) : kthLargest 3 univ v = u := by
  apply le_antisymm
  · refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff (by norm_num) hu).mp hlt
    have hs : ({y | u < v y} : Finset (Fin 3)) = {0, 1} := by
      ext y
      fin_cases y
      · simp [h0]
      · simp [h1]
      · simp [h2]
    rw [hs] at hc
    norm_num at hc
  · rcases eq_or_lt_of_le hu with rfl | hu
    · exact kthLargest_nonneg
    · apply (le_kthLargest_iff (by norm_num) hu).mpr
      have hs : ({y | u ≤ v y} : Finset (Fin 3)) = univ := by
        ext y
        fin_cases y
        · simp [h0.le]
        · simp [h1.le]
        · simp [h2]
      rw [hs]
      norm_num

private theorem floor_zero : dyadicFloor (1 / 20000) 1 0 = 1 / 20480000 := by
  norm_num [dyadicFloor, dyadicSlack]

private theorem raw_threshold :
    threshold univ 3 (1 / 20480000) 0 raw = 1 / 10000000 := by
  unfold threshold
  rw [rank_three (v := fun y => entrySize (raw y)) (u := 1 / 10000000)
    (by norm_num) (by norm_num [raw, entrySize]) (by norm_num [raw, entrySize])
    (by norm_num [raw, entrySize])]
  norm_num

private theorem raw_default :
    newDefault univ 3 3 (1 / 20480000) 0 raw = 1 / 10000000 := by
  unfold newDefault
  rw [raw_threshold, rank_three (v := fun y => raw y 0) (u := 1 / 10000000)
    (by norm_num) (by norm_num [raw]) (by norm_num [raw]) (by norm_num [raw])]
  norm_num

private theorem actual_state : actual =
    ⟨1 / 10000000, ![![1000, -1 / 40000000], ![1 / 2 + 1 / 100000000, 0],
      ![1 / 10000000, 0]]⟩ := by
  change advance univ 3 3 (dyadicFloor (1 / 20000) 1 0) (increments 0) initial = _
  simp only [advance, increments, initial, ↓reduceIte, zero_add, floor_zero]
  rw [raw_default]
  congr 1
  unfold update
  rw [raw_threshold, raw_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [raw, updateEntry, radius, entrySize, defaultEntry]

private theorem truth_rank : kthLargest 3 univ (fun y => truth y 0) = 0 :=
  rank_three (by norm_num) (by norm_num [truth]) (by norm_num [truth]) (by norm_num [truth])

private theorem truth_threshold : threshold univ 3 (1 / 20480000) 0 truth = 1 / 20480000 := by
  have hs : (fun y => entrySize (truth y)) = fun y => truth y 0 := by
    funext y
    fin_cases y <;> norm_num [truth, entrySize]
  norm_num [threshold, hs, truth_rank]

private theorem truth_default : newDefault univ 3 3 (1 / 20480000) 0 truth = 1 / 20480000 := by
  norm_num [newDefault, truth_threshold, truth_rank]

private theorem reference_state : reference =
    ⟨1 / 20480000, ![![1000, 0], ![1 / 2, 0], ![1 / 20480000, 0]]⟩ := by
  have hs : stationaryState univ (fun _ => 3) (fun _ => 3) (dyadicFloor (1 / 20000) 1)
      increments initial truth 0 = ⟨0, truth⟩ := by
    simp [stationaryState, initial]
  unfold reference stationaryContinuation
  rw [hs]
  change advance univ 3 3 (dyadicFloor (1 / 20000) 1 (0 + 0)) 0 ⟨0, truth⟩ = _
  simp only [advance, floor_zero, add_zero]
  rw [truth_default]
  congr 1
  unfold update
  rw [truth_threshold, truth_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [truth, updateEntry, radius, entrySize, defaultEntry]

private theorem actual_rank : firstRank univ 3 actual.defaultValue actual.row = 1 / 10000000 := by
  rw [actual_state]
  unfold firstRank
  rw [rank_three (u := 1 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem reference_rank : firstRank univ 3 reference.defaultValue reference.row =
    1 / 20480000 := by
  rw [reference_state]
  unfold firstRank
  rw [rank_three (u := 1 / 20480000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

private theorem first_overflow : IsFirstOverflow univ (fun _ => 3) (fun _ => 3)
    (dyadicFloor (1 / 20000) 1) increments initial 0 := by
  refine ⟨by simp, ?_⟩
  simp only [stepThreshold, inputRow, iterate_zero, initial, increments, ↓reduceIte,
    zero_add, floor_zero, raw_threshold]
  norm_num

private theorem prefix_error (y : Fin 3) :
    clippedError (truth y 0) (truth y 1) (raw y) ≤ 1 / 10000000 := by
  fin_cases y <;> norm_num [truth, raw, clippedError]

private theorem raw_one : uncompressedRow increments initial.row 1 = raw := by
  funext y ν
  simp [uncompressedRow, initial, increments]

-- Compression has a real effect and the global prefix before the first input is inaccurate.
example : IsFirstOverflow univ (fun _ => 3) (fun _ => 3) (dyadicFloor (1 / 20000) 1)
      increments initial 0 ∧ actual.defaultValue = 1 / 10000000 ∧
    raw 2 1 = -1 / 20000000 ∧ actual.row 2 1 = 0 ∧
    1 / 10000000 < clippedError (truth 0 0) (truth 0 1)
      (uncompressedRow increments initial.row 0 0) := by
  refine ⟨first_overflow, ?_⟩
  rw [actual_state]
  norm_num [raw, truth, initial, clippedError]

-- This instance exercises the small-count, small-budget branch, including a marked large entry.
example : ({y | (528 : ℝ) < truth y 0} : Finset (Fin 3)) = {0} ∧
    #{y : Fin 3 | (32 : ℝ) < truth y 0} < 3 ∧
    529 * prefixErrorBudget (fun _ => 1 / 10000000) 1 ≤ 1 / 8 := by
  have hs : ({y | (528 : ℝ) < truth y 0} : Finset (Fin 3)) = {0} := by
    ext y
    fin_cases y <;> norm_num [truth]
  refine ⟨hs, ?_, ?_⟩
  · have hc : ({y | (32 : ℝ) < truth y 0} : Finset (Fin 3)) = {0} := by
      ext y
      fin_cases y <;> norm_num [truth]
    rw [hc]
    norm_num
  · norm_num [prefixErrorBudget]

private theorem positive_error :
    0 < PolynomialAtomRow.preparation.stateRootError 1 univ 3 actual reference 1 := by
  have ha : PolynomialAtomRow.preparation.eval 1 (actual.row 1 0)
      (firstRank univ 3 actual.defaultValue actual.row) =
      polynomialSwitch4 (1 / 2) (3 / 4) (1 / 2 + 1 / 100000000) := by
    rw [actual_rank, actual_state]
    change polynomialPrepRow4 1 (1 / 2 + 1 / 100000000) (1 / 10000000) = _
    rw [polynomialPrepRow4_of_rank_le (by norm_num) (by norm_num)]
    norm_num [polynomialPrepCutoff4]
  have hb : PolynomialAtomRow.preparation.eval 1 (reference.row 1 0)
      (firstRank univ 3 reference.defaultValue reference.row) = 0 := by
    rw [reference_state]
    exact polynomialPrepRow4_eq_zero_of_entry_le (by norm_num) (by norm_num)
  have hp : 0 < polynomialSwitch4 (1 / 2 : ℝ) (3 / 4) (1 / 2 + 1 / 100000000) := by
    have hn : polynomialSwitch4 (1 / 2 : ℝ) (3 / 4) (1 / 2 + 1 / 100000000) ≠ 0 := by
      rw [ne_eq, polynomialSwitch4_eq_zero_iff (by norm_num)]
      norm_num
    exact lt_of_le_of_ne (polynomialSwitch4_nonneg _ _ _) (Ne.symm hn)
  unfold PolynomialAtomRow.stateRootError
  rw [ha, hb, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_zero]
  exact Real.rpow_pos_of_pos hp _

-- The final root error is positive and bounded by the actual post-addition raw-prefix envelope.
example : ∃ C : ℝ, 0 ≤ C ∧
    0 < PolynomialAtomRow.preparation.stateRootError 1 univ 3 actual reference 1 ∧
    |PolynomialAtomRow.preparation.stateRootError 1 univ 3 actual reference 1| ≤
      C * (7 / 2500000) := by
  obtain ⟨C, hC, hbound⟩ := PolynomialAtomRow.preparation.exists_firstOverflow_root_bound
    (θ := 1) (by norm_num)
  refine ⟨C, hC, positive_error, ?_⟩
  have h := hbound univ (fun _ => 3) increments initial truth (1 / 20000) 3
    (by norm_num) (by norm_num) (by norm_num) rfl 1 0 (by norm_num) first_overflow
    (fun y _ => by fin_cases y <;> norm_num [truth])
    (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num)
    (fun _ => 1 / 10000000) (by intros; norm_num)
    (by
      intro i _ hi y _
      have hi0 : i = 0 := by omega
      subst i
      change clippedError (truth y 0) (truth y 1) (uncompressedRow increments initial.row 1 y) ≤ _
      rw [raw_one]
      exact prefix_error y) 1 (mem_univ 1)
  norm_num [sum_Ico_eq_sum_range] at h
  exact h

-- The same positive-error calculation is accepted with an envelope above one. The bound uses
-- output range in that case; the endpoint does not assume a small propagation budget.
example : (1 / 8 : ℝ) < 529 * prefixErrorBudget (fun _ => 2) 1 ∧
    ∃ C : ℝ, 0 ≤ C ∧
      |PolynomialAtomRow.preparation.stateRootError 1 univ 3 actual reference 1| ≤ C * 168 := by
  constructor
  · norm_num [prefixErrorBudget]
  · obtain ⟨C, hC, hbound⟩ := PolynomialAtomRow.preparation.exists_iterate_root_bound
      (θ := 1) (by norm_num)
    refine ⟨C, hC, ?_⟩
    have h := hbound univ (fun _ => 3) (dyadicFloor (1 / 20000) 1) (fun _ => 0)
      truth raw 0 0 (1 / 20000) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      1 (by norm_num) (by intros; norm_num)
      (by
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        rw [floor_zero]
        norm_num)
      (fun y _ => by fin_cases y <;> norm_num [truth])
      (fun y _ => by fin_cases y <;> norm_num [truth]) (by intros; norm_num)
      (fun _ => 2) (by intros; norm_num)
      (fun _ _ _ _ => (clippedError_le_one _ _ _).trans (by norm_num)) 1 (mem_univ 1)
    have hactual : iterate univ (fun _ => 3) (fun _ => 3) (dyadicFloor (1 / 20000) 1)
        (fun _ => 0) ⟨0, raw⟩ 1 = actual := by
      simp [actual, iterate_succ, advance, increments, initial]
    have href : iterate univ (fun _ => 3) (fun _ => 3) (dyadicFloor (1 / 20000) 1)
        (fun _ => 0) ⟨0, truth⟩ 1 = reference := by
      simp [reference, stationaryContinuation, stationaryState, initial]
    simpa only [add_zero, hactual, href,
      show prefixErrorBudget (fun _ => (2 : ℝ)) 1 = 168 by norm_num [prefixErrorBudget]] using h

private noncomputable def highTruth : Fin 2 → Fin 2 → ℝ := ![![1000, 0], ![0, 0]]

private noncomputable def highRaw : Fin 2 → Fin 2 → ℝ :=
  ![![1000 + 1 / 100000000, -1 / 100000000], ![0, 0]]

private noncomputable def highRun : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 1) (fun _ => 1 / 1000000000)
    (fun _ => 0) ⟨0, highRaw⟩

private noncomputable def highReference : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 1) (fun _ => 1 / 1000000000)
    (fun _ => 0) ⟨0, highTruth⟩

private theorem high_rank (m : ℕ) :
    1 ≤ firstRank univ 1 (highRun m).defaultValue (highRun m).row := by
  apply le_iterate_firstRank_of_raw_large (D := {0}) (by norm_num) (by norm_num)
    (subset_univ _) (by norm_num) m
  intro i _ y hy
  have hy0 : y = 0 := by simpa using hy
  subst y
  norm_num [uncompressedRow, highRaw]

private theorem high_default : (highRun 1).defaultValue = 3 / 1000000000 := by
  norm_num [highRun, iterate_succ, advance, newDefault, threshold, kthLargest, highRaw,
    entrySize, Fin.univ_succ, filter_insert, filter_singleton]

-- The ≥K branch is nonempty. Here the default is still below the gate: the retained first
-- rank closes every concrete output, while a perturbed signed high entry is preserved.
example : 1 ≤ #{y : Fin 2 | (32 : ℝ) < highTruth y 0} ∧
    (highRun 1).defaultValue < 1 ∧ (highRun 1).row 0 = highRaw 0 ∧
    ∀ (kind : PolynomialAtomRow) (y : Fin 2),
      kind.eval 1 ((highRun 1).row y 0)
        (firstRank univ 1 (highRun 1).defaultValue (highRun 1).row) = 0 := by
  have hs : ({y | (32 : ℝ) < highTruth y 0} : Finset (Fin 2)) = {0} := by
    ext y
    fin_cases y <;> norm_num [highTruth]
  have hd : (highRun 1).defaultValue < 1 := by rw [high_default]; norm_num
  refine ⟨by rw [hs]; norm_num, hd, ?_, ?_⟩
  · have hp := gate_le_default_or_iterate_row_eq (s := (univ : Finset (Fin 2)))
      (n := fun _ => 2) (K := fun _ => 1) (ρ := fun _ => 1 / 1000000000)
      (Δ := fun _ => 0) (a := ⟨0, highRaw⟩) (D := {0}) (G := 1) 1 (by
        intro i _ y hy
        have hy0 : y = 0 := by simpa using hy
        subst y
        norm_num [uncompressedRow, highRaw])
    rcases hp with hz | hw
    · exact False.elim (not_le.mpr hd hz)
    · have h := hw 0 (by simp)
      have hp : uncompressedRow (fun _ => 0) highRaw 1 = highRaw := by
        funext y ν
        simp [uncompressedRow]
      rw [hp] at h
      exact h
  · intro kind y
    apply kind.eval_eq_zero_of_rank_ge (by norm_num)
    have hg : kind.gateThreshold (1 : ℝ) ≤ 1 := by
      cases kind <;> norm_num [PolynomialAtomRow.gateThreshold]
    exact hg.trans (high_rank 1)

-- Apply the complete local endpoint in that large-count branch with a small, nonzero error.
example (kind : PolynomialAtomRow) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin 2,
    |kind.stateRootError 1 univ 1 (highRun 1) (highReference 1) y| ≤ C * (21 / 2500000) := by
  obtain ⟨C, hC, hbound⟩ := kind.exists_iterate_root_bound (θ := 1) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro y
  have h := hbound univ (fun _ => 2) (fun _ => 1 / 1000000000) (fun _ => 0)
    highTruth highRaw 0 0 (1 / 20000) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 (by norm_num)
    (by intros; norm_num) (by intros; norm_num)
    (fun y _ => by fin_cases y <;> norm_num [highTruth])
    (fun y _ => by fin_cases y <;> norm_num [highTruth]) (by intros; norm_num)
    (fun _ => 1 / 10000000) (by intros; norm_num) (by
      intro i _ y _
      have hp : uncompressedRow (fun _ => 0) highRaw i = highRaw := by
        funext y ν
        simp [uncompressedRow]
      rw [hp]
      fin_cases y <;> norm_num [highTruth, highRaw, clippedError]) y (mem_univ y)
  simpa only [add_zero, highRun, highReference,
    show prefixErrorBudget (fun _ => (1 / 10000000 : ℝ)) 1 = 21 / 2500000 by
      norm_num [prefixErrorBudget]] using h

private noncomputable def closingInitial : State (Fin 1) := ⟨0, ![![1000, 0]]⟩

private noncomputable def closingIncrements (i : ℕ) : Fin 1 → Fin 2 → ℝ :=
  if i = 1 then ![![-10000, 0]] else 0

private noncomputable def closingRun : ℕ → State (Fin 1) :=
  iterate univ (fun _ => 1) (fun _ => 1) (fun _ => 1 / 1000000000)
    closingIncrements closingInitial

private theorem closing_default : (closingRun 1).defaultValue = 1000 := by
  norm_num [closingRun, iterate_succ, advance, closingIncrements, closingInitial, newDefault,
    threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]

-- Once a threshold raises the default above the gate, a later large negative raw increment
-- cannot reopen it. The raw lower-bound hypothesis itself is false at this later prefix.
example : uncompressedRow closingIncrements closingInitial.row 2 0 0 < 0 ∧
    1000 ≤ (closingRun 2).defaultValue ∧
    ∀ (kind : PolynomialAtomRow), kind.eval 1 ((closingRun 2).row 0 0)
      (firstRank univ 1 (closingRun 2).defaultValue (closingRun 2).row) = 0 := by
  have hmono : (closingRun 1).defaultValue ≤ (closingRun 2).defaultValue :=
    iterate_defaultValue_monotone (by norm_num : 1 ≤ 2)
  rw [closing_default] at hmono
  refine ⟨?_, hmono, ?_⟩
  · norm_num [uncompressedRow, closingIncrements, closingInitial, sum_range_succ]
  · intro kind
    apply kind.eval_eq_zero_of_rank_ge (by norm_num)
    have hg : kind.gateThreshold (1 : ℝ) ≤ 1000 := by
      cases kind <;> norm_num [PolynomialAtomRow.gateThreshold]
    exact (hg.trans hmono).trans default_le_firstRank

end ComplexityTests.PolynomialAtomRelative
