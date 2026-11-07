/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.SentinelIteration
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Two actual sentinel compression steps

The marked first coordinate receives increments `-5,+7`; its second coordinate receives
`+2,-3`. The modified calculation clears only those first increments. Its two input rank and
threshold ceilings are proved by evaluating its actual intermediate states. The coupling theorem
then recovers the original marked raw prefix, common defaults, and exact final rank equality.
An unmarked endpoint has raw first prefix `-2` but compressed value `2`, so the calculation is
not globally identical to its uncompressed prefixes.
-/

namespace ComplexityTests.RowCompressionSentinelIteration

open Finset Cslib.RowCompression

private noncomputable def initial : State (Fin 4) :=
  { defaultValue := 1 / 2, row := ![![1000000, -17], ![4, 0], ![2, -1], ![-1, 1]] }

private def increments (i : ℕ) : Fin 4 → Fin 2 → ℝ :=
  if i = 0 then ![![-5, 2], ![0, 0], ![0, 0], ![0, 0]]
  else if i = 1 then ![![7, -3], ![0, 0], ![0, 0], ![-1, 1]] else 0

private noncomputable def cleared (i : ℕ) : Fin 4 → Fin 2 → ℝ :=
  sentinelFirst {0} 0 (increments i)

private noncomputable def modifiedStart : State (Fin 4) := sentinelState {0} 100 initial

private noncomputable def originalRun : ℕ → State (Fin 4) :=
  iterate univ (fun _ => 3) (fun _ => 3) (fun _ => 1) increments initial

private noncomputable def modifiedRun : ℕ → State (Fin 4) :=
  iterate univ (fun _ => 3) (fun _ => 3) (fun _ => 1) cleared modifiedStart

private noncomputable def modifiedInput : ℕ → Fin 4 → Fin 2 → ℝ :=
  inputRow univ (fun _ => 3) (fun _ => 3) (fun _ => 1) cleared modifiedStart

private def inputZero : Fin 4 → Fin 2 → ℝ := ![![100, -15], ![4, 0], ![2, -1], ![-1, 1]]

private def inputOne : Fin 4 → Fin 2 → ℝ := ![![100, -18], ![2, 0], ![2, 0], ![1, 1]]

private theorem modified_input_zero : modifiedInput 0 = inputZero := by
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [modifiedInput, inputRow, modifiedStart, sentinelState, initial, cleared,
      sentinelFirst, increments, inputZero]

private theorem rank_zero : firstRank univ 3 (1 / 2) inputZero = 2 := by
  norm_num [firstRank, kthLargest, inputZero, Fin.univ_succ, filter_insert, filter_singleton]

private theorem threshold_zero : threshold univ 3 1 (1 / 2) inputZero = 2 := by
  norm_num [threshold, entrySize, kthLargest, inputZero, Fin.univ_succ,
    filter_insert, filter_singleton]

private theorem default_zero : newDefault univ 3 3 1 (1 / 2) inputZero = 2 := by
  change max (threshold univ 3 1 (1 / 2) inputZero)
    (min (firstRank univ 3 (1 / 2) inputZero) (3 * threshold univ 3 1 (1 / 2) inputZero)) = 2
  rw [threshold_zero, rank_zero]
  norm_num

private theorem modified_one : modifiedRun 1 =
    { defaultValue := 2, row := ![![100, -15], ![2, 0], ![2, 0], ![2, 0]] } := by
  have hin : modifiedStart.row + cleared 0 = inputZero := modified_input_zero
  change advance univ 3 3 1 (cleared 0) modifiedStart = _
  unfold advance
  rw [hin]
  change State.mk (newDefault univ 3 3 1 (1 / 2) inputZero)
    (update univ 3 3 1 (1 / 2) inputZero) = _
  rw [default_zero]
  congr 1
  unfold update
  rw [threshold_zero, default_zero]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, inputZero]

private theorem modified_input_one : modifiedInput 1 = inputOne := by
  change (modifiedRun 1).row + cleared 1 = inputOne
  rw [modified_one]
  funext y ν
  fin_cases y <;> fin_cases ν <;> norm_num [cleared, sentinelFirst, increments, inputOne]

private theorem rank_one : firstRank univ 3 2 inputOne = 2 := by
  norm_num [firstRank, kthLargest, inputOne, Fin.univ_succ, filter_insert, filter_singleton]

private theorem threshold_one : threshold univ 3 1 2 inputOne = 2 := by
  norm_num [threshold, entrySize, kthLargest, inputOne, Fin.univ_succ,
    filter_insert, filter_singleton]

private theorem default_one : newDefault univ 3 3 1 2 inputOne = 2 := by
  change max (threshold univ 3 1 2 inputOne)
    (min (firstRank univ 3 2 inputOne) (3 * threshold univ 3 1 2 inputOne)) = 2
  rw [threshold_one, rank_one]
  norm_num

private theorem modified_two : modifiedRun 2 =
    { defaultValue := 2, row := ![![100, -18], ![2, 0], ![2, 0], ![2, 0]] } := by
  have hin : (modifiedRun 1).row + cleared 1 = inputOne := modified_input_one
  change advance univ 3 3 1 (cleared 1) (modifiedRun 1) = _
  unfold advance
  rw [hin, modified_one]
  rw [default_one]
  congr 1
  unfold update
  rw [threshold_one, default_one]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, inputOne]

private theorem modified_ceilings (i : ℕ) (hi : i < 2) :
    firstRank univ 3 (modifiedRun i).defaultValue (modifiedInput i) ≤ 2 ∧
      threshold univ 3 1 (modifiedRun i).defaultValue (modifiedInput i) ≤ 2 := by
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · change firstRank univ 3 (1 / 2) (modifiedInput 0) ≤ 2 ∧
      threshold univ 3 1 (1 / 2) (modifiedInput 0) ≤ 2
    rw [modified_input_zero]
    exact ⟨rank_zero.le, threshold_zero.le⟩
  · rw [modified_input_one, modified_one]
    exact ⟨rank_one.le, threshold_one.le⟩

private theorem coupling (j : ℕ) (hj : j ≤ 2) :
    modifiedRun j = sentinelState {0} 100 (originalRun j) ∧
      (∀ y ∈ ({0} : Finset (Fin 4)),
        (originalRun j).row y = uncompressedRow increments initial.row j y) ∧
      (0 < j → firstRank univ 3 (originalRun j).defaultValue (originalRun j).row =
        firstRank univ 3 (modifiedRun j).defaultValue (modifiedRun j).row ∧
          firstRank univ 3 (modifiedRun j).defaultValue (modifiedRun j).row ≤ 2) := by
  apply iterate_sentinelState_of_sum_abs_lt (s := univ) (marked := {0}) (n := fun _ => 3)
    (K := 3) (ρ := fun _ => 1) (Δ := increments) (a := initial) (R := 2) (L := 100)
    2 (subset_univ _) (by norm_num) (by intros; norm_num) (by norm_num) (by norm_num)
    _ (fun i hi => (modified_ceilings i hi).1) (fun i hi => (modified_ceilings i hi).2) j hj
  intro y hy
  have hy0 : y = 0 := mem_singleton.mp hy
  subst y
  norm_num [sum_range_succ, increments, initial]

-- Only the marked first increments are removed; nonzero signed second increments survive.
example : increments 0 0 0 = -5 ∧ increments 1 0 0 = 7 ∧
    cleared 0 0 0 = 0 ∧ cleared 1 0 0 = 0 ∧ cleared 0 0 1 = 2 ∧ cleared 1 0 1 = -3 := by
  norm_num [increments, cleared, sentinelFirst]

-- The original marked entry follows both raw prefixes, derived from the actual coupling theorem.
example : (originalRun 2).row 0 = ![1000002, -18] := by
  rw [(coupling 2 (by norm_num)).2.1 0 (mem_singleton_self 0)]
  funext ν
  fin_cases ν <;> norm_num [uncompressedRow, initial, increments, sum_range_succ]

-- The defaults genuinely rise from 1/2 to 2 and agree in the two actual calculations.
example : initial.defaultValue = 1 / 2 ∧
    (originalRun 2).defaultValue = 2 ∧ (modifiedRun 2).defaultValue = 2 := by
  have heq := congrArg State.defaultValue (coupling 2 (by norm_num)).1
  rw [modified_two] at heq ⊢
  exact ⟨rfl, heq.symm, rfl⟩

-- Unmarked first values need not follow raw prefixes; actual compression still takes place.
example : (originalRun 2).row 3 0 = 2 ∧
    uncompressedRow increments initial.row 2 3 0 = -2 := by
  have h := congrArg (fun a : State (Fin 4) => a.row 3 0) (coupling 2 (by norm_num)).1
  rw [modified_two] at h
  have hfirst : (originalRun 2).row 3 0 = 2 := by
    norm_num [sentinelState, sentinelFirst] at h
    exact h.symm
  exact ⟨hfirst, by norm_num [uncompressedRow, initial, increments, sum_range_succ]⟩

-- The post-update rank helper is consumed by the actual final-rank conclusion.
example : firstRank univ 3 (originalRun 2).defaultValue (originalRun 2).row =
    firstRank univ 3 (modifiedRun 2).defaultValue (modifiedRun 2).row ∧
      firstRank univ 3 (modifiedRun 2).defaultValue (modifiedRun 2).row ≤ 2 :=
  (coupling 2 (by norm_num)).2.2 (by norm_num)

end ComplexityTests.RowCompressionSentinelIteration
