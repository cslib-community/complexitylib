/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.SentinelRelative
import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Clipped-prefix budgets for an actual sentinel comparison

The true first row is `(1000, 0)`, with one entry above the fixed threshold `1`. A local
two-group calculation starts from the already-added input of its first group. Its first
increment is zero; its second increment changes a large first entry and signed second entries.
The first actual threshold is `10⁻⁷`, strictly above the floor `10⁻⁹`. Compression raises the
default and erases the low entry's negative second channel. Every raw prefix nevertheless has
clipped error at most `10⁻⁶`.

The theorem derives coupling to the common sentinel `32`, including exact defaults and padded
ranks and the original marked channels' nonconstant raw evolution. A zero-initial global run
has the same two-group result, while its preceding raw prefix has large error. This checks why
the local comparison starts after adding the first overflow group's input.
-/

namespace ComplexityTests.RowCompressionSentinelRelative

open Finset Cslib.RowCompression
open scoped BigOperators

private noncomputable def truth : Fin 2 → Fin 2 → ℝ := ![![1000, 0], ![0, 0]]

private noncomputable def raw₀ : Fin 2 → Fin 2 → ℝ :=
  ![![1000, -1 / 4000000], ![1 / 10000000, -1 / 20000000]]

private noncomputable def later : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 10000, 1 / 8000000], ![-1 / 20000000, 1 / 40000000]]

private noncomputable def increments (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if i = 1 then later else 0

private noncomputable def initial : State (Fin 2) := ⟨0, raw₀⟩

private noncomputable def original : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 2) (fun _ => 1 / 1000000000) increments initial

private noncomputable def modified : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 2) (fun _ => 1 / 1000000000)
    (fun i => sentinelFirst {0} 0 (increments i)) (sentinelState {0} 32 initial)

private theorem heavy_set : ({y | (1 : ℝ) < truth y 0} : Finset (Fin 2)) = {0} := by
  ext y
  fin_cases y <;> norm_num [truth]

private theorem marked_set : ({y | (32 : ℝ) < truth y 0} : Finset (Fin 2)) = {0} := by
  ext y
  fin_cases y <;> norm_num [truth]

private theorem prefix_error (i : ℕ) (hi : i ≤ 2) (y : Fin 2) :
    clippedError (truth y 0) (truth y 1) (uncompressedRow increments raw₀ i y) ≤
      1 / 1000000 := by
  interval_cases i <;> fin_cases y <;>
    norm_num [clippedError, uncompressedRow, increments, raw₀, later, truth, sum_range_succ]

-- This is the exact finite weighted budget used by the theorem, including the initial error.
example : (1 + 16 * ((1 : ℝ) + 1)) *
    (28 ^ 2 * (1 / 1000000) + ∑ i ∈ range 2,
      28 ^ (2 - i) * (1 / 1000000 + 1 / 1000000)) = 9933 / 125000 := by
  norm_num [sum_range_succ]

private theorem coupling (j : ℕ) (hj : j ≤ 2) :
    modified j = sentinelState {0} 32 (original j) ∧
      (∀ y ∈ ({0} : Finset (Fin 2)), (original j).row y =
        uncompressedRow increments initial.row j y) ∧
      (0 < j → firstRank univ 2 (original j).defaultValue (original j).row =
        firstRank univ 2 (modified j).defaultValue (modified j).row ∧
          firstRank univ 2 (modified j).defaultValue (modified j).row ≤ 3) := by
  have h := iterate_sentinelState_of_clippedError_le (s := (univ : Finset (Fin 2)))
    (n := fun _ => 2) (K := 2) (ρ := fun _ => 1 / 1000000000)
    (η := 1) (L₀ := 1) (z := 0) (truth := truth) (raw₀ := raw₀)
    (loss := 0) (Δ := increments) (ε := fun _ => 1 / 1000000) 2
    (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by intros; exact le_rfl) (by intros; norm_num)
    (by intro y _; fin_cases y <;> norm_num [truth])
    (by intro y _; fin_cases y <;> norm_num [truth])
    (by intros; norm_num)
    (by rw [heavy_set]; norm_num)
    (by intros; norm_num) (by intro i hi y _; exact prefix_error i hi y)
    (by norm_num [sum_range_succ]) j hj
  norm_num only [show (16 : ℝ) * (1 + 1) = 32 by norm_num,
    show (2 : ℝ) * 1 + 1 = 3 by norm_num, marked_set, add_zero] at h
  exact h

private theorem rank_two (v : Fin 2 → ℝ)
    (h0 : v 0 = 1000) (h1 : v 1 = 1 / 10000000) :
    kthLargest 2 univ v = 1 / 10000000 := by
  apply le_antisymm
  · refine not_lt.mp fun hlt => ?_
    have hc := (lt_kthLargest_iff (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 1 / 10000000)).mp hlt
    have hs : ({y | (1 / 10000000 : ℝ) < v y} : Finset (Fin 2)) = {0} := by
      ext y
      fin_cases y <;> norm_num [h0, h1]
    rw [hs] at hc
    norm_num at hc
  · apply (le_kthLargest_iff (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10000000)).mpr
    have hs : ({y | (1 / 10000000 : ℝ) ≤ v y} : Finset (Fin 2)) = univ := by
      ext y
      fin_cases y <;> norm_num [h0, h1]
    rw [hs]
    norm_num

private theorem first_threshold :
    threshold univ 2 (1 / 1000000000) 0 raw₀ = 1 / 10000000 := by
  unfold threshold
  rw [rank_two (fun y => entrySize (raw₀ y)) (by norm_num [raw₀, entrySize])
    (by norm_num [raw₀, entrySize])]
  norm_num

private theorem first_default :
    newDefault univ 2 2 (1 / 1000000000) 0 raw₀ = 1 / 10000000 := by
  unfold newDefault
  rw [first_threshold, rank_two (fun y => raw₀ y 0) (by norm_num [raw₀])
    (by norm_num [raw₀])]
  norm_num

private theorem first_state : original 1 =
    ⟨1 / 10000000, ![![1000, -1 / 4000000], ![1 / 10000000, 0]]⟩ := by
  change advance univ 2 2 (1 / 1000000000) (increments 0) initial = _
  simp only [advance, initial, increments, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, add_zero]
  rw [first_default]
  congr 1
  unfold update
  rw [first_threshold, first_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, radius, entrySize, defaultEntry, raw₀]

-- There is a genuine first overflow, nonzero default, and erased negative second channel.
example : IsFirstOverflow univ (fun _ => 2) (fun _ => 2) (fun _ => 1 / 1000000000)
      increments initial 0 ∧
    (original 1).defaultValue = 1 / 10000000 ∧
    uncompressedRow increments initial.row 1 1 1 = -1 / 20000000 ∧
    (original 1).row 1 1 = 0 := by
  refine ⟨⟨by simp, ?_⟩, ?_⟩
  · simpa only [stepThreshold, inputRow, iterate_zero, initial, increments,
      show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, add_zero, first_threshold] using
      (show (1 / 1000000000 : ℝ) < 1 / 10000000 by norm_num)
  · rw [first_state]
    norm_num [uncompressedRow, initial, increments, raw₀]

-- Original marked first and signed second channels evolve; only the modified first is fixed.
example : (original 2).row 0 0 = 10000001 / 10000 ∧
    (original 2).row 0 1 = -1 / 8000000 ∧
    (modified 2).row 0 0 = 32 ∧ (modified 2).row 0 1 = -1 / 8000000 ∧
    (modified 2).defaultValue = (original 2).defaultValue ∧
    firstRank univ 2 (original 2).defaultValue (original 2).row =
      firstRank univ 2 (modified 2).defaultValue (modified 2).row := by
  obtain ⟨heq, hraw, hq⟩ := coupling 2 le_rfl
  have hraw0 := hraw 0 (by simp)
  rw [heq]
  simp only [sentinelState, sentinelFirst_zero_of_mem (by simp : (0 : Fin 2) ∈ ({0} : Finset _)),
    sentinelFirst_one, hraw0]
  norm_num [uncompressedRow, initial, increments, raw₀, later, sum_range_succ]
  simpa only [heq, sentinelState] using (hq (by norm_num)).1

private noncomputable def globalIncrements (i : ℕ) : Fin 2 → Fin 2 → ℝ :=
  if i = 0 then raw₀ else increments i

private noncomputable def globalRun : ℕ → State (Fin 2) :=
  iterate univ (fun _ => 2) (fun _ => 2) (fun _ => 1 / 1000000000)
    globalIncrements ⟨0, 0⟩

-- Start the comparison after adding the overflow input: the local first increment is zero.
example : globalRun 2 = original 2 ∧ increments 0 = 0 ∧
    uncompressedRow globalIncrements 0 1 = raw₀ ∧
    1 / 1000000 < clippedError (truth 0 0) (truth 0 1)
      (uncompressedRow globalIncrements 0 0 0) := by
  have hfirst : globalRun 1 = original 1 := by
    simp only [globalRun, original, iterate_succ, iterate_zero, advance, initial,
      globalIncrements, increments, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, zero_add, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change advance univ 2 2 (1 / 1000000000) (globalIncrements 1) (globalRun 1) =
      advance univ 2 2 (1 / 1000000000) (increments 1) (original 1)
    rw [hfirst]
    rfl
  · simp [increments]
  · funext y ν
    simp [uncompressedRow, globalIncrements]
  · norm_num [uncompressedRow, clippedError, truth]

-- The small-heavy-set branch is a real restriction, and unclipping needs a strict bound below one.
example : ¬ #{y : Fin 2 | (1 : ℝ) < (![1000, 1000] : Fin 2 → ℝ) y} < 2 := by
  norm_num [Fin.univ_succ, filter_insert, filter_singleton]

example : clippedError 0 0 ![2, 0] = 1 ∧ ¬ |(2 : ℝ) - 0| ≤ (1 + 0) * 1 := by
  norm_num [clippedError]

end ComplexityTests.RowCompressionSentinelRelative
