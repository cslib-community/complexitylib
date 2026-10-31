/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Analysis.RowCompression.OverflowNoise
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Tests for aggregation of actual first-overflow noise

The first group compresses a zero row to default one. On the false Boolean draw, the next
group adds `(4, -2)` and first overflows at index one. Its selected weighted noise tail is
`2 * 5 + 1 * 11 = 21`, while the full weighted sum is `4 * 7 + 2 * 5 + 1 * 11 = 49`.
Noise vanishes on the other draw, so it is correlated with the overflow event. The actual
fourth-moment comparison is checked with the existing vertex norm and positive normalization.
-/

namespace ComplexityTests.RowCompressionOverflowNoise

open Finset Cslib Cslib.RowCompression
open scoped BigOperators

private def initial : State (Fin 1) := { defaultValue := 0, row := 0 }

private def increments (σ : Bool) (i : ℕ) (_ : Fin 1) : Fin 2 → ℝ :=
  if σ = false ∧ i = 1 then ![4, -2] else 0

private def weight (i : ℕ) : ℝ := if i = 0 then 4 else if i = 1 then 2 else 1

private def noise (i : ℕ) (σ : Bool) : ℝ :=
  if σ = false then if i = 0 then 7 else if i = 1 then 5 else 11 else 0

private theorem first_overflow :
    IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments false) initial 1 := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num [stepThreshold, inputRow, iterate, initial, increments,
      threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · norm_num [stepThreshold, inputRow, iterate, advance, initial, increments,
      newDefault, threshold, kthLargest, entrySize, update, updateEntry, radius, defaultEntry,
      Fin.univ_succ, filter_insert, filter_singleton]

private theorem first_overflow_iff (j : ℕ) :
    IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments false) initial j ↔ j = 1 := by
  constructor
  · exact fun hj => hj.unique first_overflow
  · rintro rfl
    exact first_overflow

-- The first group changes the stored row, before the nonzero overflow increment arrives.
example : (iterate univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (increments false) initial 1).defaultValue = 1 := by
  norm_num [iterate, advance, initial, increments, newDefault, threshold, kthLargest,
    entrySize, Fin.univ_succ, filter_insert, filter_singleton]

-- The event and noise share the same Boolean draw; no independence hypothesis is available.
example : noise 1 false = 5 ∧ noise 1 true = 0 ∧
    ¬ IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 1 := by
  constructor
  · norm_num [noise]
  constructor
  · norm_num [noise]
  · intro h
    have hlt := h.2
    norm_num [stepThreshold, inputRow, iterate, advance, initial, increments,
      newDefault, threshold, kthLargest, entrySize, update, updateEntry, radius, defaultEntry,
      Fin.univ_succ, filter_insert, filter_singleton] at hlt

private theorem selected_tail :
    firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments false) initial 3 weight (fun i => noise i false) = 21 := by
  unfold firstOverflowNoiseTail
  simp only [first_overflow_iff]
  norm_num [sum_range_succ, weight, noise, Finset.sum_Ico_succ_top]

private theorem full_sum : (∑ i ∈ range 3, weight i * noise i false) = 49 := by
  norm_num [sum_range_succ, weight, noise]

-- The actual-run theorem gives a strict, nonzero instance, retaining the same full sum once.
example : firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (increments false) initial 3 weight (fun i => noise i false) ≤
      ∑ i ∈ range 3, weight i * noise i false := by
  apply firstOverflowNoiseTail_le
  · intro i _
    simp only [weight]
    split_ifs <;> norm_num
  · intro i _
    simp only [noise]
    split_ifs <;> norm_num

example : 0 < firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (increments false) initial 3 weight (fun i => noise i false) ∧
    firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments false) initial 3 weight (fun i => noise i false) <
        ∑ i ∈ range 3, weight i * noise i false := by
  rw [selected_tail, full_sum]
  norm_num

-- The moment theorem permits the increments, event and noise to depend on the same seed.
example : vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Fin 1) => True)
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 3 weight (fun i => noise i σ)) ≤
    vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Fin 1) => True)
      (fun σ _ => ∑ i ∈ range 3, weight i * noise i σ) := by
  apply vertexNormPow_firstOverflowNoiseTail_le (fun _ _ => univ)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun σ _ => increments σ)
    (fun _ _ => initial) 3 (by norm_num)
  · intro i _
    simp only [weight]
    split_ifs <;> norm_num
  · intro i _ σ _ _
    simp only [noise]
    split_ifs <;> norm_num

example : vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Fin 1) => True)
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 3 weight (fun i => noise i σ)) = 194481 / 2 := by
  have hz : firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 3 weight (fun i => noise i true) = 0 := by
    simp [firstOverflowNoiseTail, noise]
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  dsimp only
  rw [selected_tail, hz]
  norm_num

example : vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Fin 1) => True)
    (fun σ _ => ∑ i ∈ range 3, weight i * noise i σ) = 5764801 / 2 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [Fin.sum_univ_one, sum_range_succ, weight, noise]

-- Without uniqueness, the same summands can be counted repeatedly in several tails.
example : (∑ j ∈ range 3, ∑ _i ∈ Ico j 3, (1 : ℝ)) > ∑ _i ∈ range 3, (1 : ℝ) := by
  norm_num [sum_range_succ]

end ComplexityTests.RowCompressionOverflowNoise
