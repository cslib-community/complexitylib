/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Analysis.RowCompression.OverflowBudget
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Tests for correlated moment budgets and actual overflow tails

The active source, both noise arrays and the overflow event share one Boolean draw.
At normalization `N = 1`, `u = 1/2`, the individual budgets are attained, so the
weighted fourth-moment estimate is sharp. Values outside the retained source can be negative.
An actual compression run then yields the strict tail comparison `21^4 ≤ 49^4`.
-/

namespace ComplexityTests.OverflowMomentBudget

open Finset Cslib Cslib.RowCompression
open scoped BigOperators

private def active (σ : Bool) (_ : Fin 1) : Prop := σ = true

private instance (σ : Bool) (x : Fin 1) : Decidable (active σ x) :=
  inferInstanceAs (Decidable (σ = true))

private def signal (i σ : Bool) (_ : Fin 1) : ℝ :=
  if σ then if i then 2 else 1 else -100

private def weight (i : Bool) : ℝ := if i then 5 else 3

private def budget (i : Bool) : ℝ := if i then 2 else 1

private theorem signal_moment (i : Bool) :
    vertexNormPow 4 1 (1 / 2) active (signal i) = budget i ^ 4 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  cases i <;> norm_num [active, signal, budget]

-- The common draw gives no independence, and the weighted Minkowski budget is attained.
example : vertexNormPow 4 1 (1 / 2) active
    (fun σ x => ∑ i : Bool, weight i * signal i σ x) = 28561 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [active, signal, weight, Fintype.sum_bool]

example : vertexNormPow 4 1 (1 / 2) active
    (fun σ x => ∑ i : Bool, weight i * signal i σ x) ≤ 28561 := by
  have h := vertexNormPow_sum_le_pow_sum (X := active) (N := 1) (u := 1 / 2)
    (by decide : 4 ≠ 0) (by norm_num) (univ : Finset Bool) signal weight budget
    (by intro i _; cases i <;> norm_num [weight])
    (by intro i _; cases i <;> norm_num [budget])
    (fun i _ => (signal_moment i).le)
  norm_num [weight, budget, Fintype.sum_bool] at h ⊢
  exact h

-- Scalars of either sign factor out with absolute value.
example : vertexNormPow 4 1 (1 / 2) active (fun σ x => -3 * signal false σ x) = 81 := by
  rw [vertexNormPow_const_mul, signal_moment]
  norm_num [budget]

-- The positive-moment sum theorem includes empty index sets and zero normalization.
example : vertexNormPow 4 1 (1 / 2) active
    (fun σ x => ∑ i ∈ (∅ : Finset Bool), signal i σ x) = 0 := by
  simp [vertexNormPow]

example : vertexNormPow 1 0 1 active
    (fun σ x => ∑ i : Bool, signal i σ x) ≤ (0 : ℝ) := by
  have h := vertexNormPow_sum_le_pow_sum (X := active) (N := 0) (u := 1)
    (by decide : 1 ≠ 0) (by norm_num) (univ : Finset Bool) signal (fun _ => 1) (fun _ => 0)
    (by intros; norm_num) (by intros; norm_num)
    (by intros; simp [vertexNormPow])
  simpa using h

example : vertexNormPow 4 1 1 (fun (_ : Empty) (_ : Fin 1) => True)
    (fun σ _ => nomatch σ) = 0 := by
  simp [vertexNormPow]

private def initial : State (Fin 1) := { defaultValue := 0, row := 0 }

private def increments (σ : Bool) (i : ℕ) (_ : Fin 1) : Fin 2 → ℝ :=
  if σ = true ∧ i = 1 then ![4, -2] else 0

private def noiseBudget (i : ℕ) : ℝ := if i = 0 then 4 else 3

private def noise (i : ℕ) (σ : Bool) (_ : Fin 1) : ℝ :=
  if σ then noiseBudget i else -100

private theorem first_overflow :
    IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 1 := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num [stepThreshold, inputRow, iterate, initial, increments,
      threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]
  · norm_num [stepThreshold, inputRow, iterate, advance, initial, increments,
      newDefault, threshold, kthLargest, entrySize, update, updateEntry, radius, defaultEntry,
      Fin.univ_succ, filter_insert, filter_singleton]

private theorem selected_tail :
    firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 2 (fun _ => 7) (fun i => noise i true 0) = 21 := by
  have hevent (j : ℕ) :
      IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
        (increments true) initial j ↔ j = 1 :=
    ⟨fun hj => hj.unique first_overflow, fun h => h ▸ first_overflow⟩
  unfold firstOverflowNoiseTail
  simp only [hevent]
  norm_num [sum_range_succ, noise, noiseBudget, Finset.sum_Ico_succ_top]

private theorem noise_moment (i : ℕ) :
    vertexNormPow 4 1 (1 / 2) active (noise i) = noiseBudget i ^ 4 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  by_cases hi : i = 0 <;> norm_num [active, noise, noiseBudget, hi]

-- This consumes the budget theorem for the actual signed-increment compression run.
example : vertexNormPow 4 1 (1 / 2) active
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 2 (fun _ => 7) (fun i => noise i σ 0)) ≤ 5764801 := by
  have h := vertexNormPow_firstOverflowNoiseTail_le_pow_sum
    (fun (_ : Bool) (_ : Fin 1) => (univ : Finset (Fin 1)))
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun σ _ => increments σ)
    (fun _ _ => initial) 2 (by decide : 4 ≠ 0) (N := 1) (u := 1 / 2) (by norm_num)
    active (fun _ => 7) noiseBudget noise
    (by intros; norm_num)
    (by intro i _; simp only [noiseBudget]; split_ifs <;> norm_num)
    (by intro i _ σ x hx; change σ = true at hx; subst σ
        simp only [noise, ↓reduceIte, noiseBudget]; split_ifs <;> norm_num)
    (fun i _ => (noise_moment i).le)
  norm_num [sum_range_succ, noiseBudget] at h
  simpa [noise] using h

example : vertexNormPow 4 1 (1 / 2) active
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 2 (fun _ => 7) (fun i => noise i σ 0)) = 194481 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  dsimp only
  rw [selected_tail]
  norm_num [active]

end ComplexityTests.OverflowMomentBudget
