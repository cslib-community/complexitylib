/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.NoiseDecay
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Uniform dyadic noise budgets on an actual compression run

The concrete absolute propagation constant 28 and decay 1/64 have a uniform budget 7/9.
A common Boolean draw controls retention, noise and an actual first overflow at group zero.
For two groups the exact weighted tail is 161/256, and its normalized fourth moment is
(161/256)^4. Inactive noise can be negative. A slower decay example fails to pay for even
one group, so the numerical decay condition has substantive content.
-/

namespace ComplexityTests.OverflowNoiseDecay

open Finset Cslib Cslib.RowCompression
open scoped BigOperators

example (m : ℕ) :
    ∑ i ∈ range m, (28 : ℝ) ^ (m - i) * (1 / 64) ^ dyadicSlack m i ≤ 7 / 9 := by
  have h := sum_propagation_mul_dyadic_decay_le (C := 28) (q := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num at h ⊢
  exact h

example : ∑ i ∈ range 2, (28 : ℝ) ^ (2 - i) * (1 / 64) ^ dyadicSlack 2 i =
    161 / 256 := by norm_num [sum_range_succ, dyadicSlack]

-- The empty horizon and zero decay incur no cost.
example : ∑ i ∈ range 0, (28 : ℝ) ^ (0 - i) * (1 / 64) ^ dyadicSlack 0 i = 0 := by simp

example (m : ℕ) :
    ∑ i ∈ range m, (28 : ℝ) ^ (m - i) * 0 ^ dyadicSlack m i = 0 := by
  apply sum_eq_zero
  intro i _
  rw [zero_pow (dyadicSlack_pos m i).ne']
  exact mul_zero _

-- Decay one half is too slow to absorb even one factor of 28.
example : 1 < ∑ i ∈ range 1, (28 : ℝ) ^ (1 - i) * (1 / 2) ^ dyadicSlack 1 i := by
  norm_num [sum_range_succ, dyadicSlack]

private def active (σ : Bool) (_ : Fin 1) : Prop := σ = true

private instance (σ : Bool) (x : Fin 1) : Decidable (active σ x) :=
  inferInstanceAs (Decidable (σ = true))

private def initial : State (Fin 1) := { defaultValue := 0, row := 0 }

private def increments (σ : Bool) (i : ℕ) (_ : Fin 1) : Fin 2 → ℝ :=
  if σ = true ∧ i = 0 then ![4, -2] else 0

private noncomputable def noise (i : ℕ) (σ : Bool) (_ : Fin 1) : ℝ :=
  if σ then (1 / 64) ^ dyadicSlack 2 i else -100

private theorem first_overflow :
    IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 0 := by
  constructor
  · intro i hi
    omega
  · norm_num [stepThreshold, inputRow, initial, increments,
      threshold, kthLargest, entrySize, Fin.univ_succ, filter_insert, filter_singleton]

private theorem selected_tail :
    firstOverflowNoiseTail {0} (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments true) initial 2 (fun i => 28 ^ (2 - i)) (fun i => noise i true 0) =
        161 / 256 := by
  have hevent (j : ℕ) :
      IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
        (increments true) initial j ↔ j = 0 :=
    ⟨fun hj => hj.unique first_overflow, fun h => h ▸ first_overflow⟩
  rw [show ({0} : Finset (Fin 1)) = univ by decide]
  unfold firstOverflowNoiseTail
  simp only [hevent]
  norm_num [sum_range_succ, noise, dyadicSlack, sum_Ico_succ_top]

private theorem noise_moment (i : ℕ) :
    vertexNormPow 4 1 (1 / 2) active (noise i) =
      ((1 / 64 : ℝ) ^ dyadicSlack 2 i) ^ 4 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [active, noise, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 64) _)]
  ring

-- The same draw chooses the source, actual overflow, and both noise values.
example : vertexNormPow 4 1 (1 / 2) active
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 2 (fun i => 28 ^ (2 - i)) (fun i => noise i σ 0)) =
        (161 / 256 : ℝ) ^ 4 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [active, selected_tail]

-- Apply the uniform theorem with all individual decay budgets discharged.
example : vertexNormPow 4 1 (1 / 2) active
    (fun σ _ => firstOverflowNoiseTail univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (increments σ) initial 2 (fun i => 28 ^ (2 - i)) (fun i => noise i σ 0)) ≤
        (7 / 9 : ℝ) ^ 4 := by
  have h := vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget
    (fun (_ : Bool) (_ : Fin 1) => (univ : Finset (Fin 1)))
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun σ _ => increments σ)
    (fun _ _ => initial) 2 (by decide : 4 ≠ 0) (N := 1) (u := 1 / 2) (by norm_num)
    active (C := 28) (q := 1 / 64) (ε := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) noise
    (by
      intro i _ σ x hx
      have hs : σ = true := hx
      subst σ
      change 0 ≤ (1 / 64 : ℝ) ^ dyadicSlack 2 i
      positivity)
    (fun i _ => by simpa using (noise_moment i).le)
  norm_num at h ⊢
  exact h

end ComplexityTests.OverflowNoiseDecay
