/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of rare mean and correlated noise tail bounds)

public import Complexity.Foundations.Probability.HeavyCountTail
import Complexity.Foundations.Data.Finset.Expect

/-!
# Nonzero heavy-event mean and correlated noise

A heavy event occurs on one of two equally likely environments. A deterministic unit mean gains
that factor one half, while unit noise concentrated on the event retains its unconditional
moment one half: multiplying its moment by rarity again would be false.
-/

public section

namespace ComplexityTests.HeavyCountTail

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators

/-- The rank channel retains its sole endpoint on exactly one Boolean draw. -/
abbrev rankKept (σ : Bool) (_ : Unit) : Prop := σ = true

private theorem heavy_iff (σ : Bool) :
    heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ ↔ σ = true := by
  classical
  cases σ <;> norm_num [heavyCountEvent, rankKept]

/-- Unit noise concentrated on the very same rare event. -/
@[expose] def noise (σ : Bool) (_ : Unit) : ℝ := if σ then 1 else 0

private theorem max_unit : kthLargest 1 (univ : Finset Unit) (fun _ => |(1 : ℝ)|) = 1 := by
  norm_num [kthLargest]

private theorem mean_budget :
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ _ => (1 : ℝ)) ≤ 1 ^ 4 := by
  norm_num [rowNormPow, Fintype.expect_bool]

open Classical in
private theorem rarity :
    (#{σ : Bool | True ∧ True ∧ heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ} : ℝ) ≤
      (1 / 2 : ℝ) * #{_σ : Bool | True ∧ True} := by
  have heq : ({σ : Bool | True ∧ True ∧
      heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ} : Finset Bool) = {true} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact heavy_iff σ
  rw [heq]
  norm_num

/-- The event and its weighted deterministic mean tail are genuinely nonzero. -/
theorem rare_mean_moment :
    vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True)
      (eventTail 1 (fun _ σ (_ : Unit) =>
        heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ) (fun _ => 1)
        (fun _ _ _ => kthLargest 1 (univ : Finset Unit) (fun _ => |(1 : ℝ)|))) = 1 / 2 := by
  classical
  simp only [vertexNormPow, eventTail, sum_range_one, Nat.Ico_zero_eq_range,
    one_mul, max_unit]
  rw [Fintype.expect_bool]
  norm_num [heavyCountEvent, rankKept]

/-- The new actual-heavy-event theorem applies to that finite instance. -/
theorem rare_mean_bound :
    vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True)
      (eventTail 1 (fun _ σ (_ : Unit) =>
        heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ) (fun _ => 1)
        (fun _ _ _ => kthLargest 1 (univ : Finset Unit) (fun _ => |(1 : ℝ)|))) ≤
      ((1 / 2 : ℝ) ^ (4⁻¹ : ℝ)) ^ 4 := by
  classical
  have h := vertexNormPow_heavyCountTail_le (p := 4) (N := 1) (u := 1) (by decide)
    (by norm_num) (fun (_ : Bool) (_ : Unit) => True) rankKept (fun _ _ => True)
    1 (fun _ _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => 1) (fun _ _ _ => 1)
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    (fun _ _ _ _ => rarity) (fun _ _ => mean_budget)
  simpa [Nat.Ico_zero_eq_range] using h

/-- Correlated noise has positive unconditional moment even though its support is rare. -/
theorem noise_moment : vertexNormPow 4 1 1
    (fun (_ : Bool) (_ : Unit) => True) noise = 1 / 2 := by
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [noise]

/-- Applying the mean's rarity factor to correlated noise would give a false inequality. -/
theorem noise_cannot_gain_rarity : ¬ vertexNormPow 4 1 1
    (fun (_ : Bool) (_ : Unit) => True) noise ≤
      (1 / 2 : ℝ) * vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) noise := by
  rw [noise_moment]
  norm_num

/-- An actual compression run overflows immediately, before its single weighted tail. -/
@[expose] def initialRow : State Unit := ⟨0, 0⟩

/-- The nonzero increment makes the actual first threshold exceed its floor. -/
@[expose] def increments (_ : ℕ) (_ : Unit) (_ : Fin 2) : ℝ := 2

private theorem first_overflow :
    IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1) increments initialRow 0 := by
  constructor
  · intro i hi; omega
  · norm_num [stepThreshold, inputRow, iterate, initialRow, increments, threshold,
      kthLargest, entrySize]

/-- The actual true-overflow mean/noise tail is nonzero and shares its rare noise environment. -/
@[expose] noncomputable def actualTail (σ : Bool) (_x : Unit) : ℝ := by
  classical
  exact ∑ j ∈ range 1,
    if IsFirstOverflow univ (fun _ => 1) (fun _ => 1) (fun _ => 1) increments initialRow j ∧
        heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ then
      ∑ i ∈ Ico j 1, (1 : ℝ) * (kthLargest 1 (univ : Finset Unit)
        (fun _ => |(1 : ℝ)|) + noise σ ()) else 0

open Classical in
private theorem actualTail_eq : actualTail = (fun σ x =>
    if heavyCountEvent rankKept univ (fun (_ : Unit) => 1) 1 1 σ then 1 + noise σ x else 0) := by
  classical
  funext σ x
  unfold actualTail
  simp only [sum_range_one, first_overflow, true_and, Nat.Ico_zero_eq_range, one_mul, max_unit]

theorem actual_mixed_moment :
    vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) actualTail = 8 := by
  classical
  rw [actualTail_eq]
  unfold vertexNormPow
  rw [Fintype.expect_bool]
  norm_num [noise, heavyCountEvent, rankKept]

/-- The direct integrated theorem handles this actual mixed compression tail. -/
theorem actual_mixed_bound :
    vertexNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) actualTail ≤
      ((1 / 2 : ℝ) ^ (4⁻¹ : ℝ) + 1) ^ 4 := by
  classical
  have h := vertexNormPow_trueOverflowTail_le (p := 4) (N := 1) (u := 1) (by decide)
    (by norm_num) (fun (_ : Bool) (_ : Unit) => True) rankKept (fun _ _ => True)
    1 (fun _ _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 / 2)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ _ => 1)
    (by intros; norm_num) (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
    (fun _ _ _ _ => rarity) (fun _ _ => mean_budget)
    (fun _ _ => (univ : Finset Unit)) (fun _ => 1) (fun _ => 1)
    (fun _ _ => increments) (fun _ _ => initialRow) (fun _ => noise)
    (by intro i hi σ x hx; cases σ <;> norm_num [noise])
    (by intro i hi; rw [noise_moment]; norm_num)
  rw [actualTail_eq]
  simp only [sum_range_one, Nat.Ico_zero_eq_range, first_overflow, true_and, one_mul,
    mul_one, filter_true, abs_one] at h
  have hone : kthLargest 1 (univ : Finset Unit) (fun _ => (1 : ℝ)) = 1 := by
    norm_num [kthLargest]
  simpa only [hone, noise, Nat.cast_ofNat] using h

/-- The allowed zero normalization remains well-defined for the same nonzero tail array. -/
example : vertexNormPow 4 0 1 (fun (_ : Bool) (_ : Unit) => True) actualTail = 0 := by
  simp [vertexNormPow]

end ComplexityTests.HeavyCountTail
