/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.SentinelRelative
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Restarting compression from an already-added group input

At a first overflow in group `j`, the available error estimate concerns the raw input after
adding group `j`, not the preceding raw prefix. Start the local calculation from the actual
`inputRow` and use zero as its first increment. The local calculation agrees exactly with the
original calculation after every positive number of updates.

The corresponding local error sequence repeats the overflow group's error at indices zero and
one. Its adjacent-prefix propagation budget is at most four times the usual weighted tail sum.
Only errors from group `j` onward occur in this bound. These are exact indexing and finite-sum
identities; they require no overflow event, row bounds, or probabilistic hypotheses.

## Main definitions

* `Cslib.RowCompression.preloadedIncrement`: the remaining increment schedule with its first
  increment already added to the initial state.
* `Cslib.RowCompression.preloadedError`: the error envelope at the resulting local raw prefixes.

## Main results

* `Cslib.RowCompression.iterate_preloadedIncrement`: equality of the restarted and original
  compressed calculations after a positive number of updates.
* `Cslib.RowCompression.uncompressedRow_preloadedIncrement`: equality of the corresponding
  raw prefixes after a positive number of local increments.
* `Cslib.RowCompression.prefixErrorBudget_preloadedError_le`: the adjacent-prefix budget is
  bounded by four times the original weighted tail sum.
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- Restart at group `j` after its increment has already been added. The first local increment
is zero; later local increments are the actual subsequent increments. -/
@[expose] def preloadedIncrement (Δ : ℕ → ι → Fin 2 → ℝ) (j : ℕ) :
    ℕ → ι → Fin 2 → ℝ
  | 0 => 0
  | i + 1 => Δ (j + i + 1)

@[simp]
theorem preloadedIncrement_zero (Δ : ℕ → ι → Fin 2 → ℝ) (j : ℕ) :
    preloadedIncrement Δ j 0 = 0 := rfl

@[simp]
theorem preloadedIncrement_succ (Δ : ℕ → ι → Fin 2 → ℝ) (j i : ℕ) :
    preloadedIncrement Δ j (i + 1) = Δ (j + i + 1) := rfl

/-- Both local prefixes zero and one use the already-added group `j` input. Later local
prefixes use the errors of the subsequent groups. -/
@[expose] def preloadedError (ε : ℕ → ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => ε j
  | i + 1 => ε (j + i)

@[simp]
theorem preloadedError_zero (ε : ℕ → ℝ) (j : ℕ) : preloadedError ε j 0 = ε j := rfl

@[simp]
theorem preloadedError_succ (ε : ℕ → ℝ) (j i : ℕ) :
    preloadedError ε j (i + 1) = ε (j + i) := rfl

/-- A restart from the already-added input gives exactly the original compressed state after
any positive number of updates. Group `j` is compressed once, with no duplicated increment. -/
theorem iterate_preloadedIncrement {s : Finset ι} {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} (j : ℕ) {r : ℕ} (hr : 0 < r) :
    iterate s (fun i => n (j + i)) (fun i => K (j + i)) (fun i => ρ (j + i))
      (preloadedIncrement Δ j)
      ⟨(iterate s n K ρ Δ a j).defaultValue, inputRow s n K ρ Δ a j⟩ r =
        iterate s n K ρ Δ a (j + r) := by
  cases r with
  | zero => omega
  | succ r =>
    clear hr
    induction r with
    | zero =>
      simp [iterate_succ, advance, inputRow]
    | succ r ih =>
      rw [iterate_succ, ih]
      simp only [preloadedIncrement_succ, Nat.add_succ, iterate_succ]

/-- Raw prefixes after the preloaded restart agree with the original raw prefixes. At local
index zero the initial row is already global raw prefix `j + 1`. -/
theorem uncompressedRow_preloadedIncrement {Δ : ℕ → ι → Fin 2 → ℝ}
    {raw₀ : ι → Fin 2 → ℝ} (j : ℕ) {r : ℕ} (hr : 0 < r) :
    uncompressedRow (preloadedIncrement Δ j) (uncompressedRow Δ raw₀ (j + 1)) r =
      uncompressedRow Δ raw₀ (j + r) := by
  cases r with
  | zero => omega
  | succ r =>
    clear hr
    induction r with
    | zero =>
      funext y ν
      simp only [uncompressedRow_succ, uncompressedRow_zero, preloadedIncrement_zero,
        Pi.zero_apply, add_zero]
    | succ r ih =>
      funext y ν
      rw [uncompressedRow_succ, ih]
      simp only [preloadedIncrement_succ, Nat.add_succ, uncompressedRow_succ]

/-- The adjacent-prefix budget for a preloaded restart is at most four times the original
weighted tail budget. The estimate does not require any error bound before group `j`. -/
theorem prefixErrorBudget_preloadedError_le {ε : ℕ → ℝ} (j : ℕ) {r : ℕ}
    (hr : 0 < r) (hε : ∀ i ∈ Ico j (j + r), 0 ≤ ε i) :
    prefixErrorBudget (preloadedError ε j) r ≤
      4 * ∑ i ∈ Ico j (j + r), 28 ^ (j + r - i) * ε i := by
  cases r with
  | zero => omega
  | succ r =>
    let T : ℝ := ∑ i ∈ range (r + 1), 28 ^ (r + 1 - i) * ε (j + i)
    have hnonneg (i : ℕ) (hi : i < r + 1) : 0 ≤ ε (j + i) :=
      hε (j + i) (mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
    have htail : (∑ i ∈ Ico j (j + (r + 1)), (28 : ℝ) ^ (j + (r + 1) - i) * ε i) =
        T := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_add_left]
      rfl
    have hfirst : (28 : ℝ) ^ (r + 1) * ε j ≤ T := by
      have h := single_le_sum (s := range (r + 1))
        (f := fun i => (28 : ℝ) ^ (r + 1 - i) * ε (j + i))
        (fun i hi => mul_nonneg (by positivity) (hnonneg i (mem_range.mp hi)))
        (mem_range.mpr (Nat.zero_lt_succ r))
      simpa only [Nat.sub_zero, Nat.add_zero] using h
    have hback :
        (∑ i ∈ range r, (28 : ℝ) ^ (r - i) * ε (j + i)) ≤ T := by
      calc
        _ ≤ ∑ i ∈ range r, (28 : ℝ) ^ (r + 1 - i) * ε (j + i) := by
          refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Nat.le_succ r) i)) ?_
          exact hnonneg i ((mem_range.mp hi).trans_le (Nat.le_succ r))
        _ ≤ T := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ r))
          (fun i hi _ => mul_nonneg (by positivity) (hnonneg i (mem_range.mp hi)))
    have hbefore :
        (∑ i ∈ range (r + 1), (28 : ℝ) ^ (r + 1 - i) * preloadedError ε j i) ≤ 2 * T := by
      rw [sum_range_succ']
      simp only [preloadedError_succ, preloadedError_zero, Nat.add_sub_add_right, Nat.sub_zero]
      linarith
    have hafter :
        (∑ i ∈ range (r + 1), (28 : ℝ) ^ (r + 1 - i) * preloadedError ε j (i + 1)) = T := by
      simp only [preloadedError_succ]
      rfl
    rw [htail]
    unfold prefixErrorBudget
    simp only [mul_add, sum_add_distrib, preloadedError_zero]
    rw [hafter]
    linarith

end Cslib.RowCompression
