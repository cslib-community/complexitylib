/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Reference
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Perturbations of compression schedules

The concrete compression update has Lipschitz constant `28`. Comparing schedules with different
increments gives an initial-error term `28 ^ m * δ` and a sum of increment-error terms
`28 ^ (m - i) * ε i`. Both defaults and all retained coordinates satisfy the same bound.

A zero-increment reference with the usual small negative and second-coordinate bounds preserves
an initial padded-rank ceiling above the floor scale. Its actual thresholds satisfy that ceiling
as well. These estimates are the absolute-error ingredients of the sentinel comparison in
[OpenAI2026LogSpace, Section 8.3, Lemma 8.3]. They do not by themselves convert relative errors
at unbounded first coordinates to absolute errors or prove the final row-output comparison.

## Main results

* `Cslib.RowCompression.iterate_stability_of_increment_error`: weighted stability for two actual
  schedules with different increments.
* `Cslib.RowCompression.reference_iterate_firstRank_le`: a uniform padded-rank ceiling for
  zero-increment references.
* `Cslib.RowCompression.reference_stepThreshold_le`: the corresponding actual threshold bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, proof of Lemma 8.3, the absolute comparison after sentinel replacement
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*} {s : Finset ι} {a b : State ι}

/-- One update with an increment discrepancy adds that discrepancy before the factor `28`.
The initial defaults and both full rows may already differ. -/
theorem advance_stability_of_increment_error {n K : ℕ} {ρ δ ε : ℝ}
    {Δ Δ' : ι → Fin 2 → ℝ} (hn : 0 < n) (hK : 0 < K) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hz : |a.defaultValue - b.defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |a.row y ν - b.row y ν| ≤ δ)
    (hΔ : ∀ y ∈ s, ∀ ν, |Δ y ν - Δ' y ν| ≤ ε) :
    |(advance s n K ρ Δ a).defaultValue - (advance s n K ρ Δ' b).defaultValue| ≤
        28 * (δ + ε) ∧
      ∀ y ∈ s, ∀ ν,
        |(advance s n K ρ Δ a).row y ν - (advance s n K ρ Δ' b).row y ν| ≤
          28 * (δ + ε) := by
  have hinput (y : ι) (hy : y ∈ s) (ν : Fin 2) :
      |(a.row + Δ) y ν - (b.row + Δ') y ν| ≤ δ + ε := by
    calc
      _ = |(a.row y ν - b.row y ν) + (Δ y ν - Δ' y ν)| := by
        congr 1
        simp only [Pi.add_apply]
        ring
      _ ≤ |a.row y ν - b.row y ν| + |Δ y ν - Δ' y ν| := abs_add_le _ _
      _ ≤ δ + ε := add_le_add (hw y hy ν) (hΔ y hy ν)
  have hz' : |a.defaultValue - b.defaultValue| ≤ δ + ε := hz.trans (le_add_of_nonneg_right hε)
  constructor
  · exact (abs_newDefault_sub_newDefault_le hn hK (add_nonneg hδ hε) hz' hinput).trans
      (by nlinarith)
  · intro y hy ν
    exact abs_update_sub_update_le hn hK (add_nonneg hδ hε) hz' hinput hy ν

private theorem propagation_succ (δ : ℝ) (ε : ℕ → ℝ) (j : ℕ) :
    28 * (28 ^ j * δ + ∑ i ∈ range j, 28 ^ (j - i) * ε i + ε j) =
      28 ^ (j + 1) * δ + ∑ i ∈ range (j + 1), 28 ^ (j + 1 - i) * ε i := by
  have hsum : (∑ i ∈ range j, (28 : ℝ) ^ (j + 1 - i) * ε i) =
      28 * ∑ i ∈ range j, (28 : ℝ) ^ (j - i) * ε i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hexp : j + 1 - i = (j - i) + 1 := by
      have hi' := mem_range.mp hi
      omega
    rw [hexp, pow_succ]
    ring
  rw [sum_range_succ, hsum]
  simp only [Nat.add_sub_cancel_left, pow_succ]
  ring

/-- Different increments contribute at the group where they are actually added, with one
factor `28` for that update and for each subsequent update. No threshold ceiling is assumed. -/
theorem iterate_stability_of_increment_error {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
    {Δ Δ' : ℕ → ι → Fin 2 → ℝ} {δ : ℝ} {ε : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hz : |a.defaultValue - b.defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |a.row y ν - b.row y ν| ≤ δ) (m : ℕ)
    (hn : ∀ i < m, 0 < n i) (hK : ∀ i < m, 0 < K i)
    (hε : ∀ i < m, 0 ≤ ε i)
    (hΔ : ∀ i < m, ∀ y ∈ s, ∀ ν, |Δ i y ν - Δ' i y ν| ≤ ε i) :
    |(iterate s n K ρ Δ a m).defaultValue - (iterate s n K ρ Δ' b m).defaultValue| ≤
        28 ^ m * δ + ∑ i ∈ range m, 28 ^ (m - i) * ε i ∧
      ∀ y ∈ s, ∀ ν,
        |(iterate s n K ρ Δ a m).row y ν - (iterate s n K ρ Δ' b m).row y ν| ≤
          28 ^ m * δ + ∑ i ∈ range m, 28 ^ (m - i) * ε i := by
  induction m with
  | zero => simpa using And.intro hz hw
  | succ m ih =>
    have ih' := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
      (fun i hi => hK i (Nat.lt_succ_of_lt hi))
      (fun i hi => hε i (Nat.lt_succ_of_lt hi))
      (fun i hi => hΔ i (Nat.lt_succ_of_lt hi))
    have hbudget : 0 ≤ 28 ^ m * δ + ∑ i ∈ range m, 28 ^ (m - i) * ε i := by
      exact add_nonneg (mul_nonneg (by positivity) hδ)
        (sum_nonneg fun i hi => mul_nonneg (by positivity)
          (hε i (Nat.lt_succ_of_lt (mem_range.mp hi))))
    have h := advance_stability_of_increment_error (ρ := ρ m)
      (hn m (Nat.lt_succ_self m)) (hK m (Nat.lt_succ_self m)) hbudget
      (hε m (Nat.lt_succ_self m)) ih'.1 ih'.2 (hΔ m (Nat.lt_succ_self m))
    simpa only [iterate_succ, propagation_succ] using h

section Reference

variable {n : ℕ → ℕ} {K : ℕ} {ρ : ℕ → ℝ} {η Q : ℝ}

/-- A stationary reference's padded first rank stays below any initial ceiling above the
reference scale. The hypotheses are only on its initial row and the finite schedule. -/
theorem reference_iterate_firstRank_le (hη : 0 ≤ η) (hηQ : η ≤ Q) (hK : 0 < K)
    (hfirst : ∀ y ∈ s, -η ≤ a.row y 0) (hsecond : ∀ y ∈ s, |a.row y 1| ≤ η)
    (hq : firstRank s K a.defaultValue a.row ≤ Q) (m : ℕ)
    (hn : ∀ i < m, K ≤ n i) (hρ : ∀ i < m, ρ i ≤ η) :
    firstRank s K (iterate s n (fun _ => K) ρ (fun _ => 0) a m).defaultValue
      (iterate s n (fun _ => K) ρ (fun _ => 0) a m).row ≤ Q := by
  induction m with
  | zero => exact hq
  | succ m ih =>
    have hprev := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
      (fun i hi => hρ i (Nat.lt_succ_of_lt hi))
    have hb := reference_iterate_bounds (n := n) (K := K) (ρ := ρ) hη hfirst hsecond m
    have hnext := reference_firstRank_le
      (z := (iterate s n (fun _ => K) ρ (fun _ => 0) a m).defaultValue)
      hη (hρ m (Nat.lt_succ_self m)) hK
      (hn m (Nat.lt_succ_self m)) hb.1 hb.2
    simpa only [iterate_succ, advance, add_zero] using hnext.trans (max_le hηQ hprev)

/-- The same initial reference ceiling controls every actual input threshold. -/
theorem reference_stepThreshold_le (hη : 0 ≤ η) (hηQ : η ≤ Q) (hK : 0 < K)
    (hfirst : ∀ y ∈ s, -η ≤ a.row y 0) (hsecond : ∀ y ∈ s, |a.row y 1| ≤ η)
    (hq : firstRank s K a.defaultValue a.row ≤ Q) (m : ℕ)
    (hn : ∀ i ≤ m, K ≤ n i) (hρ : ∀ i ≤ m, ρ i ≤ η) :
    stepThreshold s n (fun _ => K) ρ (fun _ => 0) a m ≤ Q := by
  have hb := reference_iterate_bounds (n := n) (K := K) (ρ := ρ) hη hfirst hsecond m
  have hr := reference_iterate_firstRank_le hη hηQ hK hfirst hsecond hq m
    (fun i hi => hn i hi.le) (fun i hi => hρ i hi.le)
  have ht := reference_threshold_le
    (z := (iterate s n (fun _ => K) ρ (fun _ => 0) a m).defaultValue)
    hη (hρ m le_rfl) hK (hn m le_rfl) hb.1 hb.2
  simpa only [stepThreshold, inputRow, add_zero] using ht.trans (max_le hηQ hr)

end Reference

end Cslib.RowCompression
