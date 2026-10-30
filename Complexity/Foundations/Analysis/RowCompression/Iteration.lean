/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Iterated row compression

This module iterates the concrete update of [OpenAI2026LogSpace, Section 8.2, (8.5)--(8.6)].
At group `i`, add the increment `Δ i` to the current row, then compress using capacities
`n i`, `K i` and floor `ρ i`. The state contains the entire row and its common default, so two
calculations need not select the same exception lists.

The stability bound is the update-only part of (8.7): an initial absolute perturbation `δ`
is at most `28 ^ j * δ` after `j` updates with the same increments. Restarting at any group
gives the same assertion for a perturbation introduced there. The paper's final root functions
are not formalized here. The optional conversion to a fifth power of a slack assumes the
explicit scheduling fact `2 ^ j ≤ d + 1`; no halving schedule is constructed in this module.

The accumulated row loss is at most six times the sum of the actual compression thresholds.
Before the first overflow, each threshold is its floor, yielding the unweighted estimate
`6 * ∑ i < j, ρ i` in the first assertion of [OpenAI2026LogSpace, Lemma 8.2]. This does not
assert the weighted preloss estimate (8.9), the small-floor estimates (8.8), stationary-reference
preservation, or a machine-space bound.

## Main definitions

* `Cslib.RowCompression.State`: the default and full two-coordinate row.
* `Cslib.RowCompression.advance`, `Cslib.RowCompression.iterate`: one update and its iteration.
* `Cslib.RowCompression.inputRow`, `Cslib.RowCompression.stepThreshold`: the input and actual
  threshold at each group.
* `Cslib.RowCompression.uncompressedRow`: the initial row plus the prefix sum of increments.

## Main results

* `Cslib.RowCompression.iterate_stability`: width-independent propagation by `28 ^ j`.
* `Cslib.RowCompression.iterate_add`: restart a calculation at any group.
* `Cslib.RowCompression.iterate_stability_from`: propagate a perturbation from any group.
* `Cslib.RowCompression.iterate_stability_of_pow_le`: a polynomial bound given a slack bound.
* `Cslib.RowCompression.abs_iterate_sub_uncompressed_le`: accumulated compression loss.
* `Cslib.RowCompression.abs_iterate_sub_uncompressed_le_of_no_overflow`: the floor-sum bound.
* `Cslib.RowCompression.iterate_defaultValue_monotone`: defaults never decrease.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 8.2--8.3, (8.7) and the unweighted assertion of Lemma 8.2
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- A compressed row represented by its full values and its common default. The finite
exception list is intentionally not part of the mathematical state. -/
structure State (ι : Type*) where
  /-- The first coordinate of the default entry; its second coordinate is zero. -/
  defaultValue : ℝ
  /-- The full row, including values at positions represented by the default. -/
  row : ι → Fin 2 → ℝ

/-- Add an increment and apply the concrete compression update. -/
@[expose] noncomputable def advance (s : Finset ι) (n K : ℕ) (ρ : ℝ)
    (Δ : ι → Fin 2 → ℝ) (a : State ι) : State ι :=
  { defaultValue := newDefault s n K ρ a.defaultValue (a.row + Δ)
    row := update s n K ρ a.defaultValue (a.row + Δ) }

/-- The state after `j` increment-and-compression groups, indexed starting at zero. -/
@[expose] noncomputable def iterate (s : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) : ℕ → State ι
  | 0 => a
  | j + 1 => advance s (n j) (K j) (ρ j) (Δ j) (iterate s n K ρ Δ a j)

/-- The row immediately after adding group `j` and before compressing it. -/
@[expose] noncomputable def inputRow (s : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (j : ℕ) : ι → Fin 2 → ℝ :=
  (iterate s n K ρ Δ a j).row + Δ j

/-- The actual threshold of compression group `j`, including the old default and the size rank. -/
@[expose] noncomputable def stepThreshold (s : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (j : ℕ) : ℝ :=
  threshold s (n j) (ρ j) (iterate s n K ρ Δ a j).defaultValue (inputRow s n K ρ Δ a j)

/-- The initial row plus all increments before group `j`, with no compression. -/
@[expose] noncomputable def uncompressedRow (Δ : ℕ → ι → Fin 2 → ℝ)
    (w : ι → Fin 2 → ℝ) (j : ℕ) (y : ι) (ν : Fin 2) : ℝ :=
  w y ν + ∑ i ∈ range j, Δ i y ν

variable {s : Finset ι} {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
  {Δ : ℕ → ι → Fin 2 → ℝ} {a b : State ι}

@[simp]
theorem iterate_zero : iterate s n K ρ Δ a 0 = a := rfl

theorem iterate_succ (j : ℕ) : iterate s n K ρ Δ a (j + 1) =
    advance s (n j) (K j) (ρ j) (Δ j) (iterate s n K ρ Δ a j) := rfl

@[simp]
theorem uncompressedRow_zero {w : ι → Fin 2 → ℝ} : uncompressedRow Δ w 0 = w := by
  funext y ν
  simp [uncompressedRow]

theorem uncompressedRow_succ {w : ι → Fin 2 → ℝ} (j : ℕ) (y : ι) (ν : Fin 2) :
    uncompressedRow Δ w (j + 1) y ν = uncompressedRow Δ w j y ν + Δ j y ν := by
  simp only [uncompressedRow, sum_range_succ]
  ring

theorem stepThreshold_nonneg (j : ℕ) : 0 ≤ stepThreshold s n K ρ Δ a j :=
  threshold_nonneg

theorem floor_le_stepThreshold (j : ℕ) : ρ j ≤ stepThreshold s n K ρ Δ a j :=
  floor_le_threshold

/-- The one-step compression loss, before any accumulation over the schedule. -/
theorem abs_iterate_succ_sub_inputRow_le (j : ℕ) (y : ι) (ν : Fin 2) :
    |(iterate s n K ρ Δ a (j + 1)).row y ν - inputRow s n K ρ Δ a j y ν| ≤
      6 * stepThreshold s n K ρ Δ a j :=
  abs_update_sub_le_six_mul y ν

/-- Addition of the same increment cancels in the one-step stability estimate. -/
theorem advance_stability {n K : ℕ} {ρ δ : ℝ} {Δ : ι → Fin 2 → ℝ}
    (hn : 0 < n) (hK : 0 < K) (hδ : 0 ≤ δ) (hz : |a.defaultValue - b.defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |a.row y ν - b.row y ν| ≤ δ) :
    |(advance s n K ρ Δ a).defaultValue - (advance s n K ρ Δ b).defaultValue| ≤ 28 * δ ∧
      ∀ y ∈ s, ∀ ν, |(advance s n K ρ Δ a).row y ν -
        (advance s n K ρ Δ b).row y ν| ≤ 28 * δ := by
  have hadd : ∀ y ∈ s, ∀ ν, |(a.row + Δ) y ν - (b.row + Δ) y ν| ≤ δ := by
    intro y hy ν
    simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hw y hy ν
  constructor
  · exact (abs_newDefault_sub_newDefault_le hn hK hδ hz hadd).trans (by linarith)
  · intro y hy ν
    exact abs_update_sub_update_le hn hK hδ hz hadd hy ν

/-- An absolute perturbation of the full initial state grows by at most `28 ^ j` through
`j` compression groups with the same increments [OpenAI2026LogSpace, (8.7)]. -/
theorem iterate_stability {δ : ℝ} (hδ : 0 ≤ δ) (hz : |a.defaultValue - b.defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |a.row y ν - b.row y ν| ≤ δ) (j : ℕ)
    (hn : ∀ i < j, 0 < n i) (hK : ∀ i < j, 0 < K i) :
    |(iterate s n K ρ Δ a j).defaultValue - (iterate s n K ρ Δ b j).defaultValue| ≤
        28 ^ j * δ ∧
      ∀ y ∈ s, ∀ ν, |(iterate s n K ρ Δ a j).row y ν -
        (iterate s n K ρ Δ b j).row y ν| ≤ 28 ^ j * δ := by
  induction j with
  | zero => simpa using And.intro hz hw
  | succ j ih =>
    have h := ih (fun i hi => hn i (Nat.lt_succ_of_lt hi))
      (fun i hi => hK i (Nat.lt_succ_of_lt hi))
    have hnext := advance_stability (ρ := ρ j) (Δ := Δ j) (hn j (Nat.lt_succ_self j))
      (hK j (Nat.lt_succ_self j)) (by positivity : 0 ≤ 28 ^ j * δ) h.1 h.2
    simpa only [iterate_succ, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hnext

/-- Restarting the indexed schedule preserves exactly the same states. -/
theorem iterate_add (i j : ℕ) : iterate s n K ρ Δ a (i + j) =
    iterate s (fun k => n (i + k)) (fun k => K (i + k)) (fun k => ρ (i + k))
      (fun k => Δ (i + k)) (iterate s n K ρ Δ a i) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nat.add_succ, iterate_succ, ih]

/-- A perturbation present after group `i` propagates through the next `j` updates with factor
at most `28 ^ j`, without requiring agreement of earlier states or exception lists. -/
theorem iterate_stability_from (i j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hz : |(iterate s n K ρ Δ a i).defaultValue -
      (iterate s n K ρ Δ b i).defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |(iterate s n K ρ Δ a i).row y ν -
      (iterate s n K ρ Δ b i).row y ν| ≤ δ)
    (hn : ∀ k < j, 0 < n (i + k)) (hK : ∀ k < j, 0 < K (i + k)) :
    |(iterate s n K ρ Δ a (i + j)).defaultValue -
        (iterate s n K ρ Δ b (i + j)).defaultValue| ≤ 28 ^ j * δ ∧
      ∀ y ∈ s, ∀ ν, |(iterate s n K ρ Δ a (i + j)).row y ν -
        (iterate s n K ρ Δ b (i + j)).row y ν| ≤ 28 ^ j * δ := by
  rw [iterate_add (a := a) i j, iterate_add (a := b) i j]
  exact iterate_stability hδ hz hw j hn hK

/-- A schedule with `2 ^ j ≤ d + 1` turns the propagation factor into a polynomial in the
slack. We enlarge `28` to `2 ^ 5`, avoiding real exponents in this explicit coarse bound. -/
theorem propagation_le_slack_pow_five {j d : ℕ} (hjd : 2 ^ j ≤ d + 1) :
    (28 : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ 5 := by
  calc (28 : ℝ) ^ j ≤ ((2 : ℝ) ^ 5) ^ j :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) j
    _ = ((2 : ℝ) ^ j) ^ 5 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ ((d : ℝ) + 1) ^ 5 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hjd) 5

/-- The full state has polynomial perturbation growth under the explicit logarithmic
group-count condition. The condition is a premise about the schedule, not a claimed
construction of the paper's halving schedule. -/
theorem iterate_stability_of_pow_le {δ : ℝ} (hδ : 0 ≤ δ)
    (hz : |a.defaultValue - b.defaultValue| ≤ δ)
    (hw : ∀ y ∈ s, ∀ ν, |a.row y ν - b.row y ν| ≤ δ) (j d : ℕ)
    (hn : ∀ i < j, 0 < n i) (hK : ∀ i < j, 0 < K i) (hjd : 2 ^ j ≤ d + 1) :
    |(iterate s n K ρ Δ a j).defaultValue - (iterate s n K ρ Δ b j).defaultValue| ≤
        ((d : ℝ) + 1) ^ 5 * δ ∧
      ∀ y ∈ s, ∀ ν, |(iterate s n K ρ Δ a j).row y ν -
        (iterate s n K ρ Δ b j).row y ν| ≤ ((d : ℝ) + 1) ^ 5 * δ := by
  have h := iterate_stability (ρ := ρ) (Δ := Δ) hδ hz hw j hn hK
  have hscale := mul_le_mul_of_nonneg_right (propagation_le_slack_pow_five hjd) hδ
  exact ⟨h.1.trans hscale, fun y hy ν => (h.2 y hy ν).trans hscale⟩

/-- The default never decreases, independently of the increments or the capacities. -/
theorem iterate_defaultValue_monotone : Monotone fun j => (iterate s n K ρ Δ a j).defaultValue :=
  monotone_nat_of_le_succ fun _ => le_newDefault

/-- The default is nonnegative when the initial default is. -/
theorem iterate_defaultValue_nonneg (ha : 0 ≤ a.defaultValue) (j : ℕ) :
    0 ≤ (iterate s n K ρ Δ a j).defaultValue :=
  ha.trans (iterate_defaultValue_monotone (Nat.zero_le j))

/-- The accumulated row loss is bounded by six times the sum of the actual thresholds.
The increments cancel between the compressed and uncompressed calculations. -/
theorem abs_iterate_sub_uncompressed_le (j : ℕ) (y : ι) (ν : Fin 2) :
    |(iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν| ≤
      6 * ∑ i ∈ range j, stepThreshold s n K ρ Δ a i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := abs_iterate_succ_sub_inputRow_le (s := s) (n := n) (K := K) (ρ := ρ)
      (Δ := Δ) (a := a) j y ν
    have hdiff : |inputRow s n K ρ Δ a j y ν - uncompressedRow Δ a.row (j + 1) y ν| =
        |(iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν| := by
      rw [uncompressedRow_succ]
      simp only [inputRow, Pi.add_apply, add_sub_add_right_eq_sub]
    calc _ ≤ |(iterate s n K ρ Δ a (j + 1)).row y ν - inputRow s n K ρ Δ a j y ν| +
          |inputRow s n K ρ Δ a j y ν - uncompressedRow Δ a.row (j + 1) y ν| :=
        abs_sub_le _ _ _
      _ ≤ 6 * stepThreshold s n K ρ Δ a j + 6 * ∑ i ∈ range j,
          stepThreshold s n K ρ Δ a i := by rw [hdiff]; exact add_le_add hstep ih
      _ = _ := by rw [sum_range_succ]; ring

/-- Before the first overflow, the accumulated loss is at most six times the sum of floors
[OpenAI2026LogSpace, Lemma 8.2, unweighted assertion]. The hypothesis says precisely that no
earlier group's actual threshold exceeds its prescribed floor. -/
theorem abs_iterate_sub_uncompressed_le_of_no_overflow (j : ℕ)
    (hno : ∀ i < j, stepThreshold s n K ρ Δ a i ≤ ρ i) (y : ι) (ν : Fin 2) :
    |(iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν| ≤
      6 * ∑ i ∈ range j, ρ i := by
  exact (abs_iterate_sub_uncompressed_le j y ν).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun i hi => hno i (mem_range.mp hi)) (by norm_num))

/-- The default has an accumulated change bound of three times the threshold sum. This also
controls the dummy positions, which receive no increments. -/
theorem iterate_defaultValue_sub_le_three_mul_sum (ha : 0 ≤ a.defaultValue) (j : ℕ) :
    (iterate s n K ρ Δ a j).defaultValue - a.defaultValue ≤
      3 * ∑ i ∈ range j, stepThreshold s n K ρ Δ a i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hz := iterate_defaultValue_nonneg (s := s) (n := n) (K := K) (ρ := ρ) (Δ := Δ) ha j
    have hnew : (iterate s n K ρ Δ a (j + 1)).defaultValue ≤
        3 * stepThreshold s n K ρ Δ a j := newDefault_le_three_mul
    rw [sum_range_succ]
    linarith

/-- Before overflow, the default (and hence every dummy entry) has accumulated change at most
three times the floor sum. -/
theorem abs_iterate_defaultValue_sub_le_of_no_overflow (ha : 0 ≤ a.defaultValue) (j : ℕ)
    (hno : ∀ i < j, stepThreshold s n K ρ Δ a i ≤ ρ i) :
    |(iterate s n K ρ Δ a j).defaultValue - a.defaultValue| ≤
      3 * ∑ i ∈ range j, ρ i := by
  have hmono : a.defaultValue ≤ (iterate s n K ρ Δ a j).defaultValue :=
    iterate_defaultValue_monotone (Nat.zero_le j)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  exact (iterate_defaultValue_sub_le_three_mul_sum ha j).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun i hi => hno i (mem_range.mp hi)) (by norm_num))

end Cslib.RowCompression
