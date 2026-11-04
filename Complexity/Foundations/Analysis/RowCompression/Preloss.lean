/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Floors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted loss before a compression overflow

The preloss estimate of [OpenAI2026LogSpace, Lemma 8.2, (8.9)] bounds the error introduced by
compression in terms of the errors of the uncompressed prefixes. At an endpoint with true first
coordinate `d ≥ η > 0`, a compression change is possible only when the current entry is small.
If the preceding compression loss is at most the current floor `ρ` and `8 * ρ ≤ η`, the raw
prefix is then at most half of `d`. Its clipped relative error is bounded below by
`η / (2 * (1 + η))`. Combining this with the local change bound `6 * ρ` charges the change to
the raw prefix error, with the explicit constant `12 * (1 + η) / η`.

The main theorem applies this argument to the actual recursion `Cslib.RowCompression.iterate`.
It assumes that each earlier threshold is at most its floor and that
`6 * ∑ k < i, ρ k ≤ ρ i`. These hypotheses are weaker than the corresponding small-floor
conditions in (8.8). A corollary discharges both numerical hypotheses for the concrete scaled
dyadic floors constructed in `Cslib.RowCompression.dyadicFloor`. The clipped
error is (8.3), with channel indices `0, 1` and group indices starting at zero, so group `i`
uses the uncompressed prefix at `i + 1`. The argument is independent of the moment exponent.

This module proves the weighted preloss assertion of Lemma 8.2. It does not assert preservation
of row functions by the stationary reference, stability after overflow, or a machine-space bound.

## Main definitions

* `Cslib.RowCompression.clippedError`: the maximum of the clipped relative first-channel error
  and the clipped absolute second-channel error.

## Main results

* `Cslib.RowCompression.abs_update_sub_le_mul_clippedError`: the local weighted change bound.
* `Cslib.RowCompression.abs_iterate_sub_uncompressed_le_weighted`: the weighted preloss estimate
  for the concrete increment-and-compression recursion.
* `Cslib.RowCompression.abs_iterate_sub_uncompressed_le_weighted_dyadic`: the same estimate with
  the numerical floor conditions discharged by the explicit dyadic schedule.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemma 8.2, weighted preloss assertion (8.9)
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*}

/-- The clipped endpoint error of [OpenAI2026LogSpace, (8.3)]. The first true coordinate is
nonnegative in applications; the second coordinate is measured by absolute error. -/
@[expose] noncomputable def clippedError (d v : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  max (min 1 (|w 0 - d| / (1 + d))) (min 1 |w 1 - v|)

theorem clippedError_nonneg (d v : ℝ) (w : Fin 2 → ℝ) : 0 ≤ clippedError d v w :=
  (le_min (by norm_num) (abs_nonneg _)).trans (le_max_right _ _)

theorem clippedError_le_one (d v : ℝ) (w : Fin 2 → ℝ) : clippedError d v w ≤ 1 :=
  max_le (min_le_left _ _) (min_le_left _ _)

@[simp]
theorem clippedError_self (d v : ℝ) (w : Fin 2 → ℝ) (hd : w 0 = d) (hv : w 1 = v) :
    clippedError d v w = 0 := by
  simp [clippedError, hd, hv]

private theorem le_clipped_relative_error {η d r ρ : ℝ} (hη : 0 < η) (hd : η ≤ d)
    (hsmall : 8 * ρ ≤ η) (hr : r ≤ 4 * ρ) :
    η / (2 * (1 + η)) ≤ min 1 (|r - d| / (1 + d)) := by
  have hden : 0 < 1 + d := by linarith
  have hηden : 0 < 2 * (1 + η) := by positivity
  have hdiff : d ≤ 2 * |r - d| := by linarith [neg_le_abs (r - d)]
  refine le_min ?_ ?_
  · apply (div_le_iff₀ hηden).2
    linarith
  · apply (div_le_div_iff₀ hηden hden).2
    nlinarith [mul_nonneg (show 0 ≤ 1 + η by positivity)
      (show 0 ≤ 2 * |r - d| - d by linarith)]

/-- Before overflow, a change at a genuinely large target can be charged to the raw prefix's
clipped error. `raw` is the uncompressed prefix; `w` also includes preceding compression loss.
Only the first coordinate of that preceding loss is needed. -/
theorem abs_update_sub_le_mul_clippedError {s : Finset ι} {n K : ℕ} {ρ z η d v : ℝ}
    {w : ι → Fin 2 → ℝ} {raw : Fin 2 → ℝ} (hη : 0 < η) (hd : η ≤ d)
    (hno : threshold s n ρ z w ≤ ρ) (hsmall : 8 * ρ ≤ η) {y : ι}
    (hprev : |w y 0 - raw 0| ≤ ρ) (ν : Fin 2) :
    |update s n K ρ z w y ν - w y ν| ≤
      (12 * (1 + η) / η) * ρ * clippedError d v raw := by
  have hρ : 0 ≤ ρ := threshold_nonneg.trans hno
  have hC : 0 ≤ 12 * (1 + η) / η := by positivity
  by_cases hlarge : 3 * threshold s n ρ z w ≤ entrySize (w y)
  · rw [update_eq_self_of_three_mul_le hlarge, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hC hρ) (clippedError_nonneg _ _ _)
  have hsize : entrySize (w y) < 3 * threshold s n ρ z w := lt_of_not_ge hlarge
  have hraw : raw 0 ≤ 4 * ρ := by
    have hw := (le_abs_self (w y 0)).trans (abs_apply_le_entrySize (w y) 0)
    have hp := (abs_le.mp hprev).1
    linarith
  have he : η / (2 * (1 + η)) ≤ clippedError d v raw :=
    (le_clipped_relative_error hη hd hsmall hraw).trans (le_max_left _ _)
  have hcancel : (12 * (1 + η) / η) * ρ * (η / (2 * (1 + η))) = 6 * ρ := by
    field_simp
    ring
  calc |update s n K ρ z w y ν - w y ν| ≤ 6 * ρ :=
      (abs_update_sub_le_six_mul y ν).trans (mul_le_mul_of_nonneg_left hno (by norm_num))
    _ = (12 * (1 + η) / η) * ρ * (η / (2 * (1 + η))) := hcancel.symm
    _ ≤ (12 * (1 + η) / η) * ρ * clippedError d v raw :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hC hρ)

/-- The weighted preloss estimate [OpenAI2026LogSpace, Lemma 8.2, (8.9)] for actual iterates.
The right-hand errors use raw prefixes, not compressed rows. No target upper bound is needed. -/
theorem abs_iterate_sub_uncompressed_le_weighted {s : Finset ι} {n K : ℕ → ℕ}
    {ρ : ℕ → ℝ} {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {η d v : ℝ}
    (hη : 0 < η) (hd : η ≤ d) (j : ℕ)
    (hno : ∀ i < j, stepThreshold s n K ρ Δ a i ≤ ρ i)
    (hsmall : ∀ i < j, 8 * ρ i ≤ η)
    (hprior : ∀ i < j, 6 * ∑ k ∈ range i, ρ k ≤ ρ i) (y : ι) (ν : Fin 2) :
    |(iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν| ≤
      (12 * (1 + η) / η) * ∑ i ∈ range j,
        ρ i * clippedError d v (uncompressedRow Δ a.row (i + 1) y) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj := Nat.lt_succ_self j
    have hno' : ∀ i < j, stepThreshold s n K ρ Δ a i ≤ ρ i :=
      fun i hi => hno i (Nat.lt_succ_of_lt hi)
    have hprev : |inputRow s n K ρ Δ a j y 0 -
        uncompressedRow Δ a.row (j + 1) y 0| ≤ ρ j := by
      rw [uncompressedRow_succ]
      simp only [inputRow, Pi.add_apply, add_sub_add_right_eq_sub]
      exact (abs_iterate_sub_uncompressed_le_of_no_overflow j hno' y 0).trans (hprior j hj)
    have hstep := abs_update_sub_le_mul_clippedError (K := K j) (v := v) hη hd
      (hno j hj) (hsmall j hj) hprev ν
    have hbefore := ih hno' (fun i hi => hsmall i (Nat.lt_succ_of_lt hi))
      (fun i hi => hprior i (Nat.lt_succ_of_lt hi))
    have hdiff : |inputRow s n K ρ Δ a j y ν - uncompressedRow Δ a.row (j + 1) y ν| =
        |(iterate s n K ρ Δ a j).row y ν - uncompressedRow Δ a.row j y ν| := by
      rw [uncompressedRow_succ]
      simp only [inputRow, Pi.add_apply, add_sub_add_right_eq_sub]
    calc _ ≤ |(iterate s n K ρ Δ a (j + 1)).row y ν - inputRow s n K ρ Δ a j y ν| +
          |inputRow s n K ρ Δ a j y ν - uncompressedRow Δ a.row (j + 1) y ν| :=
        abs_sub_le _ _ _
      _ ≤ (12 * (1 + η) / η) * ρ j *
            clippedError d v (uncompressedRow Δ a.row (j + 1) y) +
          (12 * (1 + η) / η) * ∑ i ∈ range j,
            ρ i * clippedError d v (uncompressedRow Δ a.row (i + 1) y) := by
        rw [hdiff]
        exact add_le_add hstep hbefore
      _ = _ := by rw [sum_range_succ]; ring

/-- Weighted preloss for the concrete dyadic floors. The numerical small-floor hypotheses are
proved by the schedule; only the absence of overflow before the selected prefix remains assumed.
The parameter choice against the later estimator's noise/capacity constants is separate. -/
theorem abs_iterate_sub_uncompressed_le_weighted_dyadic {s : Finset ι} {n K : ℕ → ℕ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {η d v : ℝ}
    (hη : 0 < η) (hd : η ≤ d) (m j : ℕ) (hj : j ≤ m)
    (hno : ∀ i < j, stepThreshold s n K (dyadicFloor η m) Δ a i ≤ dyadicFloor η m i)
    (y : ι) (ν : Fin 2) :
    |(iterate s n K (dyadicFloor η m) Δ a j).row y ν - uncompressedRow Δ a.row j y ν| ≤
      (12 * (1 + η) / η) * ∑ i ∈ range j,
        dyadicFloor η m i * clippedError d v (uncompressedRow Δ a.row (i + 1) y) := by
  apply abs_iterate_sub_uncompressed_le_weighted hη hd j hno
  · exact fun i _ => eight_mul_dyadicFloor_le hη.le m i
  · intro i hi
    have hsum := six_sum_range_dyadicFloor_le hη.le (hi.trans_le hj)
    have hfloor := dyadicFloor_nonneg hη.le m i
    linarith

end Cslib.RowCompression
