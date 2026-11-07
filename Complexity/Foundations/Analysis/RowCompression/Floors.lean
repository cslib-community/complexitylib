/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Iteration
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit small floors for a halving compression schedule

For `m` groups, indexed by `i < m`, set `d_i = 2 ^ (m - (i + 1))`. These slacks halve down
to one, as in [OpenAI2026LogSpace, Section 8.1]. We construct the floors
`ρ_i = η * (1 / 1024) ^ d_i` for any fixed `η > 0`.

The paper uses the unscaled floors `2 ^ (-c₁ * d_i)` and chooses `c₁` large depending on its
fixed sensitivity margin `η`. Our explicit witness instead uses exponent ten and scales by `η`.
It proves the two numerical inequalities in (8.8), and `8 * ρ_i ≤ η`, for every positive `η`.
It does not select `c₁` against the other exponents in the integrated compression argument.

Consecutive floors grow by at least a factor of 1024. A finite induction therefore bounds the
sum before group `i` by `ρ_i / 1023`, and the sum over all groups by `η / 1023`. Multiplication
by six gives the two `/100` bounds, with no assumed small-sum hypothesis.

There are `m - (i + 1)` updates after group `i`, whose power of two equals `d_i`. Counting the
current group too introduces one extra factor of 28 in the perturbation bound; this is absorbed
by the unspecified outer constant in the source's (8.7).

## Main definitions

* `Cslib.RowCompression.dyadicSlack`: the decreasing power-of-two slacks.
* `Cslib.RowCompression.dyadicFloor`: the explicit margin-scaled floors.

## Main results

* `Cslib.RowCompression.six_sum_range_dyadicFloor_le`: prior floors are small relative to the
  current floor.
* `Cslib.RowCompression.six_sum_range_dyadicFloor_le_scale`: all floors are small relative to
  the sensitivity margin.
* `Cslib.RowCompression.eight_mul_dyadicFloor_le`: the local margin condition.
* `Cslib.RowCompression.propagation_le_dyadicSlack`: polynomial perturbation growth for the
  actual number of remaining groups.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 8.1--8.3, (8.7)--(8.8) (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

/-- The decreasing power-of-two slacks of a schedule with `m` groups. Indices `i ≥ m` are
defined too, with value one, but are not additional groups in the schedule. -/
@[expose] def dyadicSlack (m i : ℕ) : ℕ := 2 ^ (m - (i + 1))

/-- An explicit floor schedule at sensitivity scale `η`. The finite schedule consists of
indices `i < m`; the total function is convenient as an argument to `iterate`. -/
@[expose] noncomputable def dyadicFloor (η : ℝ) (m i : ℕ) : ℝ :=
  η * (1 / 1024) ^ dyadicSlack m i

theorem dyadicSlack_pos (m i : ℕ) : 0 < dyadicSlack m i := by
  unfold dyadicSlack
  positivity

@[simp]
theorem dyadicSlack_last (m : ℕ) : dyadicSlack (m + 1) m = 1 := by
  simp [dyadicSlack]

/-- Each slack is twice the next one while both indices are actual groups. -/
theorem dyadicSlack_succ {m i : ℕ} (hi : i + 1 < m) :
    dyadicSlack m i = 2 * dyadicSlack m (i + 1) := by
  have h : m - (i + 1) = m - (i + 1 + 1) + 1 := by omega
  unfold dyadicSlack
  rw [h, pow_succ, Nat.mul_comm]

theorem dyadicFloor_nonneg {η : ℝ} (hη : 0 ≤ η) (m i : ℕ) :
    0 ≤ dyadicFloor η m i := by
  unfold dyadicFloor
  positivity

theorem dyadicFloor_pos {η : ℝ} (hη : 0 < η) (m i : ℕ) :
    0 < dyadicFloor η m i := by
  unfold dyadicFloor
  positivity

@[simp]
theorem dyadicFloor_last (η : ℝ) (m : ℕ) : dyadicFloor η (m + 1) m = η / 1024 := by
  simp [dyadicFloor, div_eq_mul_inv]

private theorem pow_dyadicSlack_le (m i : ℕ) :
    (1 / 1024 : ℝ) ^ dyadicSlack m i ≤ 1 / 1024 := by
  simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 1024)
    (by norm_num : (1 / 1024 : ℝ) ≤ 1) (dyadicSlack_pos m i)

/-- Every floor is at most `η / 1024`, including the final floor where equality holds. -/
theorem dyadicFloor_le_scale_div {η : ℝ} (hη : 0 ≤ η) (m i : ℕ) :
    dyadicFloor η m i ≤ η / 1024 := by
  simpa only [dyadicFloor, mul_one_div] using
    mul_le_mul_of_nonneg_left (pow_dyadicSlack_le m i) hη

/-- Consecutive floors are separated by a factor of at least 1024. -/
theorem dyadicFloor_mul_le_succ {η : ℝ} (hη : 0 ≤ η) {m i : ℕ} (hi : i + 1 < m) :
    1024 * dyadicFloor η m i ≤ dyadicFloor η m (i + 1) := by
  have hbase := pow_dyadicSlack_le m (i + 1)
  have hnonneg := dyadicFloor_nonneg hη m (i + 1)
  have hmul := mul_le_mul_of_nonneg_left hbase hnonneg
  have heq : dyadicFloor η m i =
      dyadicFloor η m (i + 1) * (1 / 1024) ^ dyadicSlack m (i + 1) := by
    unfold dyadicFloor
    rw [dyadicSlack_succ hi, two_mul, pow_add, mul_assoc]
  rw [← heq] at hmul
  linarith

/-- The sum of earlier floors is bounded by the geometric factor `1 / 1023` times the
current floor. This is derived from the concrete schedule, without a small-sum premise. -/
theorem sum_range_dyadicFloor_le {η : ℝ} (hη : 0 ≤ η) {m j : ℕ} (hj : j < m) :
    ∑ i ∈ range j, dyadicFloor η m i ≤ dyadicFloor η m j / 1023 := by
  induction j with
  | zero => simpa using div_nonneg (dyadicFloor_nonneg hη m 0) (by norm_num : (0 : ℝ) ≤ 1023)
  | succ j ih =>
    have hprev := ih (Nat.lt_of_succ_lt hj)
    have hstep := dyadicFloor_mul_le_succ hη hj
    rw [sum_range_succ]
    linarith

/-- The first small-floor estimate of [OpenAI2026LogSpace, (8.8)], for the explicit scaled
schedule: all earlier compression changes total at most one hundredth of the current floor. -/
theorem six_sum_range_dyadicFloor_le {η : ℝ} (hη : 0 ≤ η) {m j : ℕ} (hj : j < m) :
    6 * ∑ i ∈ range j, dyadicFloor η m i ≤ dyadicFloor η m j / 100 := by
  have hsum := sum_range_dyadicFloor_le hη hj
  have hfloor := dyadicFloor_nonneg hη m j
  linarith

/-- The finite sum of all floors is at most `η / 1023`, uniformly in the number of groups. -/
theorem sum_range_dyadicFloor_le_scale {η : ℝ} (hη : 0 ≤ η) (m : ℕ) :
    ∑ i ∈ range m, dyadicFloor η m i ≤ η / 1023 := by
  cases m with
  | zero => simpa using div_nonneg hη (by norm_num : (0 : ℝ) ≤ 1023)
  | succ m =>
    have hsum := sum_range_dyadicFloor_le hη (Nat.lt_succ_self m)
    rw [sum_range_succ, dyadicFloor_last]
    rw [dyadicFloor_last] at hsum
    linarith

/-- The second small-floor estimate of [OpenAI2026LogSpace, (8.8)], uniformly in the number
of groups. -/
theorem six_sum_range_dyadicFloor_le_scale {η : ℝ} (hη : 0 ≤ η) (m : ℕ) :
    6 * ∑ i ∈ range m, dyadicFloor η m i ≤ η / 100 := by
  have hsum := sum_range_dyadicFloor_le_scale hη m
  linarith

/-- Every floor satisfies the local margin condition used in the weighted preloss estimate. -/
theorem eight_mul_dyadicFloor_le {η : ℝ} (hη : 0 ≤ η) (m i : ℕ) :
    8 * dyadicFloor η m i ≤ η := by
  have hfloor := dyadicFloor_le_scale_div hη m i
  linarith

/-- The exact power-of-two count of updates strictly after the current group is its slack. -/
theorem two_pow_remaining_eq_dyadicSlack (m i : ℕ) :
    2 ^ (m - (i + 1)) = dyadicSlack m i := rfl

/-- Including the current group, the propagation cost is at most an extra factor 28 times a
fifth-degree polynomial in its slack [OpenAI2026LogSpace, (8.7)]. -/
theorem propagation_le_dyadicSlack {m i : ℕ} (hi : i < m) :
    (28 : ℝ) ^ (m - i) ≤ 28 * ((dyadicSlack m i : ℝ) + 1) ^ 5 := by
  have hcount : m - i = m - (i + 1) + 1 := by omega
  have hpow : (28 : ℝ) ^ (m - (i + 1)) ≤ ((dyadicSlack m i : ℝ) + 1) ^ 5 :=
    propagation_le_slack_pow_five (Nat.le_succ (dyadicSlack m i))
  rw [hcount, pow_succ]
  nlinarith

end Cslib.RowCompression
