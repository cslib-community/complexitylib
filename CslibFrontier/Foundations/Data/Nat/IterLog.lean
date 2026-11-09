/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, next to `Mathlib/Data/Nat/Log.lean`)

public import CslibFrontier.Foundations.Data.Nat.LogStar
public import CslibFrontier.Init

/-!
# Iterated Base-2 Floor Logarithm (`Nat.iterLog` and `Nat.floorLogStar`)

`CslibFrontier/Foundations/Data/Nat/LogStar.lean` defines the tower of twos `Nat.twoTower` and its
ceiling-logarithm inverse `Nat.logStar` (the least `k` with `(Nat.clog 2)^[k] n ≤ 1`, equivalently
`n ≤ Nat.twoTower k`). This module supplies the companion **iterated base-2 floor logarithm**
`Nat.iterLog k n = (Nat.log 2)^[k] n` and its exact stopping count
`Nat.floorLogStar n = Nat.logStar (n + 1) - 1` (the least `k` such that `Nat.iterLog k n ≤ 1`,
equivalently `n < Nat.twoTower (k + 1)`).

Naming the floor stopping count `Nat.floorLogStar` avoids collision with the ceiling convention
`Nat.logStar` (whose values differ at `n = 3` and `n = 5, …, 15`), while defining it in terms of
`Nat.logStar` avoids duplicating structural fuel recursion and provides exact floor-logarithm
recurrence laws (`floorLogStar_of_gt_one : 1 < n → floorLogStar n = floorLogStar (Nat.log 2 n) + 1`
and `lt_floorLogStar_iff : k < floorLogStar n ↔ 1 < iterLog k n`).

## Main definitions

* `Nat.iterLog`: iterated base-2 floor logarithm `⌊log₂^(k) n⌋`.
* `Nat.floorLogStar`: base-2 floor iterated logarithm `Nat.logStar (n + 1) - 1`, the least `k` with
  `iterLog k n ≤ 1`.

## Main results

* `Nat.iterLog_eq_iterate`, `Nat.iterLog_succ_apply`, `Nat.iterLog_add`: iteration laws.
* `Nat.iterLog_mono`, `Nat.iterLog_anti_left`: monotonicity in `n` and antitonicity in `k`.
* `Nat.iterLog_le_one_iff_lt_twoTower`: `iterLog k n ≤ 1 ↔ n < twoTower (k + 1)`.
* `Nat.floorLogStar_of_le_one`, `Nat.floorLogStar_of_gt_one`: base and `Nat.log 2` step equations.
* `Nat.iterLog_floorLogStar_le_one`, `Nat.lt_floorLogStar_iff`, `Nat.floorLogStar_le_iff`: exact
  threshold characterizations `k < floorLogStar n ↔ 1 < iterLog k n` and
  `floorLogStar n ≤ k ↔ iterLog k n ≤ 1`.
* `Nat.floorLogStar_mono`, `Nat.floorLogStar_le_logStar`, `Nat.logStar_le_floorLogStar_add_one`:
  monotonicity and comparison within `1` of ceiling `Nat.logStar`.
* `Nat.max_iterLog_two_max_four`, `Nat.iterLog_two_max_four_le_clog`,
  `Nat.clog_clog_max_four_le_two_mul_iterLog`: positivity and ceiling comparison at `k = 2`.
-/

public section

namespace Nat

/-- Iterated base-2 floor logarithm `⌊log₂^(k) n⌋`: `iterLog 0 n = n` and
`iterLog (k + 1) n = Nat.log 2 (iterLog k n)`. -/
@[expose] def iterLog : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => Nat.log 2 (iterLog k n)

@[simp]
theorem iterLog_zero (n : ℕ) : iterLog 0 n = n := rfl

@[simp]
theorem iterLog_succ (k n : ℕ) : iterLog (k + 1) n = Nat.log 2 (iterLog k n) := rfl

/-- `iterLog k` agrees with `k`-fold function iteration of `Nat.log 2`. -/
theorem iterLog_eq_iterate (k n : ℕ) : iterLog k n = (Nat.log 2)^[k] n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterLog_succ, Function.iterate_succ_apply', ih]

/-- Applying `Nat.log 2` before `k` iterations is the same as `k + 1` iterations. -/
theorem iterLog_succ_apply (k n : ℕ) : iterLog (k + 1) n = iterLog k (Nat.log 2 n) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterLog_succ, ih, iterLog_succ]

/-- Addition of iteration counts composes `iterLog`. -/
theorem iterLog_add (j k n : ℕ) : iterLog (j + k) n = iterLog j (iterLog k n) := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Nat.succ_add, iterLog_succ, ih]

@[simp]
theorem iterLog_zero_right (k : ℕ) : iterLog k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem iterLog_one_of_pos {k : ℕ} (hk : 1 ≤ k) : iterLog k 1 = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, iterLog_succ_apply]
  simp

/-- `iterLog k n` never exceeds `n`. -/
theorem iterLog_le_self (k n : ℕ) : iterLog k n ≤ n := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (Nat.log_le_self 2 (iterLog k n)).trans ih

/-- `iterLog k` is monotone in its second argument. -/
theorem iterLog_mono (k : ℕ) : Monotone (iterLog k) := by
  intro m n h
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.log_mono_right ih

/-- `iterLog k n` is antitone in the iteration count `k`. -/
theorem iterLog_anti_left {j k : ℕ} (n : ℕ) (h : j ≤ k) : iterLog k n ≤ iterLog j n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, iterLog_add]
  exact iterLog_le_self d (iterLog j n)

/-- Whenever `1 < iterLog k n`, one more base-2 logarithm strictly decreases it. -/
theorem iterLog_lt_of_gt_one {k n : ℕ} (h : 1 < iterLog k n) :
    iterLog (k + 1) n < iterLog k n :=
  Nat.log_lt_self 2 (by omega)

/-- `iterLog k n ≤ 1` holds iff `n` is strictly below `twoTower (k + 1)`. -/
theorem iterLog_le_one_iff_lt_twoTower {k n : ℕ} :
    iterLog k n ≤ 1 ↔ n < twoTower (k + 1) := by
  induction k generalizing n with
  | zero =>
    change n ≤ 1 ↔ n < 2
    omega
  | succ k ih =>
    rw [iterLog_succ_apply, ih, twoTower_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [twoTower_pos, Nat.two_pow_pos]
    · exact Nat.log_lt_iff_lt_pow Nat.one_lt_two hn.ne'

/-- Base-2 floor iterated logarithm: the least `k : ℕ` such that `iterLog k n ≤ 1`,
expressed via `logStar (n + 1) - 1` so it shares `logStar`'s structural kernel reduction. -/
@[expose] def floorLogStar (n : ℕ) : ℕ :=
  logStar (n + 1) - 1

/-- Threshold characterization: `floorLogStar n ≤ k` iff `iterLog k n ≤ 1`. -/
theorem floorLogStar_le_iff {k n : ℕ} : floorLogStar n ≤ k ↔ iterLog k n ≤ 1 := by
  rw [floorLogStar, Nat.sub_le_iff_le_add, logStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  omega

/-- Strict threshold characterization: `k < floorLogStar n` iff `1 < iterLog k n`. -/
theorem lt_floorLogStar_iff {k n : ℕ} : k < floorLogStar n ↔ 1 < iterLog k n := by
  rw [← not_le, floorLogStar_le_iff, not_le]

/-- After `floorLogStar n` iterations, `iterLog` reaches at most `1`. -/
theorem iterLog_floorLogStar_le_one (n : ℕ) : iterLog (floorLogStar n) n ≤ 1 :=
  floorLogStar_le_iff.mp le_rfl

/-- Base equation: `floorLogStar n = 0` for `n ≤ 1`. -/
theorem floorLogStar_of_le_one {n : ℕ} (hn : n ≤ 1) : floorLogStar n = 0 :=
  Nat.le_zero.mp (floorLogStar_le_iff.mpr hn)

@[simp]
theorem floorLogStar_zero : floorLogStar 0 = 0 := rfl

@[simp]
theorem floorLogStar_one : floorLogStar 1 = 0 := rfl

/-- Step equation: for `1 < n`, `floorLogStar n = floorLogStar (Nat.log 2 n) + 1`. -/
theorem floorLogStar_of_gt_one {n : ℕ} (hn : 1 < n) :
    floorLogStar n = floorLogStar (Nat.log 2 n) + 1 := by
  apply le_antisymm
  · rw [floorLogStar_le_iff, iterLog_succ_apply]
    exact iterLog_floorLogStar_le_one (Nat.log 2 n)
  · have hpos : 0 < floorLogStar n := lt_floorLogStar_iff.mpr hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hpos)
    have hle : iterLog (k + 1) n ≤ 1 := by
      rw [Nat.add_comm 1 k] at hk
      exact hk ▸ iterLog_floorLogStar_le_one n
    rw [iterLog_succ_apply, ← floorLogStar_le_iff] at hle
    omega

@[simp]
theorem floorLogStar_two : floorLogStar 2 = 1 := rfl

/-- `floorLogStar` is monotone. -/
theorem floorLogStar_mono : Monotone floorLogStar := fun _ n h =>
  floorLogStar_le_iff.mpr ((iterLog_mono (floorLogStar n) h).trans (iterLog_floorLogStar_le_one n))

/-- Floor `floorLogStar` never exceeds ceiling `logStar`. -/
theorem floorLogStar_le_logStar (n : ℕ) : floorLogStar n ≤ logStar n := by
  rw [floorLogStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  exact lt_of_le_of_lt (le_twoTower_logStar n) (twoTower_lt_twoTower_succ _)

/-- Ceiling `logStar` exceeds floor `floorLogStar` by at most `1`. -/
theorem logStar_le_floorLogStar_add_one (n : ℕ) : logStar n ≤ floorLogStar n + 1 := by
  rw [logStar_le_iff]
  exact (iterLog_le_one_iff_lt_twoTower.mp (iterLog_floorLogStar_le_one n)).le

/-- `floorLogStar n` never exceeds `n`. -/
theorem floorLogStar_le_self (n : ℕ) : floorLogStar n ≤ n :=
  (floorLogStar_le_logStar n).trans (logStar_le_self n)

/-- Clamping at `4` makes the two-step floor logarithm at least `1`. -/
theorem one_le_iterLog_two_max_four (n : ℕ) : 1 ≤ iterLog 2 (max n 4) := by
  have h4 : iterLog 2 4 = 1 := by decide
  rw [← h4]
  exact iterLog_mono 2 (_root_.le_max_right n 4)

/-- Exact clamping bridge: `max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4)`. -/
theorem max_iterLog_two_max_four (n : ℕ) :
    max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4) :=
  _root_.max_eq_left (one_le_iterLog_two_max_four n)

/-- Floor-to-ceiling lower bound: `iterLog 2 (max n 4) ≤ ⌈log₂ ⌈log₂ (max n 4)⌉⌉`. -/
theorem iterLog_two_max_four_le_clog (n : ℕ) :
    iterLog 2 (max n 4) ≤ Nat.clog 2 (Nat.clog 2 (max n 4)) := by
  have h1 : Nat.log 2 (max n 4) ≤ Nat.clog 2 (max n 4) :=
    Nat.log_le_clog 2 (max n 4)
  exact (Nat.log_mono_right h1).trans (Nat.log_le_clog 2 _)

/-- Ceiling-to-floor upper bound: `⌈log₂ ⌈log₂ (max n 4)⌉⌉ ≤ 2 * iterLog 2 (max n 4)`. -/
theorem clog_clog_max_four_le_two_mul_iterLog (n : ℕ) :
    Nat.clog 2 (Nat.clog 2 (max n 4)) ≤ 2 * iterLog 2 (max n 4) := by
  set m := max n 4
  set k := iterLog 2 m
  have hk : 1 ≤ k := one_le_iterLog_two_max_four n
  have hlog_lt : Nat.log 2 m < 2 ^ (k + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (Nat.log 2 m)
  have hm_lt : m < 2 ^ (2 ^ (k + 1)) := by
    calc m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      _ ≤ 2 ^ (2 ^ (k + 1)) := Nat.pow_le_pow_right Nat.two_pos hlog_lt
  have hclog1 : Nat.clog 2 m ≤ 2 ^ (k + 1) :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hm_lt.le
  have hclog2 : Nat.clog 2 (Nat.clog 2 m) ≤ k + 1 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hclog1
  omega

end Nat
