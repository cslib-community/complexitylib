/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.LogStar

/-!
# Iterated Base-2 Floor Logarithm (`iterLog` and `logStar`)

`Complexity/Foundations/Data/Nat/LogStar.lean` defines the tower of twos `Nat.twoTower` and its
ceiling-logarithm inverse `Nat.logStar` (the least `k` with `(Nat.clog 2)^[k] n ≤ 1`, equivalently
`n ≤ Nat.twoTower k`). This module supplies the companion **iterated base-2 floor logarithm**
`Cslib.iterLog k n = (Nat.log 2)^[k] n` and its exact stopping count
`Cslib.logStar n = Nat.logStar (n + 1) - 1` (the least `k` such that `iterLog k n ≤ 1`,
equivalently `n < Nat.twoTower (k + 1)`).

Keeping `Cslib.logStar` defined directly in terms of `Nat.logStar` avoids duplicating structural
fuel recursion while providing exact floor-logarithm recurrence laws
(`logStar_of_gt_one : 1 < n → logStar n = logStar (Nat.log 2 n) + 1` and
`lt_logStar_iff : k < logStar n ↔ 1 < iterLog k n`) and explicit bridges to both `Nat.logStar` and
two-step ceiling logarithms.

## Main definitions

* `Cslib.iterLog`: iterated base-2 floor logarithm `⌊log₂^(k) n⌋`.
* `Cslib.logStar`: base-2 floor iterated logarithm `Nat.logStar (n + 1) - 1`, the least `k` with
  `iterLog k n ≤ 1`.

## Main results

* `Cslib.iterLog_eq_iterate`, `Cslib.iterLog_succ_apply`, `Cslib.iterLog_add`: iteration laws.
* `Cslib.iterLog_mono`, `Cslib.iterLog_anti_left`: monotonicity in `n` and antitonicity in `k`.
* `Cslib.iterLog_le_one_iff_lt_twoTower`: `iterLog k n ≤ 1 ↔ n < Nat.twoTower (k + 1)`.
* `Cslib.logStar_le_one`, `Cslib.logStar_of_gt_one`: base and `Nat.log 2` step equations.
* `Cslib.iterLog_logStar_le_one`, `Cslib.lt_logStar_iff`, `Cslib.logStar_le_iff`: exact threshold
  characterizations `k < logStar n ↔ 1 < iterLog k n` and `logStar n ≤ k ↔ iterLog k n ≤ 1`.
* `Cslib.logStar_mono`, `Cslib.logStar_le_natLogStar`, `Cslib.natLogStar_le_logStar_add_one`:
  monotonicity and comparison within `1` of `Nat.logStar`.
* `Cslib.max_iterLog_two_max_four`, `Cslib.iterLog_two_max_four_le_clog`,
  `Cslib.clog_clog_max_four_le_two_mul_iterLog`: positivity and ceiling comparison at `k = 2`.
-/

public section

namespace Cslib

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

/-- `iterLog k` is monotone in its argument `n`. -/
theorem iterLog_mono {m n : ℕ} (k : ℕ) (h : m ≤ n) : iterLog k m ≤ iterLog k n := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.log_mono_right ih

theorem iterLog_monotone (k : ℕ) : Monotone (iterLog k) :=
  fun _ _ h => iterLog_mono k h

/-- `iterLog k n` is antitone in the iteration count `k`. -/
theorem iterLog_anti_left {j k : ℕ} (n : ℕ) (h : j ≤ k) : iterLog k n ≤ iterLog j n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, iterLog_add]
  exact iterLog_le_self d (iterLog j n)

/-- Whenever `1 < iterLog k n`, one more base-2 logarithm strictly decreases it. -/
theorem iterLog_lt_of_gt_one {k n : ℕ} (h : 1 < iterLog k n) :
    iterLog (k + 1) n < iterLog k n :=
  Nat.log_lt_self 2 (by omega)

/-- `iterLog k n ≤ 1` holds iff `n` is strictly below `Nat.twoTower (k + 1)`. -/
theorem iterLog_le_one_iff_lt_twoTower {k n : ℕ} :
    iterLog k n ≤ 1 ↔ n < Nat.twoTower (k + 1) := by
  induction k generalizing n with
  | zero =>
    change n ≤ 1 ↔ n < 2
    omega
  | succ k ih =>
    rw [iterLog_succ_apply, ih, Nat.twoTower_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.twoTower_pos, Nat.two_pow_pos]
    · exact Nat.log_lt_iff_lt_pow Nat.one_lt_two hn.ne'

/-- Base-2 floor iterated logarithm `log* n`: the least `k : ℕ` such that `iterLog k n ≤ 1`,
expressed via `Nat.logStar (n + 1) - 1` so it shares `Nat.logStar`'s structural kernel reduction. -/
@[expose] def logStar (n : ℕ) : ℕ :=
  Nat.logStar (n + 1) - 1

/-- Threshold characterization: `logStar n ≤ k` iff `iterLog k n ≤ 1`. -/
theorem logStar_le_iff {k n : ℕ} : logStar n ≤ k ↔ iterLog k n ≤ 1 := by
  rw [logStar, Nat.sub_le_iff_le_add, Nat.logStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  omega

/-- Strict threshold characterization: `k < logStar n` iff `1 < iterLog k n`. -/
theorem lt_logStar_iff {k n : ℕ} : k < logStar n ↔ 1 < iterLog k n := by
  rw [← not_le, logStar_le_iff, not_le]

/-- After `logStar n` iterations, `iterLog` reaches at most `1`. -/
theorem iterLog_logStar_le_one (n : ℕ) : iterLog (logStar n) n ≤ 1 :=
  logStar_le_iff.mp le_rfl

/-- Base equation: `logStar n = 0` for `n ≤ 1`. -/
theorem logStar_le_one {n : ℕ} (hn : n ≤ 1) : logStar n = 0 :=
  Nat.le_zero.mp (logStar_le_iff.mpr hn)

@[simp]
theorem logStar_zero : logStar 0 = 0 := rfl

@[simp]
theorem logStar_one : logStar 1 = 0 := rfl

/-- Step equation: for `1 < n`, `logStar n = logStar (Nat.log 2 n) + 1`. -/
theorem logStar_of_gt_one {n : ℕ} (hn : 1 < n) : logStar n = logStar (Nat.log 2 n) + 1 := by
  apply le_antisymm
  · rw [logStar_le_iff, iterLog_succ_apply]
    exact iterLog_logStar_le_one (Nat.log 2 n)
  · have hpos : 0 < logStar n := lt_logStar_iff.mpr hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hpos)
    have hle : iterLog (k + 1) n ≤ 1 := by
      rw [Nat.add_comm 1 k] at hk
      exact hk ▸ iterLog_logStar_le_one n
    rw [iterLog_succ_apply, ← logStar_le_iff] at hle
    omega

@[simp]
theorem logStar_two : logStar 2 = 1 := rfl

/-- `logStar` is monotone. -/
theorem logStar_mono {m n : ℕ} (h : m ≤ n) : logStar m ≤ logStar n :=
  logStar_le_iff.mpr ((iterLog_mono (logStar n) h).trans (iterLog_logStar_le_one n))

theorem logStar_monotone : Monotone logStar :=
  fun _ _ h => logStar_mono h

/-- Floor `Cslib.logStar` never exceeds ceiling `Nat.logStar`. -/
theorem logStar_le_natLogStar (n : ℕ) : logStar n ≤ Nat.logStar n := by
  rw [logStar_le_iff, iterLog_le_one_iff_lt_twoTower]
  exact lt_of_le_of_lt (Nat.le_twoTower_logStar n) (Nat.twoTower_lt_twoTower_succ _)

/-- Ceiling `Nat.logStar` exceeds floor `Cslib.logStar` by at most `1`. -/
theorem natLogStar_le_logStar_add_one (n : ℕ) : Nat.logStar n ≤ logStar n + 1 := by
  rw [Nat.logStar_le_iff]
  exact ((iterLog_le_one_iff_lt_twoTower.mp (iterLog_logStar_le_one n)).le)

/-- `logStar n` never exceeds `n`. -/
theorem logStar_le_self (n : ℕ) : logStar n ≤ n :=
  (logStar_le_natLogStar n).trans (Nat.logStar_le_self n)

/-- Clamping at `4` makes the two-step floor logarithm at least `1`. -/
theorem one_le_iterLog_two_max_four (n : ℕ) : 1 ≤ iterLog 2 (max n 4) := by
  have h4 : iterLog 2 4 = 1 := by decide
  rw [← h4]
  exact iterLog_mono 2 (le_max_right n 4)

/-- Exact clamping bridge: `max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4)`. -/
theorem max_iterLog_two_max_four (n : ℕ) :
    max (iterLog 2 (max n 4)) 1 = iterLog 2 (max n 4) :=
  max_eq_left (one_le_iterLog_two_max_four n)

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

end Cslib
