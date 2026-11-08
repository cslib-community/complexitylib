/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `Mathlib/Data/Nat/Log.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Hyperoperation
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Function.Iterate

/-!
# Towers of twos and the iterated logarithm

The tower `Nat.twoTower k = 2 ^ 2 ^ ⋯ ^ 2` (`k` twos, `twoTower 0 = 1`) and its inverse, the
iterated logarithm `Nat.logStar n = log* n`: the number of times `⌈log₂ ·⌉` must be applied to `n`
to reach a value at most `1`. Both are computable by structural recursion, so small values follow
by `decide`. Mathlib already has the tower as `hyperoperation 4 2` (and no iterated logarithm);
`Nat.twoTower_eq_hyperoperation` identifies the two. The structural copy is kept because
`hyperoperation` is defined by well-founded recursion, on which `decide` and kernel reduction get
stuck. The characterization `log* n ≤ k ↔ n ≤ twoTower k` (`Nat.logStar_le_iff`) is the main
interface; the recursion `log* n = log* ⌈log₂ n⌉ + 1` for `n ≥ 2` is `Nat.logStar_of_two_le`.

## Main definitions

* `Nat.twoTower`: the tower of twos `2 ↑↑ k`, a structurally recursive copy of
  `hyperoperation 4 2`.
* `Nat.logStar`: the iterated ceiling logarithm `log* n`.

## Main results

* `Nat.twoTower_eq_hyperoperation`: `twoTower k = hyperoperation 4 2 k`.
* `Nat.logStar_le_iff`: `log* n ≤ k ↔ n ≤ 2 ↑↑ k`.
* `Nat.logStar_of_two_le`: `log* n = log* ⌈log₂ n⌉ + 1` for `n ≥ 2`.
* `Nat.logStar_twoTower`, `Nat.logStar_twoTower_add_one`: `log* (2 ↑↑ k) = k` and
  `log* (2 ↑↑ k + 1) = k + 1`.
* `Nat.logStar_mono`: `log*` is monotone.
* `Nat.iterate_two_pow_le_twoTower`: iterating `c ↦ 2 ^ c` `k` times from `c` stays below
  `2 ↑↑ (k + log* c)`.
-/

public section

namespace Nat

/-- The tower of twos `2 ↑↑ k`: `twoTower 0 = 1` and `twoTower (k + 1) = 2 ^ twoTower k`.

This equals Mathlib's `hyperoperation 4 2` (`Nat.twoTower_eq_hyperoperation`). It is redefined by
structural recursion so that `decide` and kernel reduction can evaluate it; `hyperoperation` uses
well-founded recursion and does not reduce. -/
@[expose] def twoTower : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ twoTower k

/-- Iterated ceiling logarithm with a fuel argument; `logStar` supplies enough fuel. -/
@[expose] def logStarAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 1 then 0 else logStarAux fuel (clog 2 n) + 1

/-- The iterated logarithm `log* n`: the number of times `⌈log₂ ·⌉` must be applied to `n` to reach
a value at most `1`. Equivalently (`Nat.logStar_le_iff`), the least `k` with `n ≤ 2 ↑↑ k`. -/
@[expose] def logStar (n : ℕ) : ℕ := logStarAux n n

@[simp] theorem twoTower_zero : twoTower 0 = 1 := rfl

theorem twoTower_succ (k : ℕ) : twoTower (k + 1) = 2 ^ twoTower k := rfl

/-- The tower is Mathlib's fourth hyperoperation with base `2`. -/
theorem twoTower_eq_hyperoperation (k : ℕ) : twoTower k = hyperoperation 4 2 k := by
  induction k with
  | zero => rw [hyperoperation_ge_three_eq_one]; rfl
  | succ k ih => rw [twoTower, ih, hyperoperation_recursion, hyperoperation_three]

theorem twoTower_pos (k : ℕ) : 0 < twoTower k := by
  cases k with
  | zero => exact Nat.one_pos
  | succ k => exact Nat.pow_pos Nat.two_pos

theorem lt_twoTower (k : ℕ) : k < twoTower k := by
  induction k with
  | zero => exact Nat.one_pos
  | succ k ih => exact lt_of_le_of_lt (Nat.succ_le_of_lt ih) Nat.lt_two_pow_self

theorem twoTower_lt_twoTower_succ (k : ℕ) : twoTower k < twoTower (k + 1) :=
  Nat.lt_two_pow_self

theorem twoTower_strictMono : StrictMono twoTower :=
  strictMono_nat_of_lt_succ twoTower_lt_twoTower_succ

theorem twoTower_monotone : Monotone twoTower := twoTower_strictMono.monotone

theorem twoTower_le_twoTower {j k : ℕ} : twoTower j ≤ twoTower k ↔ j ≤ k :=
  twoTower_strictMono.le_iff_le

private theorem clog_two_lt_self {n : ℕ} (hn : 2 ≤ n) : clog 2 n < n := by
  have h : clog 2 n ≤ n - 1 := (clog_le_iff_le_pow (by decide)).2 <| by
    have := Nat.lt_two_pow_self (n := n - 1)
    omega
  omega

private theorem logStarAux_le_iff :
    ∀ fuel n k, n ≤ fuel → (logStarAux fuel n ≤ k ↔ n ≤ twoTower k)
  | 0, n, k, hn => by
    have := twoTower_pos k
    simp only [logStarAux, Nat.zero_le, true_iff]
    omega
  | fuel + 1, n, k, hn => by
    by_cases h1 : n ≤ 1
    · simp only [logStarAux, h1, ↓reduceIte, Nat.zero_le, true_iff]
      exact h1.trans (twoTower_pos k)
    · simp only [logStarAux, h1, ↓reduceIte]
      have hlt := clog_two_lt_self (n := n) (by omega)
      cases k with
      | zero =>
        simp only [twoTower_zero]
        omega
      | succ k =>
        rw [Nat.add_le_add_iff_right, logStarAux_le_iff fuel (clog 2 n) k (by omega),
          twoTower_succ, ← clog_le_iff_le_pow (by decide)]

/-- `log* n ≤ k` exactly when `n ≤ 2 ↑↑ k`. -/
theorem logStar_le_iff {n k : ℕ} : logStar n ≤ k ↔ n ≤ twoTower k :=
  logStarAux_le_iff n n k le_rfl

theorem le_twoTower_logStar (n : ℕ) : n ≤ twoTower (logStar n) :=
  logStar_le_iff.1 le_rfl

/-- `log* n` is the least `k` with `n ≤ 2 ↑↑ k`: the tower one level lower is below `n`. -/
theorem twoTower_logStar_pred_lt {n : ℕ} (hn : 1 < n) : twoTower (logStar n - 1) < n := by
  by_contra h
  have := logStar_le_iff.2 (not_lt.1 h)
  have h0 : logStar n ≠ 0 := by
    intro h0
    have := le_twoTower_logStar n
    rw [h0, twoTower_zero] at this
    omega
  omega

theorem logStar_mono : Monotone logStar := fun _ _ h =>
  logStar_le_iff.2 (h.trans (le_twoTower_logStar _))

@[simp] theorem logStar_twoTower (k : ℕ) : logStar (twoTower k) = k := by
  refine le_antisymm (logStar_le_iff.2 le_rfl) ?_
  by_contra h
  have := le_twoTower_logStar (twoTower k)
  rw [twoTower_le_twoTower] at this
  omega

/-- `log*` steps up just after each tower: `log* (2 ↑↑ k + 1) = k + 1`. -/
theorem logStar_twoTower_add_one (k : ℕ) : logStar (twoTower k + 1) = k + 1 := by
  refine le_antisymm (logStar_le_iff.2 (twoTower_lt_twoTower_succ k)) ?_
  by_contra h
  have := logStar_le_iff.1 (Nat.le_of_lt_succ (not_le.1 h))
  omega

theorem logStar_le_self (n : ℕ) : logStar n ≤ n :=
  logStar_le_iff.2 (lt_twoTower n).le

theorem logStar_of_le_one {n : ℕ} (hn : n ≤ 1) : logStar n = 0 :=
  Nat.le_zero.1 (logStar_le_iff.2 (by simpa using hn))

/-- The recursion `log* n = log* ⌈log₂ n⌉ + 1` for `n ≥ 2`. -/
theorem logStar_of_two_le {n : ℕ} (hn : 2 ≤ n) : logStar n = logStar (clog 2 n) + 1 := by
  refine le_antisymm (logStar_le_iff.2 ?_) ?_
  · rw [twoTower_succ, ← clog_le_iff_le_pow (by decide)]
    exact le_twoTower_logStar _
  · cases h : logStar n with
    | zero =>
      have := le_twoTower_logStar n
      rw [h, twoTower_zero] at this
      omega
    | succ k =>
      have := le_twoTower_logStar n
      rw [h, twoTower_succ, ← clog_le_iff_le_pow (by decide)] at this
      exact Nat.add_le_add_right (logStar_le_iff.2 this) 1

/-- Iterating `c ↦ 2 ^ c` `k` times from `c` stays below the tower of height `k + log* c`. -/
theorem iterate_two_pow_le_twoTower (k c : ℕ) :
    (2 ^ ·)^[k] c ≤ twoTower (k + logStar c) := by
  induction k with
  | zero => simpa using le_twoTower_logStar c
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.add_right_comm, twoTower_succ]
    exact Nat.pow_le_pow_right Nat.two_pos ih

end Nat
