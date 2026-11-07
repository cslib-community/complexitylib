/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log

/-!
# Halving recurrences

A cost `T` with `T n ≤ a T(⌈n/2⌉) + c n` for `n ≥ 2` grows like `a ^ ⌈log₂ n⌉`. The
substitution method proves this exactly, with a subtracted linear term: if
`2 c + 2 β ≤ a β` and `T n + β ≤ α` for `n ≤ 1`, then `T n + β 2 ^ k ≤ α a ^ k` whenever
`n ≤ 2 ^ k` (`Nat.add_mul_two_pow_le_mul_pow_of_halving`). The step hypothesis only asks that `T n`
be at most `a S + c n` whenever `S` bounds `T` on `[0, ⌈n/2⌉]`, so recurrences that split `n` into
`⌊n/2⌋` and `⌈n/2⌉`, or that are not monotone, are covered directly.

The real-exponent forms compare `a ^ ⌈log₂ n⌉` and `a ^ ⌊log₂ n⌋` with `n ^ log₂ a`, within a
factor `a` in each direction (`Nat.pow_clog_two_le_mul_rpow_logb`,
`Nat.rpow_logb_le_mul_pow_log_two`).

## Main results

* `Nat.add_mul_two_pow_le_mul_pow_of_halving`: the halving recurrence at a power of two.
* `Nat.add_mul_two_pow_clog_le_of_halving`: the same at `k = ⌈log₂ n⌉`.
* `Nat.pow_clog_two_le_mul_rpow_logb`: `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0`.
* `Nat.rpow_logb_le_mul_pow_log_two`: `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 4.3
  (the substitution method, including subtracting a lower-order term).
-/

public section

namespace Nat

/-- **Halving recurrence.** If `T n ≤ a S + c n` whenever `S` bounds `T` on `[0, ⌈n/2⌉]` and
`n ≥ 2`, then `T n + β 2 ^ k ≤ α a ^ k` for `n ≤ 2 ^ k`, provided the base case
`T n + β ≤ α` for `n ≤ 1` and the slack condition `2 c + 2 β ≤ a β`. -/
theorem add_mul_two_pow_le_mul_pow_of_halving {T : ℕ → ℕ} {a c α β : ℕ}
    (ha : 1 ≤ a) (hc : 2 * c + 2 * β ≤ a * β)
    (base : ∀ n ≤ 1, T n + β ≤ α)
    (step : ∀ n, 2 ≤ n → ∀ S, (∀ m ≤ (n + 1) / 2, T m ≤ S) → T n ≤ a * S + c * n) :
    ∀ k n, n ≤ 2 ^ k → T n + β * 2 ^ k ≤ α * a ^ k := by
  intro k
  induction k with
  | zero => intro n hn; simpa using base n (by simpa using hn)
  | succ k ih =>
    intro n hn
    rw [pow_succ, pow_succ]
    rcases Nat.lt_or_ge n 2 with h | h
    · have h1 := ih n (le_trans (by omega) (Nat.one_le_two_pow (n := k)))
      have h2 : T n ≤ a * T n := Nat.le_mul_of_pos_left _ ha
      have h3 : β * 2 ≤ a * β := by omega
      calc T n + β * (2 ^ k * 2) = T n + (β * 2) * 2 ^ k := by ring
        _ ≤ a * T n + (a * β) * 2 ^ k := by gcongr
        _ = a * (T n + β * 2 ^ k) := by ring
        _ ≤ a * (α * a ^ k) := by gcongr
        _ = α * (a ^ k * a) := by ring
    · set S := α * a ^ k - β * 2 ^ k with hS
      have hchild : ∀ m ≤ (n + 1) / 2, T m ≤ S := by
        intro m hm
        have := ih m (by rw [pow_succ] at hn; omega)
        omega
      have h1 := step n h S hchild
      have h2 : c * n ≤ c * (2 ^ k * 2) := by rw [pow_succ] at hn; gcongr
      have h3 : (2 * c + 2 * β) * 2 ^ k ≤ (a * β) * 2 ^ k := by gcongr
      have h4 : S + β * 2 ^ k = α * a ^ k := by
        have := ih 0 (Nat.zero_le _)
        omega
      calc T n + β * (2 ^ k * 2) ≤ a * S + c * (2 ^ k * 2) + β * (2 ^ k * 2) := by omega
        _ = a * S + (2 * c + 2 * β) * 2 ^ k := by ring
        _ ≤ a * S + (a * β) * 2 ^ k := by gcongr
        _ = a * (S + β * 2 ^ k) := by ring
        _ = α * (a ^ k * a) := by rw [h4]; ring

/-- **Halving recurrence** at `k = ⌈log₂ n⌉`: `T n + β 2 ^ ⌈log₂ n⌉ ≤ α a ^ ⌈log₂ n⌉`. -/
theorem add_mul_two_pow_clog_le_of_halving {T : ℕ → ℕ} {a c α β : ℕ}
    (ha : 1 ≤ a) (hc : 2 * c + 2 * β ≤ a * β)
    (base : ∀ n ≤ 1, T n + β ≤ α)
    (step : ∀ n, 2 ≤ n → ∀ S, (∀ m ≤ (n + 1) / 2, T m ≤ S) → T n ≤ a * S + c * n) (n : ℕ) :
    T n + β * 2 ^ Nat.clog 2 n ≤ α * a ^ Nat.clog 2 n :=
  add_mul_two_pow_le_mul_pow_of_halving ha hc base step _ n (Nat.le_pow_clog one_lt_two n)

private theorem two_pow_rpow_logb {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ Real.logb 2 a = (a : ℝ) ^ j := by
  rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast ha),
    Real.rpow_natCast]

private theorem logb_two_nonneg {a : ℕ} (ha : 1 ≤ a) : 0 ≤ Real.logb 2 (a : ℝ) :=
  Real.logb_nonneg one_lt_two (by exact_mod_cast ha)

/-- `a ^ ⌈log₂ n⌉ ≤ a n ^ log₂ a` for `n ≠ 0` and `a ≥ 1`. -/
theorem pow_clog_two_le_mul_rpow_logb {a n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) :
    ((a ^ Nat.clog 2 n : ℕ) : ℝ) ≤ a * (n : ℝ) ^ Real.logb 2 a := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp only [Nat.clog_one_right, pow_zero, Nat.cast_one, Real.one_rpow, mul_one]
    exact_mod_cast ha
  · set k := Nat.clog 2 n with hk
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.clog_pos one_lt_two h)
    have hlt : 2 ^ (k - 1) < n := by
      have := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < n)
      simpa [Nat.pred_eq_sub_one] using this
    have hmono : ((2 : ℝ) ^ (k - 1)) ^ Real.logb 2 a ≤ (n : ℝ) ^ Real.logb 2 a :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (logb_two_nonneg ha)
    have hsplit : k = (k - 1) + 1 := by omega
    calc ((a ^ k : ℕ) : ℝ) = (a : ℝ) * (a : ℝ) ^ (k - 1) := by
          rw [Nat.cast_pow, hsplit, pow_succ, Nat.add_sub_cancel, mul_comm]
      _ ≤ a * (n : ℝ) ^ Real.logb 2 a := by
          rw [← two_pow_rpow_logb ha]; gcongr

/-- `n ^ log₂ a ≤ a a ^ ⌊log₂ n⌋` for `a ≥ 1`, including `n = 0`. -/
theorem rpow_logb_le_mul_pow_log_two {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    (n : ℝ) ^ Real.logb 2 a ≤ a * (a : ℝ) ^ Nat.log 2 n := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, pow_zero, mul_one, Nat.cast_zero]
    exact (Real.zero_rpow_le_one _).trans ha'
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    calc (n : ℝ) ^ Real.logb 2 a ≤ ((2 : ℝ) ^ (Nat.log 2 n + 1)) ^ Real.logb 2 a :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (logb_two_nonneg ha)
      _ = a * (a : ℝ) ^ Nat.log 2 n := by rw [two_pow_rpow_logb ha, pow_succ, mul_comm]

end Nat
