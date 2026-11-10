/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Halving recurrences

A cost `T` with `T n ≤ a T(⌈n/2⌉) + c n` for `n ≥ 2` grows like `a ^ ⌈log₂ n⌉`. The
substitution method proves this exactly, with a subtracted linear term
(`Nat.add_mul_two_pow_le_mul_pow_of_halving`). Assume

* `1 ≤ a` and the slack condition `2 c + 2 β ≤ a β`;
* the base case `T n + β ≤ α` for every `n ≤ 1`;
* the step: for every `n ≥ 2` and every `S`, if `T m ≤ S` for all `m ≤ (n + 1) / 2`, then
  `T n ≤ a S + c n`.

Then `T n + β 2 ^ k ≤ α a ^ k` for all `k` and `n ≤ 2 ^ k`. Because the step only uses a common
bound `S` on all sizes up to `⌈n/2⌉`, recurrences that split `n` into `⌊n/2⌋` and `⌈n/2⌉`, or
that are not monotone, are covered directly. `Nat.pow_clog_two_le_mul_rpow_logb` in
`CslibFrontier.Foundations.Data.Nat.LogTwoRpow` converts `a ^ ⌈log₂ n⌉` to `n ^ log₂ a`.

## Main results

* `Nat.add_mul_two_pow_le_mul_pow_of_halving`: the halving recurrence at a power of two.
* `Nat.add_mul_two_pow_clog_le_of_halving`: the same at `k = ⌈log₂ n⌉`.

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

end Nat
