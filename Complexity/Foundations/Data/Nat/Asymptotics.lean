/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/Asymptotics.lean`)

public import Complexity.Init
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-!
# Further asymptotic bounds on natural numbers

For any natural base `b > 1`, `Nat.log b` tends to infinity at infinity (`Nat.tendsto_log_atTop`),
every affine function of a shifted logarithm `a + c * log b (n + d)` is eventually at most `n`
(`Nat.eventually_add_mul_log_add_le`), and every fixed multiple of `(n + 1) ^ k` is eventually at
most `b ^ n` (`Nat.eventually_mul_add_one_pow_le_pow`) and at most `b ^ (n / m)` for `m > 0`
(`Nat.eventually_mul_add_one_pow_le_pow_div`).

## Main results

* `Nat.tendsto_log_atTop`: `Tendsto (Nat.log b) atTop atTop` for `1 < b`.
* `Nat.eventually_le_log`: `∀ᶠ n in atTop, k ≤ Nat.log b n` for `1 < b`.
* `Nat.eventually_add_mul_log_add_le`: `∀ᶠ n in atTop, a + c * Nat.log b (n + d) ≤ n` for `1 < b`.
* `Nat.eventually_add_mul_log_le`: `∀ᶠ n in atTop, a + c * Nat.log b n ≤ n` for `1 < b`.
* `Nat.eventually_mul_add_one_pow_le_pow_div`:
  `∀ᶠ n in atTop, c * (n + 1) ^ k ≤ b ^ (n / m)` for `1 < b` and `0 < m`.
* `Nat.eventually_mul_add_one_pow_le_pow`: `∀ᶠ n in atTop, c * (n + 1) ^ k ≤ b ^ n` for `1 < b`.
* `Nat.eventually_mul_pow_le_pow_div`:
  `∀ᶠ n in atTop, c * n ^ k ≤ b ^ (n / m)` for `1 < b` and `0 < m`.
* `Nat.eventually_add_one_pow_mul_lt_pow`:
  `∀ᶠ n in atTop, (n + 1) ^ k * n < b ^ n` for `1 < b`.
-/

@[expose] public section

open Filter

namespace Nat

/-- The base-`b` logarithm tends to infinity for `1 < b`. -/
theorem tendsto_log_atTop {b : ℕ} (hb : 1 < b) : Tendsto (log b) atTop atTop :=
  tendsto_atTop_atTop.2 fun k => ⟨b ^ k, fun _ hN => le_log_of_pow_le hb hN⟩

/-- Every constant is eventually at most `log b n` for `1 < b`. -/
theorem eventually_le_log (k : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, k ≤ log b n :=
  (tendsto_log_atTop hb).eventually_ge_atTop k

/-- Every affine function of a shifted logarithm `a + c * log b (n + d)` is eventually at most
`n` for `1 < b`. -/
theorem eventually_add_mul_log_add_le (a c d : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, a + c * log b (n + d) ≤ n := by
  filter_upwards [eventually_mul_log_le (c + 1) hb,
    eventually_ge_atTop (max d (b ^ (a + c)))] with n hlog hn
  have hnd : d ≤ n := le_of_max_le_left hn
  have hpow : b ^ (a + c) ≤ n := le_of_max_le_right hn
  have hn0 : 0 < n := (Nat.pow_pos (by omega)).trans_le hpow
  have hac : a + c ≤ log b n := le_log_of_pow_le hb hpow
  have hlog_add : log b (n + d) ≤ log b n + 1 := by
    calc log b (n + d) ≤ log b (n * b) := log_mono_right (by nlinarith)
      _ = log b n + 1 := log_mul_base hb hn0.ne'
  nlinarith

/-- Every affine function `a + c * log b n` is eventually at most `n` for `1 < b`. -/
theorem eventually_add_mul_log_le (a c : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, a + c * log b n ≤ n := by
  simpa only [add_zero] using eventually_add_mul_log_add_le a c 0 hb

/-- Every fixed multiple of `(n + 1) ^ k` is eventually at most `b ^ (n / m)` for `1 < b`
and `0 < m`. -/
theorem eventually_mul_add_one_pow_le_pow_div (c k m : ℕ) {b : ℕ} (hb : 1 < b) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, c * (n + 1) ^ k ≤ b ^ (n / m) := by
  have htend : Tendsto (fun n : ℕ => n / m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun j => ⟨m * j, fun n hn =>
      (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hn)⟩
  filter_upwards [htend.eventually (eventually_mul_pow_le_pow (c * (2 * m) ^ k) k hb),
    eventually_ge_atTop m] with n hn hmn
  have hk : n + 1 ≤ 2 * m * (n / m) := by
    have := Nat.lt_mul_div_succ n hm
    have : 1 ≤ n / m := (Nat.le_div_iff_mul_le hm).mpr (by omega)
    nlinarith
  calc c * (n + 1) ^ k ≤ c * (2 * m * (n / m)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk k)
    _ = c * (2 * m) ^ k * (n / m) ^ k := by rw [mul_pow, mul_assoc]
    _ ≤ b ^ (n / m) := hn

/-- Every fixed multiple of `(n + 1) ^ k` is eventually at most `b ^ n` for `1 < b`. -/
theorem eventually_mul_add_one_pow_le_pow (c k : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, c * (n + 1) ^ k ≤ b ^ n := by
  simpa only [Nat.div_one] using eventually_mul_add_one_pow_le_pow_div c k 1 hb one_pos

/-- Every fixed multiple of `n ^ k` is eventually at most `b ^ (n / m)` for `1 < b` and `0 < m`. -/
theorem eventually_mul_pow_le_pow_div (c k m : ℕ) {b : ℕ} (hb : 1 < b) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, c * n ^ k ≤ b ^ (n / m) :=
  (eventually_mul_add_one_pow_le_pow_div c k m hb hm).mono fun n =>
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.le_succ n) k)).trans

/-- Every `(n + 1) ^ k * n` is eventually strictly below `b ^ n` for `1 < b`. -/
theorem eventually_add_one_pow_mul_lt_pow (k : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, (n + 1) ^ k * n < b ^ n := by
  filter_upwards [eventually_mul_add_one_pow_le_pow 1 (k + 1) hb] with n hn
  have hlt : (n + 1) ^ k * n < 1 * (n + 1) ^ (k + 1) := by
    rw [one_mul, pow_succ]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) (Nat.pow_pos n.succ_pos)
  exact hlt.trans_le hn

end Nat
