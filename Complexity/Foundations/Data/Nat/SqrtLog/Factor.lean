/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Factors below `√(log n)`

Bounds on the scale `n / √⌊log₂ n⌋` that compare it with `n`, behind the separations of the counting
simulation at time `T · h` (#1833). The divisor `√⌊log₂ n⌋` tends to infinity
(`Nat.tendsto_sqrt_log_two_atTop`), so the scale is `o(n)`: every multiple `C * n` is eventually at
most `n * √⌊log₂ n⌋` (`Nat.eventually_mul_le_mul_sqrt_log_two`).

Multiplying `a` by a factor `b ≥ 1` keeps its scale below `a / C` as long as `C * b ≤ √⌊log₂ a⌋`
(`Nat.mul_mul_le_mul_sqrt_log_two_mul`). The fourth root `⌊√⌊√⌊log₂ n⌋⌋⌋` of the logarithm is such
a factor for every `C` from some `n` on (`Nat.eventually_mul_sqrt_sqrt_log_two_le`), and it is
positive from `n = 2` on (`Nat.one_le_sqrt_sqrt_log_two`).

## Main results

* `Nat.tendsto_sqrt_log_two_atTop`: `√⌊log₂ n⌋` tends to infinity.
* `Nat.eventually_mul_le_mul_sqrt_log_two`: `C * n ≤ n * √⌊log₂ n⌋` eventually.
* `Nat.mul_mul_le_mul_sqrt_log_two_mul`: `C * b ≤ √⌊log₂ a⌋` and `1 ≤ b` give
  `C * (a * b) ≤ a * √⌊log₂ (a * b)⌋`.
* `Nat.eventually_mul_sqrt_sqrt_log_two_le`: `C * ⌊√⌊√⌊log₂ n⌋⌋⌋ ≤ √⌊log₂ n⌋` eventually.
-/

public section

open Filter

namespace Nat

/-- The divisor `√⌊log₂ n⌋` tends to infinity. -/
theorem tendsto_sqrt_log_two_atTop : Tendsto (fun n => sqrt (log 2 n)) atTop atTop :=
  tendsto_atTop_atTop.2 fun C => ⟨2 ^ (C * C), fun _ hn =>
    le_sqrt.2 (le_log_of_pow_le one_lt_two hn)⟩

/-- **The scale `n / √⌊log₂ n⌋` is `o(n)`**: every multiple `C * n` is eventually at most
`n * √⌊log₂ n⌋`. -/
theorem eventually_mul_le_mul_sqrt_log_two (C : ℕ) :
    ∀ᶠ n in atTop, C * n ≤ n * sqrt (log 2 n) :=
  (tendsto_sqrt_log_two_atTop.eventually_ge_atTop C).mono fun n hn =>
    (Nat.mul_comm C n).trans_le (Nat.mul_le_mul_left n hn)

/-- **A factor below `√⌊log₂ a⌋ / C`**: if `b ≥ 1` and `C * b ≤ √⌊log₂ a⌋`, then
`C * (a * b) ≤ a * √⌊log₂ (a * b)⌋`, so the scale of `a * b` is at most `a / C`. -/
theorem mul_mul_le_mul_sqrt_log_two_mul {C a b : ℕ} (hb : 1 ≤ b) (h : C * b ≤ sqrt (log 2 a)) :
    C * (a * b) ≤ a * sqrt (log 2 (a * b)) :=
  calc C * (a * b) = a * (C * b) := by rw [Nat.mul_left_comm]
    _ ≤ a * sqrt (log 2 a) := Nat.mul_le_mul_left a h
    _ ≤ a * sqrt (log 2 (a * b)) :=
        Nat.mul_le_mul_left a (sqrt_log_two_mono (Nat.le_mul_of_pos_right a hb))

/-- The fourth root `⌊√⌊√⌊log₂ n⌋⌋⌋` of the logarithm is positive from `n = 2` on. -/
theorem one_le_sqrt_sqrt_log_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ sqrt (sqrt (log 2 n)) :=
  le_sqrt.2 ((Nat.one_mul 1).trans_le (one_le_sqrt_log_two hn))

/-- **The fourth root of the logarithm is `o(√log)`**: every multiple of `⌊√⌊√⌊log₂ n⌋⌋⌋` is
eventually at most `√⌊log₂ n⌋`. -/
theorem eventually_mul_sqrt_sqrt_log_two_le (C : ℕ) :
    ∀ᶠ n in atTop, C * sqrt (sqrt (log 2 n)) ≤ sqrt (log 2 n) :=
  (tendsto_sqrt_log_two_atTop.eventually_ge_atTop (C * C)).mono fun _ hn =>
    (Nat.mul_le_mul_right _ (le_sqrt.2 hn)).trans (sqrt_le _)

end Nat
