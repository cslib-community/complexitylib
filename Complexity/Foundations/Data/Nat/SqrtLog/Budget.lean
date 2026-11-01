/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

/-!
# An explicit budget for the shifted square-root-logarithm scale

Write `q(n) = Nat.sqrt (Nat.log 2 (n + 2))`. A size bound of
`3 * (n * q(n) / (12 * (A + 1))) + D * (n + 1) + n` permits three copies of a circuit
of size `n * q(n) / (12 * (A + 1))` and linear additional work. For any padded size `M`
between `n` and this bound, the shifted exponent `A * (M + 1) / q(M)` is at most `n / 2`
once `q(n) ≥ 8 * A * (D + 1)`.

These are natural-number inequalities, including every division and square-root rounding.
They provide the arithmetic for transferring the quantitative counting bound to a circuit
lower bound; they do not assert a complexity-class separation. The coefficient `A` remains
an explicit parameter. The overhead coefficient `D` affects the starting length, not the
coefficient `12 * (A + 1)` in the circuit-size budget.

## Main results

* `Nat.two_mul_mul_succ_div_sqrt_log_two_le`: twice the shifted exponent is at most `n`
  under an explicit lower bound on `q(n)`.
* `Nat.two_mul_mul_succ_div_sqrt_log_two_le_of_pow_le`: the same conclusion once
  `2 ^ ((8 * A * (D + 1)) ^ 2) ≤ n + 2`.
-/

public section

namespace Nat

/-- **An explicit size budget.** Three copies of a circuit with at most
`n * √⌊log₂ (n + 2)⌋ / (12 * (A + 1))` gates, plus linear overhead, give a shifted
exponent at most `n / 2`. The tested size is padded to be at least `n`. -/
theorem two_mul_mul_succ_div_sqrt_log_two_le {A D n M : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ M)
    (hM : M ≤ 3 * (n * sqrt (log 2 (n + 2)) / (12 * (A + 1))) + D * (n + 1) + n)
    (hq : 8 * A * (D + 1) ≤ sqrt (log 2 (n + 2))) :
    2 * (A * (M + 1) / sqrt (log 2 (M + 2))) ≤ n := by
  set q := sqrt (log 2 (n + 2))
  set s := n * q / (12 * (A + 1))
  have hs : 12 * (A + 1) * s ≤ n * q := by
    simpa only [s, mul_comm] using div_mul_le_self (n * q) (12 * (A + 1))
  have hDn : D ≤ D * n := Nat.le_mul_of_pos_right D hn
  have hM' : M + 1 ≤ 3 * s + (2 * D + 2) * n := by
    change M ≤ 3 * s + D * (n + 1) + n at hM
    nlinarith
  have hqn : 8 * A * (D + 1) * n ≤ n * q := by
    simpa only [mul_comm] using Nat.mul_le_mul_left n hq
  have hnum : 2 * (A * (M + 1)) ≤ n * q := by
    nlinarith [Nat.mul_le_mul_left (4 * A) hM']
  have hmono : q ≤ sqrt (log 2 (M + 2)) :=
    sqrt_log_two_mono (Nat.add_le_add_right hnM 2)
  calc
    2 * (A * (M + 1) / sqrt (log 2 (M + 2)))
        ≤ 2 * (A * (M + 1)) / sqrt (log 2 (M + 2)) :=
      mul_div_le_mul_div_assoc _ _ _
    _ ≤ n := Nat.div_le_of_le_mul (by
      calc
        2 * (A * (M + 1)) ≤ n * q := hnum
        _ ≤ n * sqrt (log 2 (M + 2)) := Nat.mul_le_mul_left n hmono
        _ = sqrt (log 2 (M + 2)) * n := mul_comm _ _)

/-- The size-budget inequality has the explicit starting-length condition
`2 ^ ((8 * A * (D + 1)) ^ 2) ≤ n + 2`. -/
theorem two_mul_mul_succ_div_sqrt_log_two_le_of_pow_le {A D n M : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ M)
    (hM : M ≤ 3 * (n * sqrt (log 2 (n + 2)) / (12 * (A + 1))) + D * (n + 1) + n)
    (hpow : 2 ^ ((8 * A * (D + 1)) ^ 2) ≤ n + 2) :
    2 * (A * (M + 1) / sqrt (log 2 (M + 2))) ≤ n := by
  apply two_mul_mul_succ_div_sqrt_log_two_le hn hnM hM
  exact le_sqrt'.2 (le_log_of_pow_le one_lt_two hpow)

end Nat
