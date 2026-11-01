/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The scale `n / √(log n)` under linear bounds

Two estimates that transfer bounds in a derived size `L ≤ c₁ T + c₂`, such as the number of gates
of a circuit, to the scale `T / √⌊log₂ T⌋` of a time bound `T ≥ 2`: the shifted scale
`A (L + 1) / √⌊log₂ (L + 2)⌋` is at most a constant times `T / √⌊log₂ T⌋` plus a constant
(`Nat.mul_succ_div_sqrt_log_two_le_of_le`), and a polynomial `(n + 1) ^ e` in `n ≤ T` is at most
`2 ^ (2 e T / √⌊log₂ T⌋)` (`Nat.add_one_pow_le_two_pow_div_sqrt_log_two`).

## Main results

* `Nat.mul_succ_div_sqrt_log_two_le_of_le`: the shifted scale under a linear bound.
* `Nat.add_one_pow_le_two_pow_div_sqrt_log_two`: polynomials are absorbed by the exponential scale.
-/

public section

namespace Nat

/-- **The shifted scale under a linear bound.** If `L ≤ c₁ T + c₂` and `2 ≤ T`, then
`A (L + 1) / √⌊log₂ (L + 2)⌋` is at most a constant times `T / √⌊log₂ T⌋`, plus a constant. -/
theorem mul_succ_div_sqrt_log_two_le_of_le (A c₁ c₂ : ℕ) {T L : ℕ} (hT : 2 ≤ T)
    (hL : L ≤ c₁ * T + c₂) :
    A * (L + 1) / Nat.sqrt (Nat.log 2 (L + 2)) ≤
      2 * A * (c₁ + c₂ + 2) * (T / Nat.sqrt (Nat.log 2 T)) + (2 * A * (c₁ + c₂ + 2) + 3 * A) := by
  have hM : L + 2 ≤ (c₁ + c₂ + 2) * T := by nlinarith
  calc A * (L + 1) / Nat.sqrt (Nat.log 2 (L + 2))
      ≤ A * (L + 2) / Nat.sqrt (Nat.log 2 (L + 2)) :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    _ ≤ A * ((L + 2) / Nat.sqrt (Nat.log 2 (L + 2))) + A := Nat.mul_div_le_mul_div_add _ _ _
    _ ≤ A * (2 * ((c₁ + c₂ + 2) * T / Nat.sqrt (Nat.log 2 ((c₁ + c₂ + 2) * T))) + 2) + A := by
        gcongr
        exact Nat.div_sqrt_log_two_le_of_le hM
    _ ≤ A * (2 * ((c₁ + c₂ + 2) * (T / Nat.sqrt (Nat.log 2 T)) + (c₁ + c₂ + 2)) + 2) + A := by
        gcongr
        exact Nat.mul_div_sqrt_log_two_le _ T
    _ = _ := by ring

/-- A polynomial in `n + 1 ≤ T + 1` is at most `2 ^ (2 e T / √⌊log₂ T⌋)`. -/
theorem add_one_pow_le_two_pow_div_sqrt_log_two {n T : ℕ} (e : ℕ) (hT : 2 ≤ T) (hn : n ≤ T) :
    (n + 1) ^ e ≤ 2 ^ (2 * e * (T / Nat.sqrt (Nat.log 2 T))) := by
  have h1 := Nat.one_le_div_sqrt_log_two hT
  have h2 := Nat.log_two_le_div_sqrt_log_two T
  calc (n + 1) ^ e ≤ (2 ^ (Nat.log 2 T + 1)) ^ e :=
        Nat.pow_le_pow_left ((Nat.succ_le_succ hn).trans (Nat.lt_pow_succ_log_self one_lt_two T)) e
    _ = 2 ^ (e * (Nat.log 2 T + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end Nat
