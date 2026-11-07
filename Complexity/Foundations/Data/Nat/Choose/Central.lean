/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Nat/Choose/Central.lean`)

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An upper bound on the central binomial coefficient

`C(2n, n) ^ 2 (2n + 1) ≤ 16 ^ n`, that is `C(2n, n) ≤ 4 ^ n / √(2n + 1)`
(`Nat.centralBinom_sq_mul_le`). Mathlib's `Nat.four_pow_le_two_mul_add_one_mul_centralBinom` is the
matching lower bound `4 ^ n ≤ (2n + 1) C(2n, n)`.

## Main results

* `Nat.centralBinom_sq_mul_le`: `C(2n, n) ^ 2 (2n + 1) ≤ 16 ^ n`.
-/

public section

namespace Nat

/-- `C(2n, n) ^ 2 (2n + 1) ≤ 16 ^ n`: the product of the ratios `(2k - 1) / (2k)` is at most
`1 / √(2n + 1)`. -/
theorem centralBinom_sq_mul_le (n : ℕ) : n.centralBinom ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    refine Nat.le_of_mul_le_mul_left (c := (n + 1) ^ 2) ?_ (by positivity)
    calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1))
        = ((n + 1) * (n + 1).centralBinom) ^ 2 * (2 * n + 3) := by ring
      _ = 4 * (2 * n + 1) * n.centralBinom ^ 2 * ((2 * n + 1) * (2 * n + 3)) := by rw [h]; ring
      _ ≤ 4 * (2 * n + 1) * n.centralBinom ^ 2 * (4 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = 16 * (n + 1) ^ 2 * (n.centralBinom ^ 2 * (2 * n + 1)) := by ring
      _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring

end Nat
