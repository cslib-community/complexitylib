/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Log.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log

/-!
# Ceiling logarithms of powers

Encoding an `m`-tuple over an alphabet of size `n` in base `b` uses `⌈log_b (n ^ m)⌉` digits, which
is at most `m · ⌈log_b n⌉` (`Nat.clog_pow_le_mul`), the cost of encoding each coordinate separately.

## Main results

* `Nat.clog_pow_le_mul`: `⌈log_b (n ^ m)⌉ ≤ m · ⌈log_b n⌉`.
-/

public section

namespace Nat

/-- Ceiling logarithm of an `m`-th power: `⌈log_b (n ^ m)⌉ ≤ m · ⌈log_b n⌉`. -/
theorem clog_pow_le_mul (b n m : ℕ) : clog b (n ^ m) ≤ m * clog b n := by
  rcases le_or_gt b 1 with hb | hb
  · rw [clog_of_left_le_one hb, clog_of_left_le_one hb, Nat.mul_zero]
  · refine clog_le_of_le_pow ?_
    calc n ^ m ≤ (b ^ clog b n) ^ m := Nat.pow_le_pow_left (le_pow_clog hb n) m
      _ = b ^ (m * clog b n) := by rw [← Nat.pow_mul, Nat.mul_comm]

end Nat
