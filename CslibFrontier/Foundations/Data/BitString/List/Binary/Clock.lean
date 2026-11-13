/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Tactic.Linarith

/-!
# Short binary clocks for exponential bounds

An all-ones word with `m + c₁ + c₂ + 1` bits exceeds `c₁ * 2 ^ m + c₂` numerically. Thus a
clock of linear word length can bound an exponential computation. The argument is extracted
from bounded-acceptance completeness so that bounded termination can reuse the same clock.

## Main results

* `Cslib.BitString.le_binaryValue_replicate_true`: affine-length binary clocks dominate
  exponential numerical budgets with arbitrary natural multiplicative and additive constants.
-/

public section

namespace Cslib.BitString

/-- An exponential bound has an all-ones binary clock whose length is affine in its exponent. -/
theorem le_binaryValue_replicate_true (m c₁ c₂ : ℕ) :
    c₁ * 2 ^ m + c₂ ≤ binaryValue (List.replicate (m + c₁ + c₂ + 1) true) := by
  have h₁ := binaryValue_replicate_true (m + (c₁ + c₂ + 1))
  have h₂ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h₃ : 2 ^ m * (c₁ + c₂ + 1) ≤ 2 ^ m * 2 ^ (c₁ + c₂ + 1) :=
    Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
  have h₄ : c₂ * 1 ≤ c₂ * 2 ^ m := Nat.mul_le_mul_left _ h₂
  rw [pow_add] at h₁
  simp only [Nat.add_assoc] at *
  nlinarith

end Cslib.BitString
