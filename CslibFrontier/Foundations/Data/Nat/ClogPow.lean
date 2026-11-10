/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Log.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Logarithmic exponents give polynomial powers

A word width of `c * ⌈log₂ m⌉` bits has a word universe of size `2 ^ (c * ⌈log₂ m⌉)`. Since
`2 ^ ⌈log₂ m⌉ ≤ 2 m ≤ m ^ 2` for `m ≠ 0`, that universe is at most `m ^ e` for every `e ≥ 2 c`
(`Nat.two_pow_mul_clog_le_pow`). This is the step that turns a logarithmic width bound into a
polynomial bound on every word value.

## Main results

* `Nat.two_pow_clog_le_sq`: `2 ^ ⌈log₂ m⌉ ≤ m ^ 2` for `m ≠ 0`.
* `Nat.two_pow_mul_clog_le_pow`: `2 ^ (c ⌈log₂ m⌉) ≤ m ^ e` for `m ≠ 0` and `2 c ≤ e`.
-/

public section

namespace Nat

/-- `2 ^ ⌈log₂ m⌉ ≤ m ^ 2` for `m ≠ 0`. -/
theorem two_pow_clog_le_sq {m : ℕ} (hm : m ≠ 0) : 2 ^ clog 2 m ≤ m ^ 2 := by
  rcases (one_le_iff_ne_zero.2 hm).eq_or_lt with rfl | h1
  · simp
  · calc 2 ^ clog 2 m ≤ 2 * m := pow_clog_le_mul Nat.one_lt_two hm
      _ ≤ m * m := Nat.mul_le_mul_right m h1
      _ = m ^ 2 := (Nat.pow_two m).symm

/-- A width of `c * ⌈log₂ m⌉` bits has a polynomial word universe:
`2 ^ (c ⌈log₂ m⌉) ≤ m ^ e` for `m ≠ 0` and `2 c ≤ e`. -/
theorem two_pow_mul_clog_le_pow {c e m : ℕ} (hm : m ≠ 0) (he : 2 * c ≤ e) :
    2 ^ (c * clog 2 m) ≤ m ^ e :=
  calc 2 ^ (c * clog 2 m) = (2 ^ clog 2 m) ^ c := by rw [Nat.mul_comm, Nat.pow_mul]
    _ ≤ (m ^ 2) ^ c := Nat.pow_le_pow_left (two_pow_clog_le_sq hm) c
    _ = m ^ (2 * c) := by rw [← Nat.pow_mul]
    _ ≤ m ^ e := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm) he

end Nat
