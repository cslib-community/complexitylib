/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Data/Nat/Defs.lean`)

public import Complexity.Init
import Batteries.Data.Nat.Lemmas

/-!
# Packing numbers into fields

A low field `x < m` and a high field `y` are packed into the number `x + m * y`. Reducing modulo
`m` recovers `x` (`Nat.add_mul_mod_of_lt`), and dividing by `m` recovers `y`
(`Nat.add_mul_div_left_of_lt`). For fields of `a` and `b` bits, the packed number has `a + b` bits
(`Nat.add_two_pow_mul_lt`). Packing a packed number again as the high field gives any fixed number
of fields, which these facts decode one at a time.

## Main results

* `Nat.add_mul_mod_of_lt`, `Nat.add_mul_div_left_of_lt`: decoding the two fields.
* `Nat.add_two_pow_mul_lt`: fields of `a` and `b` bits fit in `a + b` bits.
-/

@[expose] public section

namespace Nat

/-- Reducing the packed number `x + m * y` modulo `m` gives the low field `x < m`. -/
theorem add_mul_mod_of_lt {x m : ℕ} (y : ℕ) (hx : x < m) : (x + m * y) % m = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- Dividing the packed number `x + m * y` by `m` gives the high field `y`, for `x < m`. -/
theorem add_mul_div_left_of_lt {x m : ℕ} (y : ℕ) (hx : x < m) : (x + m * y) / m = y := by
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hx), Nat.div_eq_of_lt hx, Nat.zero_add]

/-- Fields `x < 2 ^ a` and `y < 2 ^ b` pack into a number `x + 2 ^ a * y` of `a + b` bits. -/
theorem add_two_pow_mul_lt {a b x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    x + 2 ^ a * y < 2 ^ (a + b) := by
  rw [Nat.pow_add]
  exact Nat.add_mul_lt_mul_of_lt_of_lt hx hy

end Nat
