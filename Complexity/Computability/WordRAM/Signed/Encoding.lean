/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Signed
public import Complexity.Computability.WordRAM.Defs

/-!
# Signed integers encoded in unsigned words

An integer is stored as twice its magnitude plus a low sign bit. Zero has sign bit zero;
the natural number one is not a canonical encoding. Unlike two's complement, this encoding
does not depend on the word width. A signed `w`-bit integer, including `-2^(w-1)`, fits in
one unsigned word of `w + 1` bits. The signed range is the existing `GenericRAM.Signed.Fits`.

## Main definitions

* `Signed.encode`, `Signed.decode`: the sign-and-magnitude representation and its interpretation.

## Main results

* `Signed.decode_encode`: encoding preserves the integer.
* `Signed.encode_fits`: one additional unsigned bit suffices for every signed input.

## References

This representation and the bounds below are an original implementation choice, not a
formalization of a cited algorithm.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

/-- Twice the magnitude, with the low bit set exactly for negative integers. -/
def encode (z : ℤ) : ℕ := 2 * z.natAbs + if z < 0 then 1 else 0

/-- Interpret the low bit as a sign and the remaining bits as a magnitude. -/
def decode (v : ℕ) : ℤ := if v % 2 = 0 then (v / 2 : ℕ) else -(v / 2 : ℕ)

/-- The magnitude can be read by unsigned division by two. -/
@[simp]
theorem encode_div_two (z : ℤ) : encode z / 2 = z.natAbs := by
  unfold encode
  split_ifs <;> omega

/-- The low bit is the sign. -/
@[simp]
theorem encode_mod_two (z : ℤ) : encode z % 2 = if z < 0 then 1 else 0 := by
  unfold encode
  split_ifs <;> omega

/-- Decoding an encoded integer returns that integer, including at zero. -/
@[simp]
theorem decode_encode (z : ℤ) : decode (encode z) = z := by
  by_cases hz : z < 0
  · simp [decode, hz, Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)]
  · simp [decode, hz, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ z)]

/-- Different integers have different encoded words. -/
theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

/-- Every signed `w`-bit integer fits in one unsigned word with one extra bit. -/
theorem encode_fits {w : ℕ} {z : ℤ} (h : GenericRAM.Signed.Fits w z) :
    Fits (w + 1) (encode z) := by
  have hm := h.natAbs_le
  have hw0 := h.1
  have hp : 2 ^ (w + 1) = 4 * 2 ^ (w - 1) := by
    have hw : w + 1 = (w - 1) + 2 := by omega
    rw [hw, pow_add]
    omega
  have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
  unfold Fits encode
  split_ifs <;> omega

end Cslib.WordRAM.Signed
