/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Mathlib.Data.List.DropRight
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.BitString.Counter
import Complexity.Foundations.Data.List.Append
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Reading arbitrary little-endian natural-number words

The existing word interpretation and normalization identity are independent of machine or
complexity certificates. Trailing false symbols are ignored, and the empty word represents zero.

## Main definitions

* `Turing.MultiTapeTM.ofBits`: read little-endian digits as a natural number.

## Main results

* `Turing.MultiTapeTM.bits_ofBits`: normalize a word by removing its trailing false symbols.
* `Turing.MultiTapeTM.bits_add_two_pow`: the binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are
  the `W` low-order digits of `x` (`Cslib.BitString.lowBits`) followed by a one.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- Binary digits, least significant first, read as a number. -/
def ofBits (w : List Bool) : ℕ := w.foldr Nat.bit 0

/-- The binary digits of a word read as a number are the word up to its last `true`. -/
theorem bits_ofBits (w : List Bool) : (ofBits w).bits = w.rdropWhile (!·) := by
  induction w with
  | nil => simp [ofBits]
  | cons b w ih =>
    rw [ofBits, List.foldr_cons, ← ofBits, ← List.singleton_append, List.rdropWhile_append, ← ih]
    by_cases h : ofBits w = 0 ∧ b = false
    · obtain ⟨h₀, rfl⟩ := h
      simp [h₀]
    · rw [Nat.bits_append_bit _ _ fun h₀ => by simpa [h₀] using h]
      by_cases h₀ : ofBits w = 0
      · obtain rfl : b = true := by simpa [h₀] using h
        simp [h₀, List.rdropWhile_singleton]
      · simp only [Nat.bits_eq_nil_iff, h₀, ↓reduceIte]
        rfl

/-- A trailing one adds `2 ^ |w|` to the value of a word. -/
private theorem foldr_bit_one_eq (w : List Bool) :
    w.foldr Nat.bit 1 = w.foldr Nat.bit 0 + 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, Nat.bit_val, Nat.bit_val, List.length_cons, pow_succ]
    omega

/-- The binary digits of `x + 2 ^ W`, for `x < 2 ^ W`, are the `W` low-order digits of `x`,
followed by a one. -/
theorem bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits = Cslib.BitString.lowBits W x ++ [true] := by
  have h := foldr_bit_one_eq (Cslib.BitString.lowBits W x)
  rw [← Cslib.BitString.lsbValue_eq_foldr_bit, Cslib.BitString.lsbValue_lowBits hx,
    Cslib.BitString.length_lowBits] at h
  rw [← h, Nat.bits_foldr_bit_one]

/-- The `W` low-order digits of `x < 2 ^ W` are `(x + 2 ^ W).bits` without its last digit. -/
theorem dropLast_bits_add_two_pow {W x : ℕ} (hx : x < 2 ^ W) :
    (x + 2 ^ W).bits.dropLast = Cslib.BitString.lowBits W x := by
  rw [bits_add_two_pow hx, List.dropLast_concat]

end Turing.MultiTapeTM
