/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import Mathlib.Data.List.DropRight
import Complexity.Foundations.Data.List.Append
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-! # Total binary-number decoding

Binary digits are read least significant first. Trailing false symbols are ignored, including on
malformed words, and empty input returns zero. The decoder satisfies the encoding round-trip law
and has a certificate from direct plain machines.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-! ### Binary digits -/

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

namespace Decoder

/-- Binary numbers are decoded from their digits up to the last `true`. -/
def nat : Decoder encNat where
  decode := ofBits
  -- A tactic proof keeps the foundational binary-digit lemma a proof-only dependency.
  decode_enc n := by exact Nat.foldr_bit_bits n
  computable := by
    have hd : ComputableInPolyTime (fun w : List Bool => w.dropWhile (!·)) encBits encBits := by
      refine ⟨fun n => 2 * n + 3, fun _ => 0, by fun_prop, by fun_prop,
        0, _, inferInstance, dropFalsesT.toTM, fun w => ?_⟩
      simpa only [show dropFalsesT.q₀ = false from rfl, dropFalsesT_run,
        encBits, Function.Embedding.refl_apply] using
        dropFalsesT.computesInTimeAndSpace_toTM w
    have h : ComputableInPolyTime (fun w : List Bool => (w.reverse.dropWhile (!·)).reverse)
        encBits encBits := by
      fun_prop
    exact (h.of_enc_eq fun w => by rw [encNat_apply, bits_ofBits]; rfl).exists_degree

end Decoder

/-- Decode every little-endian bit word, including noncanonical trailing false symbols. -/
@[fun_prop]
theorem ComputableInPolyTime.bitsToNat : ComputableInPolyTime ofBits encBits encNat :=
  Decoder.nat.computableInPolyTime

end Turing.MultiTapeTM
