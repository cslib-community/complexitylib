/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import Complexity.Foundations.Data.Nat.Bits

/-! # Total binary-number decoding

Binary digits are read least significant first. Trailing false symbols are ignored, including on
malformed words, and empty input returns zero. The decoder satisfies the encoding round-trip law
and has a certificate from direct plain machines.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace Decoder

/-- Binary numbers are decoded from their digits up to the last `true`. -/
def nat : Decoder encNat where
  decode := ofBits
  -- A tactic proof keeps the foundational binary-digit lemma a proof-only dependency.
  decode_enc n := by exact Nat.foldr_bit_bits n
  computable :=
    (ComputableInO.bitsToNat.computableInPolyTime
      (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
      (PolyBounded.of_forall_le 1 1 (fun _ => by simp))).exists_degree

end Decoder

/-- Decode every little-endian bit word, including noncanonical trailing false symbols. -/
@[fun_prop]
theorem ComputableInPolyTime.bitsToNat : ComputableInPolyTime ofBits encBits encNat :=
  Decoder.nat.computableInPolyTime

end Turing.MultiTapeTM
