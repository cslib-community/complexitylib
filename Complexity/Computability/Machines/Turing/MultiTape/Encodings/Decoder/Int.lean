/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Total binary signed-integer decoding

Read a sign bit and a binary magnitude, normalizing negative zero. The actual decoder has
polynomial bit cost/output growth on every word and inverts every canonical integer encoding.
-/

public section

namespace Turing.MultiTapeTM.Decoder

/-- Sign-magnitude decoding; empty and noncanonical words have total normalized interpretations. -/
@[expose] def int : Decoder encIntBin where
  decode w := if w.headD false then -(nat.decode w.tail : ℤ) else nat.decode w.tail
  decode_enc z := by
    cases z with
    | ofNat n =>
      rw [show encIntBin (Int.ofNat n) = false :: encNat n from encIntBin_natCast n]
      simp only [ List.headD_cons, List.tail_cons, Bool.false_eq_true, ite_false]
      exact congrArg Int.ofNat (nat.decode_enc n)
    | negSucc n =>
      simp only [encIntBin_negSucc, List.headD_cons, List.tail_cons, ite_true]
      change -(nat.decode (encNat (n + 1)) : ℤ) = Int.negSucc n
      rw [nat.decode_enc]
      omega
  computable := by
    have hs := ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false
    have ht : ComputableInPolyTime List.tail encBits encBits :=
      .of_tidy ComputableTidilyInPolyTime.bitsTail
    have hm := nat.computableInPolyTime.comp ht
    exact ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_signMagnitude).comp
      (hs.prod hm)).exists_degree

end Turing.MultiTapeTM.Decoder
