/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Foundations.Data.Rat.BinarySize
import Mathlib.Tactic

/-!
# Canonical binary rational encoding

A rational is encoded as its reduced signed numerator paired with its positive
denominator. The first field uses `encIntBin`, the second uses `encNat`, and
`encPair` supplies unambiguous framing. This is a binary encoding, not a unary
encoding of the magnitudes. Validity and reduction proofs are not input fields.

## Main results

* `length_encRatBin`: exact encoded length.
* `binaryWidth_le_length_encRatBin`: each operand magnitude fits in the encoded word.
* `length_encRatBin_le`: linear overhead over the maximum operand width.
-/

public section
namespace Turing.MultiTapeTM

/-- Reduced signed binary numerator paired with the positive binary denominator. -/
@[expose] def encRatBin : ℚ ↪ List Bool :=
  (⟨fun q => (q.num,q.den), fun q r h => by
    have hn : q.num = r.num := congrArg Prod.fst h
    have hd : q.den = r.den := congrArg Prod.snd h
    rw [← q.num_divInt_den, ← r.num_divInt_den, hn, hd]⟩ : ℚ ↪ ℤ × ℕ).trans
      (encPair encIntBin encNat)

/-- Exact length including sign and pair framing. -/
theorem length_encRatBin (q : ℚ) :
    (encRatBin q).length = 2 * q.num.natAbs.size + q.den.size + 3 := by
  change (encPair encIntBin encNat (q.num,q.den)).length = _
  rw [length_encPair, length_encIntBin]
  simp only [encNat_apply, ← Nat.size_eq_bits_len]
  omega

/-- Both magnitude fields are bounded by the complete encoded length. -/
theorem binaryWidth_le_length_encRatBin (q : ℚ) :
    q.binaryWidth ≤ (encRatBin q).length := by
  rw [length_encRatBin]
  unfold Rat.binaryWidth
  omega

/-- Framing and sign add only linear overhead. -/
theorem length_encRatBin_le (q : ℚ) :
    (encRatBin q).length ≤ 3 * q.binaryWidth + 3 := by
  rw [length_encRatBin]
  unfold Rat.binaryWidth
  omega

end Turing.MultiTapeTM
