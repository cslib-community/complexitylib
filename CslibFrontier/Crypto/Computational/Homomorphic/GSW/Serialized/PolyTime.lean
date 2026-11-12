/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Serialized
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.PPT

/-!
# Uniform native computation of serialized GSW encryption

The actual word-valued encryption algorithm is polynomial-time uniformly in its unary dimensions
and binary residues, charging the complete public key, message, coins, and ciphertext words.

## Main results

* `computableInPolyTime_encryptEntry`, `computableInPolyTime_encryptWithCoinsSerialized`:
  actual deterministic public-word encryption.
* `isPPTOn_encryptSerialized`: strict PPT for the complete encryption program.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n m w i k j : α → ℕ}

/-- Compute a binary entry of the masked public matrix plus the message gadget. -/
@[fun_prop]
theorem computableInPolyTime_encryptEntry
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → SerializedCoins}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encSerializedCoins)
    (hi : ComputableInPolyTime i input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime
      (fun a => encryptEntry (n a) (m a) (w a) (publicWord a) (message a) (coins a)
        (i a) (k a) (j a)) input encNat := by
  unfold encryptEntry
  have hcoinsRow := (listGetD (encA := encBits) []).comp
    (((listGetD (encA := encList encBits) []).comp (hcoins.prod hi)).prod hk)
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ => if (((coins p.1).getD (i p.1) []).getD (k p.1) []).getD p.2 false
        then Matrix.binaryEntry (n p.1 + 1) (w p.1) (publicWord p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp
      ((hcoinsRow.comp (fst input encUnary)).prod (snd input encUnary))).ite'
    · exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (snd input encUnary) (by fun_prop)
    · exact const 0
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a r => if (((coins a).getD (i a) []).getD (k a) []).getD r false
        then Matrix.binaryEntry (n a + 1) (w a) (publicWord a) r (j a) else 0)
      (range.comp hm) hterm)
  have hboolUnary : ComputableInPolyTime Bool.toNat encBool encUnary := of_finite Bool.toNat
  have hgadget : ComputableInPolyTime
      (fun a => if i a = j a then (message a).toNat * 2 ^ k a else 0) input encNat := by
    simpa only [Function.comp_apply, beq_iff_eq] using (beq hi hj).ite'
      (binary_mul' (unary_to_binary.comp (hboolUnary.comp hmessage))
        (binary_pow' (const 2) hk)) (const 0)
  exact binary_mod.comp ((binary_add.comp (hgadget.prod hsum)).prod (binary_pow' (const 2) hw))

/-- Encrypt from arbitrary public words and coins, charging the complete ciphertext output. -/
@[fun_prop]
theorem computableInPolyTime_encryptWithCoinsSerialized
    {publicWord : α → List Bool} {message : α → Bool} {coins : α → SerializedCoins}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool)
    (hcoins : ComputableInPolyTime coins input encSerializedCoins) :
    ComputableInPolyTime
      (fun a => encryptWithCoinsSerialized (n a) (m a) (w a) (publicWord a) (message a) (coins a))
      input encBits := by
  unfold encryptWithCoinsSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

/-- The complete encryption program is strict PPT on arbitrary public words and messages. -/
@[fun_prop]
theorem isPPTOn_encryptSerialized {publicWord : α → List Bool} {message : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hpublicWord : ComputableInPolyTime publicWord input encBits)
    (hmessage : ComputableInPolyTime message input encBool) :
    IsPPTOn input encBits
      (fun a => encryptSerialized (n a) (m a) (w a) (publicWord a) (message a)) := by
  have hsample := isPPTOn_sampleCoinsSerialized hn hm hw
  unfold encryptSerialized
  ppt

end Cslib.Crypto.Homomorphic.GSW
