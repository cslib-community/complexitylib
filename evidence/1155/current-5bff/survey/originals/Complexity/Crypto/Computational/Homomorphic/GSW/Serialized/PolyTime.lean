/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PPT

/-!
# Uniform native computation of serialized GSW keys and ciphertexts

The actual word-valued algorithms are polynomial-time uniformly in their unary dimensions,
binary residues and signed binary errors. No shape or canonical-input assumption is needed:
defaulted lookup and signed remainder specify the behavior on arbitrary inputs. The certificates
charge the complete public key, secret and ciphertext words, as well as all intermediate list
framing. They do not use a fixed-dimensional finite-type encoding to obtain efficiency.

## Main results

* `computableInPolyTime_publicMatrixSerialized`,
  `computableInPolyTime_secretSerialized`: actual deterministic key construction.
* `computableInPolyTime_encryptWithCoinsSerialized`: actual public-word encryption.
* `isPPTOn_keyGenSerialized`, `isPPTOn_encryptSerialized`: strict PPT for the complete programs,
  composing the existing independent input samplers with the deterministic computations.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n m w η i k j : α → ℕ}

/-- Compute a public row's leading residue from arbitrary binary inputs and signed errors. -/
@[fun_prop]
theorem computableInPolyTime_publicRowHead {inputs : α → SerializedKeyInputs}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => publicRowHead (n a) (w a) (inputs a) (i a))
      input encNat := by
  have hn := hn.tidy
  have hw := hw.tidy
  have hinputs := hinputs.tidy
  have hi := hi.tidy
  refine .of_tidy ?_
  unfold publicRowHead
  have hrow := (listGetD (encA := encList encNat) []).comp (hinputs.snd'.fst'.prod hi)
  have hproduct : ComputableTidilyInPolyTime
      (fun p : α × ℕ => ((inputs p.1).2.1.getD (i p.1) []).getD p.2 0 *
        (inputs p.1).1.getD p.2 0) (encPair input encUnary) encNat := by
    apply binary_mul'
    · exact (listGetD (encA := encNat) 0).comp
        ((hrow.comp (fst input encUnary)).prod (snd input encUnary))
    · exact (listGetD (encA := encNat) 0).comp
        ((hinputs.fst'.comp (fst input encUnary)).prod (snd input encUnary))
  have hsum := binary_sum.comp (mapWithInput
    (f := fun a j => ((inputs a).2.1.getD (i a) []).getD j 0 * (inputs a).1.getD j 0)
    (range.comp hn) hproduct)
  have herror := (listGetD (encA := encIntBin) 0).comp (hinputs.snd'.snd'.prod hi)
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    intBin_emodNat' (intBin_add' (intBin_natCast.comp hsum) herror) (binary_pow' (const 2) hw)

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Construct the entire public word, charging the runtime number and width of every entry. -/
@[fun_prop]
theorem computableInPolyTime_publicMatrixSerialized {inputs : α → SerializedKeyInputs}
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hinputs : ComputableInPolyTime inputs input encSerializedKeyInputs) :
    ComputableInPolyTime
      (fun a => publicMatrixSerialized (n a) (m a) (w a) (inputs a)) input encBits := by
  have hn := hn.tidy
  have hm := hm.tidy
  have hw := hw.tidy
  have hinputs := hinputs.tidy
  refine .of_tidy ?_
  unfold publicMatrixSerialized
  apply flatMapToBitsWithInput (range.comp hm)
  apply bitsAppend
  · fun_prop
  · apply flatMapToBitsWithInput (range.comp (hn.comp (fst input encUnary)))
    apply bitsLow (by fun_prop)
    apply binary_mod'
    · have hrow := (listGetD (encA := encList encNat) []).comp
        ((hinputs.snd'.fst'.comp (fst input encUnary)).prod (snd input encUnary))
      exact (listGetD (encA := encNat) 0).comp
        ((hrow.comp (fst (encPair input encUnary) encUnary)).prod
          (snd (encPair input encUnary) encUnary))
    · exact binary_pow' (const 2) (by fun_prop)

/-- Normalize and write the declared number of binary secret coordinates. -/
@[fun_prop]
theorem computableInPolyTime_secretSerialized {secret : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecret : ComputableInPolyTime secret input (encList encNat)) :
    ComputableInPolyTime (fun a => secretSerialized (n a) (w a) (secret a))
      input encBits := by
  have hn := hn.tidy
  have hw := hw.tidy
  have hsecret := hsecret.tidy
  refine .of_tidy ?_
  unfold secretSerialized
  apply flatMapToBitsWithInput (range.comp hn)
  apply bitsLow (hw.comp (fst input encUnary))
  apply binary_mod'
  · exact (listGetD (encA := encNat) 0).comp
      ((hsecret.comp (fst input encUnary)).prod (snd input encUnary))
  · exact binary_pow' (const 2) (hw.comp (fst input encUnary))

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
  have hn := hn.tidy
  have hm := hm.tidy
  have hw := hw.tidy
  have hpublicWord := hpublicWord.tidy
  have hmessage := hmessage.tidy
  have hcoins := hcoins.tidy
  have hi := hi.tidy
  have hk := hk.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  unfold encryptEntry
  have hcoinsRow := (listGetD (encA := encBits) []).comp
    (((listGetD (encA := encList encBits) []).comp (hcoins.prod hi)).prod hk)
  have hterm : ComputableTidilyInPolyTime
      (fun p : α × ℕ => if (((coins p.1).getD (i p.1) []).getD (k p.1) []).getD p.2 false
        then Matrix.binaryEntry (n p.1 + 1) (w p.1) (publicWord p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp
      ((hcoinsRow.comp (fst input encUnary)).prod (snd input encUnary))).ite'
    · exact matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (snd input encUnary) (by fun_prop)
    · exact const 0
  have hsum := binary_sum.comp (mapWithInput
    (f := fun a r => if (((coins a).getD (i a) []).getD (k a) []).getD r false
      then Matrix.binaryEntry (n a + 1) (w a) (publicWord a) r (j a) else 0)
    (range.comp hm) hterm)
  have hgadget : ComputableTidilyInPolyTime
      (fun a => if i a = j a then (message a).toNat * 2 ^ k a else 0) input encNat := by
    simpa only [Function.comp_apply, beq_iff_eq] using (unary_beq hi hj).ite'
      (binary_mul' (unary_to_binary.comp (bool_toUnary.comp hmessage))
        (binary_pow' (const 2) hk)) (const 0)
  exact binary_mod' (binary_add' hgadget hsum) (binary_pow' (const 2) hw)

attribute [local fun_prop] ComputableInPolyTime.tidy in
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
  have hn := hn.tidy
  have hm := hm.tidy
  have hw := hw.tidy
  have hpublicWord := hpublicWord.tidy
  have hmessage := hmessage.tidy
  have hcoins := hcoins.tidy
  refine .of_tidy ?_
  unfold encryptWithCoinsSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The complete key generator is strict PPT for arbitrary efficient runtime dimensions. -/
@[fun_prop]
theorem isPPTOn_keyGenSerialized
    (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hη : ComputableInPolyTime η input encUnary) :
    IsPPTOn input (encPair encBits encBits)
      (fun a => keyGenSerialized (n a) (m a) (w a) (η a)) := by
  have hn := hn.tidy
  have hm := hm.tidy
  have hw := hw.tidy
  have hη := hη.tidy
  have hsample := isPPTOn_sampleKeyInputsSerialized (.of_tidy hn) (.of_tidy hm) (.of_tidy hw)
    (.of_tidy hη)
  unfold keyGenSerialized
  ppt

attribute [local fun_prop] ComputableInPolyTime.tidy in
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
  have hn := hn.tidy
  have hm := hm.tidy
  have hw := hw.tidy
  have hpublicWord := hpublicWord.tidy
  have hmessage := hmessage.tidy
  have hsample := isPPTOn_sampleCoinsSerialized (.of_tidy hn) (.of_tidy hm) (.of_tidy hw)
  unfold encryptSerialized
  ppt

end Cslib.Crypto.Homomorphic.GSW
