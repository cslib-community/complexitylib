/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation.PolyTime

/-!
The actual word algorithms are tested on malformed inputs, small widths, signed wraparound,
integer carries and asymmetric matrix products. A positive-noise supported fixture exercises
both plaintexts, and a growing-input client composes key generation, encryption, NAND and
decryption through their native certificates. No security or bootstrappability is assumed.
-/

namespace ComplexityTests.GSWEvaluation

open Cslib Cslib.Probability Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM

example (n : ℕ) (secret ciphertext left right : List Bool) :
    decryptSerialized n 0 secret ciphertext = false ∧ nandSerialized n 0 left right = [] := by
  constructor
  · simp [decryptSerialized]
  · apply List.eq_nil_of_length_eq_zero
    simp

-- Width one is not the width-zero convention: either plaintext can be recovered.
example : decryptSerialized 0 1 [] [true] = true ∧
    decryptSerialized 0 1 [] [] = false := by decide +kernel

private def phaseWord (value : ℕ) : List Bool := List.replicate 6 false ++ BitString.lowBits 3 value

-- Both half-open endpoints are tested through the actual raw-word program.
example : decryptSerialized 0 3 [] (phaseWord 1) = false ∧
    decryptSerialized 0 3 [] (phaseWord 2) = true ∧
    decryptSerialized 0 3 [] (phaseWord 5) = true ∧
    decryptSerialized 0 3 [] (phaseWord 6) = false := by decide +kernel

-- The selected row is [0,2], secret is 1: signed subtraction gives -2 mod4 = 2.
private def negativePhase : List Bool := [false, false, false, false, false, false, false, true]

example : decryptResidue 1 2 [true] negativePhase = 2 ∧
    decryptSerialized 1 2 [true] negativePhase = true := by decide +kernel

-- Missing secret/ciphertext bits are zero; bits beyond the declared widths are ignored.
example : decryptSerialized 1 2 [true] negativePhase =
      decryptSerialized 1 2 [true, false] (negativePhase ++ List.replicate 8 false) ∧
    decryptSerialized 1 2 [true, false, true, true]
      (negativePhase ++ List.replicate 8 false ++ [true, true]) = true := by decide +kernel

private def leftWord : List Bool := [true, true, false, false]
private def rightWord : List Bool := [true, false, true, false]

-- The forward product contains a count of 2. The reverse product is different; both have
-- negative entries before modular reduction, so parity or truncated subtraction is detected.
example : nandSerialized 0 2 leftWord rightWord = [true, true, false, true] ∧
    nandSerialized 0 2 rightWord leftWord = [false, true, true, true] := by decide +kernel

-- Off-diagonal gadget zero minus one must wrap to 3, not truncate to zero.
example : nandEntry 1 2 [true] [false, false, true] 0 0 1 = 3 := by decide +kernel

example : nandSerialized 0 2 [true] [true] = [false, false, false, true] ∧
    nandSerialized 0 2 (leftWord ++ [true, false, true]) (rightWord ++ [true, true]) =
      nandSerialized 0 2 leftWord rightWord := by decide +kernel

-- Concrete word-level bridges for length, decryption, and NAND evaluation.
example :
    (nandSerialized 1 2 leftWord rightWord).length = 16 ∧
      decryptSerialized 1 2 [true] negativePhase =
        decrypt (decodeSecret 1 2 [true]) (decodeCiphertext 1 2 negativePhase) ∧
      nandSerialized 1 2 leftWord rightWord =
        serializeCiphertext (nand (decodeCiphertext 1 2 leftWord)
          (decodeCiphertext 1 2 rightWord)) :=
  ⟨length_nandSerialized 1 2 leftWord rightWord,
    decryptSerialized_eq 1 2 [true] negativePhase,
    nandSerialized_eq 1 2 leftWord rightWord⟩

private def keyInputs : KeyInputs 1 1 6 :=
  ⟨fun _ => 5, fun _ _ => 3, fun _ => 1⟩

private def typedKeys :=
  (publicMatrix keyInputs.publicPart keyInputs.secret keyInputs.error, keyInputs.secret)

private def wordKeys : List Bool × List Bool :=
  (serializePublicMatrix typedKeys.1, serializeSecret typedKeys.2)

private def coins : _root_.Matrix (Fin 2 × Fin 6) (Fin 1) Bool := fun _ _ => true

private def wordCipher (message : Bool) : List Bool :=
  encryptWithCoinsSerialized 1 1 6 wordKeys.1 message (serializeCoins coins)

private theorem keys_supported :
    wordKeys ∈ (ProbComp.eval (keyGenSerialized 1 1 6 1)).support := by
  rw [eval_keyGenSerialized, PMF.mem_support_map_iff]
  refine ⟨typedKeys, ?_, rfl⟩
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff]
  refine ⟨keyInputs, ?_, rfl⟩
  rw [mem_support_sampleKeyInputs_iff]
  decide +kernel

private theorem cipher_supported (message : Bool) :
    wordCipher message ∈ (ProbComp.eval (encryptSerialized 1 1 6 wordKeys.1 message)).support := by
  rw [show wordKeys.1 = serializePublicMatrix typedKeys.1 from rfl,
    eval_encryptSerialized_serializePublicMatrix, PMF.mem_support_map_iff]
  refine ⟨encryptWithCoins typedKeys.1 message coins, ?_, ?_⟩
  · exact (mem_support_encrypt_iff _ _ _).mpr ⟨coins, rfl⟩
  · exact (encryptWithCoinsSerialized_serialize typedKeys.1 message coins).symm

-- This supported key/coin fixture checks both messages and the entire Boolean NAND table.
example (message : Bool) : decryptSerialized 1 6 wordKeys.2 (wordCipher message) = message :=
  keyGenSerialized_encrypt_correct (by decide) (by decide) keys_supported message
    (cipher_supported message)

example (left right : Bool) :
    decryptSerialized 1 6 wordKeys.2 (nandSerialized 1 6 (wordCipher left) (wordCipher right)) =
      !(left && right) :=
  keyGenSerialized_nand_correct (by decide) (by decide) keys_supported left right
    (cipher_supported left) (cipher_supported right)

-- Both dimensions and both entire raw words vary with the input.
example : ComputableInPolyTime
    (fun p : ℕ × ℕ × List Bool × List Bool => decryptSerialized p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encBits encBits))) encBool := by fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × ℕ × List Bool × List Bool => nandSerialized p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encBits encBits))) encBits := by fun_prop

private noncomputable def completeClient (p : ℕ × ℕ × ℕ × ℕ × Bool × Bool) : ProbComp Bool := do
  let keys ← keyGenSerialized p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let left ← encryptSerialized p.1 p.2.1 p.2.2.1 keys.1 p.2.2.2.2.1
  let right ← encryptSerialized p.1 p.2.1 p.2.2.1 keys.1 p.2.2.2.2.2
  return decryptSerialized p.1 p.2.2.1 keys.2 (nandSerialized p.1 p.2.2.1 left right)

example : IsPPTOn
    (encPair encUnary (encPair encUnary (encPair encUnary
      (encPair encUnary (encPair encBool encBool))))) encBool completeClient := by
  unfold completeClient
  ppt

end ComplexityTests.GSWEvaluation
