/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Correctness
import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.PolyTime

/-!
Serialized GSW regressions exercise exact bit order and widths, negative wraparound, ragged
numeric and coin lists, truncated public words, empty dimensions, and actual generated-key
support. The nonzero-noise fixture connects word algorithms to ordinary typed decryption.
These are construction and runtime tests, with no security or bootstrappability assumption.
-/

namespace ComplexityTests.GSWNative

open Cslib Cslib.Probability Cslib.Crypto.Homomorphic.GSW
open Turing.MultiTapeTM

example : BitString.lowBits 4 5 = [true, false, true, false] ∧
    BitString.lowBits 2 5 = [true, false] := by decide +kernel

-- Row order and low-order-first digits are checked independently of the roundtrip theorem.
private def smallMatrix : _root_.Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 3)) :=
  fun i j => ((2 * i.val + j.val + 1 : ℕ) : ZMod (2 ^ 3))

example : Cslib.Matrix.toBinary smallMatrix =
    [true, false, false, false, true, false, true, true, false, false, false, true] := by
  decide +kernel

example : Cslib.Matrix.ofBinary 2 2 3 (Cslib.Matrix.toBinary smallMatrix) = smallMatrix :=
  Cslib.Matrix.ofBinary_toBinary smallMatrix

-- Binary representatives exceeding the modulus normalize before encoding.
example : secretSerialized 1 6 [69, 99] = [true, false, true, false, false, false] := by
  decide +kernel

-- The leading public residue is 3*5-16 = -1, hence 63 modulo64.
example : publicMatrixSerialized 1 1 6 ([5], ([[3]], [-16])) =
    [true, true, true, true, true, true, true, true, false, false, false, false] := by
  decide +kernel

-- Missing numeric entries are zero; excess rows/errors are ignored.
private def ragged : SerializedKeyInputs := ([3], ([[2, 5], [], [99]], [-1, 66, 42]))

example :
    Cslib.Matrix.binaryEntry 3 3 (publicMatrixSerialized 2 2 3 ragged) 0 0 = 5 ∧
    Cslib.Matrix.binaryEntry 3 3 (publicMatrixSerialized 2 2 3 ragged) 0 1 = 2 ∧
    Cslib.Matrix.binaryEntry 3 3 (publicMatrixSerialized 2 2 3 ragged) 0 2 = 5 ∧
    Cslib.Matrix.binaryEntry 3 3 (publicMatrixSerialized 2 2 3 ragged) 1 0 = 2 ∧
    (publicMatrixSerialized 2 2 3 ragged).length = 18 := by
  decide +kernel

-- A short public word decodes to [5,0]. Only the first coin is present and true.
example : encryptWithCoinsSerialized 1 1 3 [true, false, true, false] false [[[true]]] =
    [true, false, true, false, false, false] ++ List.replicate 30 false := by
  decide +kernel

-- No public rows: encrypting true still constructs the full identity ciphertext.
example : encryptWithCoinsSerialized 1 0 2 [] true [] =
    [true, false, false, false, false, true, false, false,
      false, false, true, false, false, false, false, true] := by
  decide +kernel

example : publicMatrixSerialized 0 1 3 ([], ([[]], [-1])) = [true, true, true] := by
  decide +kernel

example (n m : ℕ) (inputs : SerializedKeyInputs) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) :
    publicMatrixSerialized n m 0 inputs = [] ∧
      encryptWithCoinsSerialized n m 0 publicWord message coins = [] := by
  constructor
  · apply List.eq_nil_of_length_eq_zero
    rw [length_publicMatrixSerialized, Nat.mul_zero]
  · apply List.eq_nil_of_length_eq_zero
    rw [length_encryptWithCoinsSerialized, Nat.mul_zero]
    rfl

example : publicMatrixSerialized 0 0 4 ragged = [] := rfl

private def keyInputs : KeyInputs 1 1 6 :=
  ⟨fun _ => 5, fun _ _ => 3, fun _ => 1⟩

private def keys :=
  (publicMatrix keyInputs.publicPart keyInputs.secret keyInputs.error, keyInputs.secret)

private def coins : _root_.Matrix (Fin 2 × Fin 6) (Fin 1) Bool := fun _ _ => true

private def wordKeys : List Bool × List Bool :=
  (publicMatrixSerialized 1 1 6 (serializeKeyInputs keyInputs),
    secretSerialized 1 6 (serializeKeyInputs keyInputs).1)

private theorem wordKeys_eq :
    wordKeys = (serializePublicMatrix keys.1, serializeSecret keys.2) := by
  simp [wordKeys, keys, publicMatrixSerialized_serializeKeyInputs,
    secretSerialized_serializeKeyInputs]

private def wordCipher (message : Bool) : List Bool :=
  encryptWithCoinsSerialized 1 1 6 wordKeys.1 message (serializeCoins coins)

private theorem wordCipher_eq (message : Bool) :
    wordCipher message = serializeCiphertext (encryptWithCoins keys.1 message coins) := by
  rw [wordCipher, wordKeys_eq, encryptWithCoinsSerialized_serialize]

-- This fixture is actually supported by the sampler, with nonzero signed error.
private theorem keys_supported : keys ∈ (ProbComp.eval (keyGen 1 1 6 1)).support := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  refine ⟨keyInputs, ?_, rfl⟩
  rw [mem_support_sampleKeyInputs_iff]
  decide +kernel

example : wordKeys ∈ (ProbComp.eval (keyGenSerialized 1 1 6 1)).support := by
  rw [wordKeys_eq, eval_keyGenSerialized, PMF.mem_support_map_iff]
  exact ⟨keys, keys_supported, rfl⟩

example (message : Bool) :
    wordCipher message ∈ (ProbComp.eval (encryptSerialized 1 1 6 wordKeys.1 message)).support := by
  rw [wordCipher_eq, wordKeys_eq, eval_encryptSerialized_serializePublicMatrix,
    PMF.mem_support_map_iff]
  exact ⟨encryptWithCoins keys.1 message coins,
    (mem_support_encrypt_iff _ _ _).mpr ⟨coins, rfl⟩, rfl⟩

example (message : Bool) : decrypt (decodeSecret 1 6 wordKeys.2)
    (decodeCiphertext 1 6 (wordCipher message)) = message := by
  rw [wordCipher_eq, wordKeys_eq, decode_serializeSecret, decode_serializeCiphertext]
  exact decrypt_encryptWithCoins (bound := 1) keyInputs.publicPart keyInputs.secret keyInputs.error
    message coins (by decide) (by decide +kernel) (by decide)

-- Full unbounded-size words are covered by the total semantic bridges.
example :
    encryptWithCoinsSerialized 1 1 3 [true, false, true, false] false [[[true]]] =
      serializeCiphertext
        (encryptWithCoins (Cslib.Matrix.ofBinary 1 2 3 [true, false, true, false]) false
          (decodeCoins 1 1 3 [[[true]]])) :=
  encryptWithCoinsSerialized_eq 1 1 3 [true, false, true, false] false [[[true]]]

-- Every dimension grows. Key generation includes all sampled errors, matrix arithmetic and words.
example : IsPPTOn encUnary (encPair encBits encBits)
    (fun size => keyGenSerialized size size (size + 1) size) :=
  isPPTOn_keyGenSerialized (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

-- Arbitrary public words are charged in full; there is no canonical-word or length premise.
example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => encryptSerialized p.1 p.1 (p.1 + 1) p.2.1 p.2.2) :=
  isPPTOn_encryptSerialized (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

-- Arbitrary malformed coins are also part of the deterministic input encoding.
example : ComputableInPolyTime
    (fun p : ℕ × (List Bool × (Bool × SerializedCoins)) =>
      encryptWithCoinsSerialized p.1 p.1 (p.1 + 1) p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encBits (encPair encBool encSerializedCoins))) encBits :=
  computableInPolyTime_encryptWithCoinsSerialized
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

-- The joint client preserves the sampled keys while encrypting under the generated public key.
example : IsPPTOn (encPair encUnary encBool) (encPair (encPair encBits encBits) encBits)
    (fun p => do
      let keys ← keyGenSerialized p.1 p.1 (p.1 + 1) p.1
      let ciphertext ← encryptSerialized p.1 p.1 (p.1 + 1) keys.1 p.2
      return (keys, ciphertext)) := by
  ppt

end ComplexityTests.GSWNative
