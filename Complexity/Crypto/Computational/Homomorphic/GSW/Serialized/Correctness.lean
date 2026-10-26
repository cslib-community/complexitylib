/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized
import Mathlib.Algebra.BigOperators.Fin
import Complexity.Foundations.Data.List.Lookup

/-!
# Exact bridges for the serialized GSW algorithms

The executable word algorithms agree with the typed modular formulas, for every serialized
input under the specified total decoders. The equalities do not require a noise bound or a
security assumption. Composition with the exact sampling laws retains the complete joint key
distribution and the encryption distribution.

## Main results

* `publicMatrixSerialized_eq`, `encryptWithCoinsSerialized_eq`: exact deterministic bridges.
* `eval_keyGenSerialized`, `eval_encryptSerialized`: exact probabilistic bridges.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability BitString
open scoped BigOperators _root_.Matrix

/-- The binary signed-remainder computation returns the canonical leading public residue. -/
theorem publicRowHead_eq {n m w : ℕ} (inputs : SerializedKeyInputs) (i : Fin m) :
    publicRowHead n w inputs i.val =
      (publicMatrix (decodeKeyInputs n m w inputs).publicPart
        (decodeKeyInputs n m w inputs).secret (decodeKeyInputs n m w inputs).error i 0).val := by
  unfold publicRowHead publicMatrix LWE.publicMatrix decodeKeyInputs
  simp only [Fin.cons_zero, _root_.Matrix.mulVec, dotProduct]
  rw [List.map_range_eq_ofFn, List.sum_ofFn]
  have h : ((∑ j : Fin n,
      (inputs.2.1.getD i.val []).getD j.val 0 * inputs.1.getD j.val 0 : ℕ) : ZMod (2 ^ w)) =
      ∑ j : Fin n, ((inputs.2.1.getD i.val []).getD j.val 0 : ZMod (2 ^ w)) *
        (inputs.1.getD j.val 0 : ZMod (2 ^ w)) := by simp
  rw [← h]
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ w)
    (((∑ j : Fin n,
      (inputs.2.1.getD i.val []).getD j.val 0 * inputs.1.getD j.val 0 : ℕ) : ℤ) +
        inputs.2.2.getD i.val 0))
  simpa only [Int.toNat_natCast, Int.cast_add, Int.cast_natCast, Nat.cast_pow,
    Nat.cast_ofNat] using hv.symm

/-- The total public-key computation is exactly the typed public matrix of the decoded inputs. -/
theorem publicMatrixSerialized_eq (n m w : ℕ) (inputs : SerializedKeyInputs) :
    publicMatrixSerialized n m w inputs = serializePublicMatrix
      (publicMatrix (decodeKeyInputs n m w inputs).publicPart
        (decodeKeyInputs n m w inputs).secret (decodeKeyInputs n m w inputs).error) := by
  simp only [publicMatrixSerialized, serializePublicMatrix, Cslib.Matrix.toBinary_eq,
    List.flatMap_def, List.map_range_eq_ofFn, lowBits_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [List.ofFn_succ]
  simp only [List.flatten_cons]
  congr 1
  · rw [publicRowHead_eq inputs i]
  · simp [publicMatrix, LWE.publicMatrix, decodeKeyInputs, ZMod.val_natCast]

/-- The total secret computation agrees with the same padded and modularly normalized inputs. -/
theorem secretSerialized_eq (n w : ℕ) (secret : List ℕ) :
    secretSerialized n w secret =
      serializeSecret (fun i : Fin n => (secret.getD i.val 0 : ZMod (2 ^ w))) := by
  unfold secretSerialized serializeSecret Cslib.Matrix.toBinary
  rw [ofFn_blocksEquiv_symm]
  simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, ofFn_blocksEquiv_symm, List.flatMap_def, List.map_range_eq_ofFn,
    lowBits_eq_ofFn, ZMod.val_natCast]

/-- A computed ciphertext entry is the canonical residue of the actual modular formula. -/
theorem encryptEntry_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) (i : Fin (n + 1)) (k : Fin w) (j : Fin (n + 1)) :
    encryptEntry n m w publicWord message coins i.val k.val j.val =
      (((message.toNat : ZMod (2 ^ w)) • gadgetMatrix n w +
        bitMatrix (ZMod (2 ^ w)) (decodeCoins n m w coins) *
          Cslib.Matrix.ofBinary m (n + 1) w publicWord) (i, k) j).val := by
  unfold encryptEntry
  rw [List.map_range_eq_ofFn, List.sum_ofFn, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_add, Nat.cast_sum, _root_.Matrix.add_apply, _root_.Matrix.smul_apply,
    _root_.Matrix.mul_apply, gadgetMatrix_apply]
  congr 1
  · by_cases h : i = j
    · simp [h]
    · have hv : i.val ≠ j.val := fun hij => h (Fin.ext hij)
      simp [h, hv]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [bitMatrix_apply, Cslib.Matrix.ofBinary_apply]
    cases h : ((coins.getD i.val []).getD k.val []).getD r.val false <;>
      simp only [decodeCoins, h, Bool.false_eq_true, ↓reduceIte,
        Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul]

/-- All bits of the total ciphertext computation agree with encryption of the decoded inputs. -/
theorem encryptWithCoinsSerialized_eq (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) :
    encryptWithCoinsSerialized n m w publicWord message coins = serializeCiphertext
      (encryptWithCoins (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message
        (decodeCoins n m w coins)) := by
  rw [encryptWithCoins_eq_decomposeMatrix]
  simp only [encryptWithCoinsSerialized, serializeCiphertext, List.flatMap_def,
    List.map_range_eq_ofFn, lowBits_eq_ofFn, ofFn_blocksEquiv_symm,
    encryptEntry_eq, decomposeMatrix, bitDecomp]

/-- Canonical sampled inputs produce exactly the original typed public key. -/
theorem publicMatrixSerialized_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    publicMatrixSerialized n m w (serializeKeyInputs inputs) =
      serializePublicMatrix (publicMatrix inputs.publicPart inputs.secret inputs.error) := by
  rw [publicMatrixSerialized_eq, decode_serializeKeyInputs]

/-- Canonical sampled inputs produce exactly the original typed secret key. -/
theorem secretSerialized_serializeKeyInputs {n m w : ℕ} (inputs : KeyInputs n m w) :
    secretSerialized n w (serializeKeyInputs inputs).1 = serializeSecret inputs.secret := by
  rw [secretSerialized_eq]
  congr 1
  funext i
  simp [serializeKeyInputs]

/-- Serialization commutes with the actual typed encryption on canonical inputs. -/
theorem encryptWithCoinsSerialized_serialize {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (message : Bool)
    (coins : _root_.Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    encryptWithCoinsSerialized n m w (serializePublicMatrix A) message (serializeCoins coins) =
      serializeCiphertext (encryptWithCoins A message coins) := by
  rw [encryptWithCoinsSerialized_eq, decode_serializeCoins]
  simp only [serializePublicMatrix, Cslib.Matrix.ofBinary_toBinary]

/-- Every arbitrary input produces the complete declared public word. -/
theorem length_publicMatrixSerialized (n m w : ℕ) (inputs : SerializedKeyInputs) :
    (publicMatrixSerialized n m w inputs).length = m * (n + 1) * w := by
  simp [publicMatrixSerialized, List.length_flatMap, Nat.mul_add, Nat.add_mul,
    Nat.mul_assoc, Nat.add_comm]

/-- Secret normalization retains exactly the declared number of residue bits. -/
theorem length_secretSerialized (n w : ℕ) (secret : List ℕ) :
    (secretSerialized n w secret).length = n * w := by
  simp [secretSerialized, List.length_flatMap]

/-- Encryption writes every bit of its square ciphertext, on arbitrary input words and coins. -/
theorem length_encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) :
    (encryptWithCoinsSerialized n m w publicWord message coins).length = ((n + 1) * w) ^ 2 := by
  simp [encryptWithCoinsSerialized, List.length_flatMap, pow_two, Nat.mul_assoc]

/-- The efficient key sampler retains the typed construction's complete public/secret joint law. -/
theorem eval_keyGenSerialized (n m w η : ℕ) :
    ProbComp.eval (keyGenSerialized n m w η) = (ProbComp.eval (keyGen n m w η)).map
      (fun keys => (serializePublicMatrix keys.1, serializeSecret keys.2)) := by
  simp only [keyGenSerialized, keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleKeyInputsSerialized,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def,
    publicMatrixSerialized_serializeKeyInputs, secretSerialized_serializeKeyInputs]

/-- The efficient encryption sampler agrees with typed encryption of every decoded public word. -/
theorem eval_encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w publicWord message) =
      (ProbComp.eval (encrypt (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message)).map
        serializeCiphertext := by
  simp only [encryptSerialized, encrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleCoinsSerialized,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def,
    encryptWithCoinsSerialized_eq, decode_serializeCoins]

/-- Canonical public words have the exact original typed encryption distribution. -/
theorem eval_encryptSerialized_serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w (serializePublicMatrix A) message) =
      (ProbComp.eval (encrypt A message)).map serializeCiphertext := by
  rw [eval_encryptSerialized]
  simp only [serializePublicMatrix, Cslib.Matrix.ofBinary_toBinary]

end Cslib.Crypto.Homomorphic.GSW
