/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Serialized
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Exact bridges for serialized GSW encryption

The executable ciphertext encryption word algorithm agrees with the typed modular formula for
every serialized input under the specified total decoders.

## Main results

* `encryptWithCoinsSerialized_eq`: exact deterministic bridge.
* `eval_encryptSerialized`, `eval_encryptSerialized_serializePublicMatrix`: exact
  probabilistic bridges.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.1][GentrySahaiWaters2013]
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability BitString
open scoped BigOperators _root_.Matrix

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

/-- Serialization commutes with the actual typed encryption on canonical inputs. -/
theorem encryptWithCoinsSerialized_serialize {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (message : Bool)
    (coins : _root_.Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    encryptWithCoinsSerialized n m w (LWE.serializePublicMatrix A) message (serializeCoins coins) =
      serializeCiphertext (encryptWithCoins A message coins) := by
  rw [encryptWithCoinsSerialized_eq, decode_serializeCoins]
  simp only [LWE.serializePublicMatrix, Cslib.Matrix.ofBinary_toBinary]

/-- Encryption writes every bit of its square ciphertext, on arbitrary input words and coins. -/
theorem length_encryptWithCoinsSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool)
    (coins : SerializedCoins) :
    (encryptWithCoinsSerialized n m w publicWord message coins).length = ((n + 1) * w) ^ 2 := by
  simp [encryptWithCoinsSerialized, List.length_flatMap, pow_two, Nat.mul_assoc]

/-- The efficient encryption sampler agrees with typed encryption of every decoded public word. -/
theorem eval_encryptSerialized (n m w : ℕ) (publicWord : List Bool) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w publicWord message) =
      (ProbComp.eval (encrypt (Cslib.Matrix.ofBinary m (n + 1) w publicWord) message)).map
        serializeCiphertext := by
  simp only [pmf_norm, encryptSerialized, encrypt, eval_sampleCoinsSerialized,
    encryptWithCoinsSerialized_eq, decode_serializeCoins]

/-- Canonical public words have the exact original typed encryption distribution. -/
theorem eval_encryptSerialized_serializePublicMatrix {n m w : ℕ}
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (message : Bool) :
    ProbComp.eval (encryptSerialized n m w (LWE.serializePublicMatrix A) message) =
      (ProbComp.eval (encrypt A message)).map serializeCiphertext := by
  rw [eval_encryptSerialized]
  simp only [LWE.serializePublicMatrix, Cslib.Matrix.ofBinary_toBinary]

end Cslib.Crypto.Homomorphic.GSW
