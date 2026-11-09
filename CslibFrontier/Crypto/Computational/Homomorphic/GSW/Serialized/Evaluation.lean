/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Serialized.Correctness
public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Decryption
import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# Total serialized GSW decryption and NAND

The algorithms read the existing fixed-width, row-major words. Missing bits are `false` and
excess bits are ignored. Arithmetic uses signed subtraction before reduction modulo `2 ^ w`;
NAND retains integer matrix-product counts before decomposing the resulting residues.

## Main definitions

* `decryptResidue`, `decryptSerialized`: the selected modular row product and its scalar decoder.
* `nandEntry`, `nandSerialized`: the actual modular NAND computation and complete output word.

## Main results

* `decryptSerialized_eq`, `nandSerialized_eq`: agreement with the typed operations on all words.
* `length_nandSerialized`: the exact square ciphertext width on every input.
* `decryptSerialized_nand`: correctness from the actual input error equations and bounds.
* `keyGenSerialized_encrypt_correct`, `keyGenSerialized_nand_correct`: correctness for every
  supported draw of the actual word-valued key generator and encryption programs.

## References

* [Gentry, Sahai and Waters, Sections 3.1 and 3.3][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability BitString
open scoped BigOperators _root_.Matrix

/-- The selected row multiplied by `(1,-secret)`, reduced only after signed subtraction. -/
def decryptResidue (n w : ℕ) (secret ciphertext : List Bool) : ℕ :=
  (((Cslib.Matrix.binaryEntry (n + 1) w ciphertext (w - 1) 0 : ℤ) -
    (((List.range n).map fun j =>
      Cslib.Matrix.binaryEntry (n + 1) w ciphertext (w - 1) (j + 1) *
        Cslib.Matrix.binaryEntry n w secret 0 j).sum : ℕ)) % (2 ^ w : ℤ)).toNat

/-- Decode the selected residue. Width zero returns `false`; every positive width uses the
same half-open middle-half test as the typed decoder, including width one. -/
def decryptSerialized (n w : ℕ) (secret ciphertext : List Bool) : Bool :=
  if w = 0 then false else
    let value := decryptResidue n w secret ciphertext
    decide (2 ^ w ≤ 4 * value ∧ 4 * value < 3 * 2 ^ w)

/-- One recomposed NAND entry: its gadget value minus the exact selected row product. -/
def nandEntry (n w : ℕ) (left right : List Bool) (i k j : ℕ) : ℕ :=
  ((((if i = j then 2 ^ k else 0 : ℕ) : ℤ) -
    (((List.range ((n + 1) * w)).map fun r =>
      if left.getD ((i * w + k) * ((n + 1) * w) + r) false then
        Cslib.Matrix.binaryEntry (n + 1) w right r j else 0).sum : ℕ)) % (2 ^ w : ℤ)).toNat

/-- Write all bits of `Flatten(I - left * right)` using the existing ciphertext order. -/
def nandSerialized (n w : ℕ) (left right : List Bool) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j => lowBits w (nandEntry n w left right i k j)

/-- Raw ciphertext lookup agrees with its finite row/column view on every input word. -/
theorem decodeCiphertext_apply (n w : ℕ) (word : List Bool)
    (i j : Fin (n + 1)) (k l : Fin w) :
    decodeCiphertext n w word (i, k) (j, l) =
      word.getD ((i.val * w + k.val) * ((n + 1) * w) + j.val * w + l.val) false := by
  simp only [decodeCiphertext, block, ofList, finProdFinEquiv, Equiv.coe_fn_mk]
  congr 1
  ring

/-- A raw residue word is exactly the recomposition of the decoded ciphertext bits. -/
theorem binaryEntry_eq_recompose_decodeCiphertext (n w : ℕ) (word : List Bool)
    (i : Fin (n + 1)) (k : Fin w) (j : Fin (n + 1)) :
    (Cslib.Matrix.binaryEntry (n + 1) w word (i.val * w + k.val) j.val : ZMod (2 ^ w)) =
      recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (decodeCiphertext n w word)) (i, k) j := by
  unfold Cslib.Matrix.binaryEntry
  have hbound : (i.val * w + k.val) * (n + 1) + j.val < ((n + 1) * w) * (n + 1) := by
    simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using
      (finProdFinEquiv (finProdFinEquiv (i, k), j)).isLt
  rw [listRow_eq_ofFn w
    (⟨(i.val * w + k.val) * (n + 1) + j.val, hbound⟩ : Fin (((n + 1) * w) * (n + 1)))]
  rw [Nat.foldr_bit_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, bitMatrix_apply,
    decodeCiphertext_apply, block, ofList, finProdFinEquiv, Equiv.coe_fn_mk]
  congr 4
  ring

/-- Signed word arithmetic returns exactly the selected modular phase of the decoded inputs. -/
theorem decryptResidue_eq {n w : ℕ} (hw : 0 < w) (secret ciphertext : List Bool) :
    decryptResidue n w secret ciphertext =
      (decryptionPhase (decodeSecret n w secret) (decodeCiphertext n w ciphertext)
        (0, ⟨w - 1, by omega⟩)).val := by
  let value : ℤ := (Cslib.Matrix.binaryEntry (n + 1) w ciphertext (w - 1) 0 : ℤ) -
    ((∑ j : Fin n, Cslib.Matrix.binaryEntry (n + 1) w ciphertext (w - 1) (j.val + 1) *
      Cslib.Matrix.binaryEntry n w secret 0 j.val : ℕ) : ℤ)
  have hcast : (value : ZMod (2 ^ w)) =
      decryptionPhase (decodeSecret n w secret) (decodeCiphertext n w ciphertext)
        (0, ⟨w - 1, by omega⟩) := by
    simp only [value, Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
      Nat.cast_sum, Nat.cast_mul,
      decryptionPhase, ← binaryEntry_eq_recompose_decodeCiphertext,
      decodeSecret, Cslib.Matrix.ofBinary_apply, Fin.val_zero, Fin.val_succ,
      Nat.zero_mul, Nat.zero_add]
  unfold decryptResidue
  rw [List.map_range_eq_ofFn, List.sum_ofFn]
  change (value % (2 ^ w : ℤ)).toNat = _
  rw [← hcast]
  exact (congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ w) value)).symm

/-- The total word algorithm is the original decryption of the total decoded inputs. -/
theorem decryptSerialized_eq (n w : ℕ) (secret ciphertext : List Bool) :
    decryptSerialized n w secret ciphertext =
      decrypt (decodeSecret n w secret) (decodeCiphertext n w ciphertext) := by
  by_cases hw : w = 0
  · subst w
    simp [decryptSerialized]
  · have hpos : 0 < w := by omega
    rw [decrypt_eq_decode_decryptionPhase hpos]
    simp only [decryptSerialized, hw, ↓reduceIte, decode, decryptResidue_eq hpos]

/-- Canonical words decrypt exactly as their typed secret and ciphertext. -/
@[simp] theorem decryptSerialized_serialize {n w : ℕ} (secret : Fin n → ZMod (2 ^ w))
    (ciphertext : Ciphertext n w) :
    decryptSerialized n w (serializeSecret secret) (serializeCiphertext ciphertext) =
      decrypt secret ciphertext := by
  rw [decryptSerialized_eq, decode_serializeSecret, decode_serializeCiphertext]

private theorem nand_eq_decomposeMatrix {n w : ℕ} (left right : Ciphertext n w) :
    nand left right = decomposeMatrix w
      (gadgetMatrix n w - bitMatrix (ZMod (2 ^ w)) left *
        recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) right)) := by
  rw [nand, flattenMatrix, recomposeMatrix_sub, recomposeMatrix_mul]
  rfl

/-- A computed NAND word is the canonical residue of the typed row product. -/
theorem nandEntry_eq (n w : ℕ) (left right : List Bool)
    (i : Fin (n + 1)) (k : Fin w) (j : Fin (n + 1)) :
    nandEntry n w left right i.val k.val j.val =
      ((gadgetMatrix n w - bitMatrix (ZMod (2 ^ w)) (decodeCiphertext n w left) *
        recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (decodeCiphertext n w right)))
          (i, k) j).val := by
  let value : ℤ := ((if i.val = j.val then 2 ^ k.val else 0 : ℕ) : ℤ) -
    ((∑ r : Fin ((n + 1) * w),
      if left.getD ((i.val * w + k.val) * ((n + 1) * w) + r.val) false then
        Cslib.Matrix.binaryEntry (n + 1) w right r.val j.val else 0 : ℕ) : ℤ)
  have hcast : (value : ZMod (2 ^ w)) =
      (gadgetMatrix n w - bitMatrix (ZMod (2 ^ w)) (decodeCiphertext n w left) *
        recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (decodeCiphertext n w right)))
          (i, k) j := by
    simp only [value, Int.cast_sub, Int.cast_sum, Int.cast_natCast, Nat.cast_sum,
      _root_.Matrix.sub_apply, _root_.Matrix.mul_apply, gadgetMatrix_apply]
    congr 1
    · by_cases h : i = j
      · simp [h]
      · have hv : i.val ≠ j.val := fun hij => h (Fin.ext hij)
        simp [h, hv]
    · rw [← (finProdFinEquiv : Fin (n + 1) × Fin w ≃ Fin ((n + 1) * w)).sum_comp]
      apply Finset.sum_congr rfl
      rintro ⟨r, l⟩ hr
      rw [bitMatrix_apply, decodeCiphertext_apply,
        ← binaryEntry_eq_recompose_decodeCiphertext]
      simp only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_assoc, Nat.mul_comm,
        Nat.add_comm]
      split_ifs with h <;> simp_all
  unfold nandEntry
  rw [List.map_range_eq_ofFn, List.sum_ofFn]
  change (value % (2 ^ w : ℤ)).toNat = _
  rw [← hcast]
  exact (congrArg Int.toNat (ZMod.val_intCast (n := 2 ^ w) value)).symm

/-- The actual NAND program agrees with the typed operation for every pair of raw words. -/
theorem nandSerialized_eq (n w : ℕ) (left right : List Bool) :
    nandSerialized n w left right = serializeCiphertext
      (nand (decodeCiphertext n w left) (decodeCiphertext n w right)) := by
  rw [nand_eq_decomposeMatrix]
  simp only [nandSerialized, serializeCiphertext, List.flatMap_def,
    List.map_range_eq_ofFn, lowBits_eq_ofFn, ofFn_blocksEquiv_symm,
    nandEntry_eq, decomposeMatrix, bitDecomp]

/-- Decoding a raw NAND result recovers the typed operation on the decoded inputs. -/
@[simp] theorem decode_nandSerialized (n w : ℕ) (left right : List Bool) :
    decodeCiphertext n w (nandSerialized n w left right) =
      nand (decodeCiphertext n w left) (decodeCiphertext n w right) := by
  rw [nandSerialized_eq, decode_serializeCiphertext]

/-- Canonical input words produce the canonical word of their actual typed NAND. -/
@[simp] theorem nandSerialized_serialize {n w : ℕ} (left right : Ciphertext n w) :
    nandSerialized n w (serializeCiphertext left) (serializeCiphertext right) =
      serializeCiphertext (nand left right) := by
  rw [nandSerialized_eq, decode_serializeCiphertext, decode_serializeCiphertext]

/-- Every raw pair produces the complete declared ciphertext word. -/
@[simp] theorem length_nandSerialized (n w : ℕ) (left right : List Bool) :
    (nandSerialized n w left right).length = ((n + 1) * w) ^ 2 := by
  simp [nandSerialized, List.length_flatMap, pow_two, Nat.mul_assoc]

/-- The actual serialized NAND retains the exact propagated integer error equation. -/
theorem nandSerialized_hasError {n w : ℕ} (secret left right : List Bool) (μ₁ μ₂ : Bool)
    (error₁ error₂ : Fin (n + 1) × Fin w → ℤ)
    (hleft : HasError (decodeSecret n w secret) (decodeCiphertext n w left) μ₁ error₁)
    (hright : HasError (decodeSecret n w secret) (decodeCiphertext n w right) μ₂ error₂) :
    HasError (decodeSecret n w secret) (decodeCiphertext n w (nandSerialized n w left right))
      (!(μ₁ && μ₂)) (nandError (decodeCiphertext n w left) μ₂ error₁ error₂) := by
  rw [decode_nandSerialized]
  exact nand_hasError _ _ _ _ _ _ _ hleft hright

/-- Any raw ciphertext satisfying the modular equation decrypts under the original strict
noise margin. The ciphertext may be an output of previous homomorphic operations. -/
theorem decryptSerialized_eq_of_hasError {n w : ℕ} (hw : 0 < w)
    (secret ciphertext : List Bool) (μ : Bool) (error : Fin (n + 1) × Fin w → ℤ)
    (hC : HasError (decodeSecret n w secret) (decodeCiphertext n w ciphertext) μ error)
    (herror : ∀ i, 4 * (error i).natAbs < 2 ^ w) :
    decryptSerialized n w secret ciphertext = μ := by
  rw [decryptSerialized_eq]
  exact decrypt_eq_of_hasError hw _ _ _ _ hC herror

/-- Canonical actual encryption words decrypt under exactly the typed fresh-noise hypotheses. -/
theorem decryptSerialized_encryptWithCoins {n m w bound : ℕ}
    (B : _root_.Matrix (Fin m) (Fin n) (ZMod (2 ^ w))) (secret : Fin n → ZMod (2 ^ w))
    (error : Fin m → ℤ) (μ : Bool) (coins : _root_.Matrix (Fin (n + 1) × Fin w) (Fin m) Bool)
    (hw : 0 < w) (herror : ∀ j, (error j).natAbs ≤ bound)
    (hmargin : 4 * (m * bound) < 2 ^ w) :
    decryptSerialized n w (serializeSecret secret)
      (encryptWithCoinsSerialized n m w (serializePublicMatrix (publicMatrix B secret error))
        μ (serializeCoins coins)) = μ := by
  rw [encryptWithCoinsSerialized_serialize, decryptSerialized_serialize]
  exact decrypt_encryptWithCoins B secret error μ coins hw herror hmargin

/-- NAND on arbitrary raw ciphertext words is correct under the original propagated-noise
margin. No freshness, support, or canonical-length premise is added. -/
theorem decryptSerialized_nand {n w bound₁ bound₂ : ℕ}
    (secret left right : List Bool) (μ₁ μ₂ : Bool)
    (error₁ error₂ : Fin (n + 1) × Fin w → ℤ)
    (hleft : HasError (decodeSecret n w secret) (decodeCiphertext n w left) μ₁ error₁)
    (hright : HasError (decodeSecret n w secret) (decodeCiphertext n w right) μ₂ error₂)
    (hw : 0 < w)
    (herror₁ : ∀ i, (error₁ i).natAbs ≤ bound₁)
    (herror₂ : ∀ i, (error₂ i).natAbs ≤ bound₂)
    (hmargin : 4 * (bound₁ + ((n + 1) * w) * bound₂) < 2 ^ w) :
    decryptSerialized n w secret (nandSerialized n w left right) = !(μ₁ && μ₂) := by
  rw [decryptSerialized_eq, decode_nandSerialized]
  exact decrypt_nand _ _ _ _ _ _ _ hleft hright hw herror₁ herror₂ hmargin

/-- Every supported actual key and encryption word is correct under the existing fresh margin. -/
theorem keyGenSerialized_encrypt_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * (m * η) < 2 ^ w) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGenSerialized n m w η)).support) (μ : Bool)
    {ciphertext : List Bool}
    (hciphertext : ciphertext ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ)).support) :
    decryptSerialized n w keys.2 ciphertext = μ := by
  rw [eval_keyGenSerialized, PMF.mem_support_map_iff] at hkeys
  obtain ⟨typedKeys, htypedKeys, rfl⟩ := hkeys
  rw [eval_encryptSerialized_serializePublicMatrix, PMF.mem_support_map_iff] at hciphertext
  obtain ⟨typedCiphertext, htypedCiphertext, rfl⟩ := hciphertext
  rw [decryptSerialized_serialize]
  exact keyGen_encrypt_correct hw hmargin htypedKeys μ htypedCiphertext

/-- Every pair of supported fresh actual encryption words has a correct actual NAND under the
same strict fresh-NAND margin as the typed sampler theorem. -/
theorem keyGenSerialized_nand_correct {n m w η : ℕ} (hw : 0 < w)
    (hmargin : 4 * ((1 + (n + 1) * w) * (m * η)) < 2 ^ w) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGenSerialized n m w η)).support) (μ₁ μ₂ : Bool)
    {left right : List Bool}
    (hleft : left ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ₁)).support)
    (hright : right ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ₂)).support) :
    decryptSerialized n w keys.2 (nandSerialized n w left right) = !(μ₁ && μ₂) := by
  rw [eval_keyGenSerialized, PMF.mem_support_map_iff] at hkeys
  obtain ⟨typedKeys, htypedKeys, rfl⟩ := hkeys
  rw [eval_encryptSerialized_serializePublicMatrix, PMF.mem_support_map_iff] at hleft hright
  obtain ⟨typedLeft, htypedLeft, rfl⟩ := hleft
  obtain ⟨typedRight, htypedRight, rfl⟩ := hright
  rw [nandSerialized_serialize, decryptSerialized_serialize]
  exact keyGen_nand_correct hw hmargin htypedKeys μ₁ μ₂ htypedLeft htypedRight

end Cslib.Crypto.Homomorphic.GSW
