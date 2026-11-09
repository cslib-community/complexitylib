/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
import Mathlib.Data.ZMod.Basic
/-!
# Tests for symmetric block-cipher modes of operation

Exercises `CslibFrontier/Crypto/Primitives/BlockCipher/Modes.lean` on concrete `BitString 4` and
`ZMod (2 ^ 4)` blocks and audits the axiom footprint of its choice-free round-trip theorems.
-/
namespace Cslib.Crypto.BlockCipherModes.Tests
open Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal
/-! ### Concrete round-trip, keystream, and attack checks over `BitString 4` and `ZMod (2 ^ 4)` -/
/-- Sample involution on `BitString 4` (XOR with a fixed mask) used for concrete mode checks. -/
def sampleMask4 : BitString 4 := ![true, false, true, false]
/-- Sample block permutation on `BitString 4`. -/
def samplePerm4 : Equiv.Perm (BitString 4) := Equiv.addRight sampleMask4
/-- Sample non-invertible block function on `BitString 4` (constant mask). -/
def sampleConstBlock4 : BitString 4 → BitString 4 := fun _ => sampleMask4
/-- Sample counter schedule on `BitString 4`. -/
def sampleCounter4 (iv : BitString 4) (i : ℕ) : BitString 4 :=
  iv + fun k => decide (k.val = i % 4)
/-- Concrete 4-bit IV and 3-block message vectors. -/
def iv4 : BitString 4 := ![false, true, false, true]
/-- First concrete 4-bit plaintext block. -/
def msgA : BitString 4 := ![true, true, false, false]
/-- Second concrete 4-bit plaintext block. -/
def msgB : BitString 4 := ![true, false, false, true]
/-- Third concrete 4-bit plaintext block. -/
def msgC : BitString 4 := ![false, true, true, false]
example :
    cbcDecryptBlocks samplePerm4.symm iv4
      (cbcEncryptBlocks samplePerm4 iv4 [msgA, msgB, msgC]) = [msgA, msgB, msgC] := by
  decide
example :
    ofbDecryptBlocks sampleConstBlock4 iv4
      (ofbEncryptBlocks sampleConstBlock4 iv4 [msgA, msgB, msgC]) = [msgA, msgB, msgC] := by
  decide
example :
    cfbDecryptBlocks sampleConstBlock4 iv4
      (cfbEncryptBlocks sampleConstBlock4 iv4 [msgA, msgB, msgC]) = [msgA, msgB, msgC] := by
  decide
example :
    cfbEncryptBlocks sampleConstBlock4 iv4
      (cfbDecryptBlocks sampleConstBlock4 iv4 [msgA, msgB, msgC]) = [msgA, msgB, msgC] := by
  decide
example :
    ctrDecryptBlocks sampleConstBlock4 sampleCounter4 iv4
      (ctrEncryptBlocks sampleConstBlock4 sampleCounter4 iv4 [msgA, msgB, msgC]) =
      [msgA, msgB, msgC] := by
  decide
example :
    ofbChain samplePerm4 iv4 3 = cbcEncryptBlocks samplePerm4 iv4 (List.replicate 3 0) := by
  decide
example :
    List.zipWith (· + ·)
      (ofbEncryptBlocks samplePerm4 iv4 [msgB, msgC])
      (ofbEncryptBlocks samplePerm4 iv4 [msgC, msgB]) = [msgB + msgC, msgC + msgB] ∧
    List.zipWith (· + ·)
      (ctrEncryptBlocks samplePerm4 sampleCounter4 iv4 [msgB, msgC])
      (ctrEncryptBlocks samplePerm4 sampleCounter4 iv4 [msgC, msgB]) =
      [msgB + msgC, msgC + msgB] ∧
    streamIVReuseTest msgB msgC
      ((ofbEncryptBlocks samplePerm4 iv4 [msgB]).getD 0 0,
       (ofbEncryptBlocks samplePerm4 iv4 [msgC]).getD 0 0) = true ∧
    streamIVReuseTest msgB msgC
      ((ctrEncryptBlocks samplePerm4 sampleCounter4 iv4 [msgB]).getD 0 0,
       (ctrEncryptBlocks samplePerm4 sampleCounter4 iv4 [msgC]).getD 0 0) = true := by
  decide
example :
    let ctr := fun v (i : ℕ) => (samplePerm4^[i + 1]) v
    let c₁ := ctrEncryptBlocks samplePerm4 ctr iv4 [msgA, msgB]
    let c₂ := ctrEncryptBlocks samplePerm4 ctr (samplePerm4 iv4) [msgB, msgC]
    ((c₁.getD 0 0 + msgA, c₁.getD 1 0 + msgB),
     (c₂.getD 0 0 + msgB, c₂.getD 1 0 + msgC)) =
      overlappingStreamBlocks samplePerm4 samplePerm4 iv4 ∧
    overlappingStreamTest (overlappingStreamBlocks samplePerm4 samplePerm4 iv4) = true := by
  decide
example :
    cbcEncryptBlocks samplePerm4 iv4 [cbcPredictableIVQuery iv4 msgA msgB] =
      cbcEncryptBlocks samplePerm4 msgA [msgB] ∧
    cfbSameIVRecover msgA (samplePerm4 iv4 + msgA) (samplePerm4 iv4 + msgB) = msgB ∧
    xorFunctionCipherRecover
      (xorFunctionCipher sampleMask4 iv4 0)
      (xorFunctionCipher sampleMask4 msgA msgB) = msgB := by
  decide
/-- Concrete Exercise 3.25 check over modular addition `ZMod (2 ^ 4)` (`δ = 1`, `-δ = -1`) and
  over `BitString 4`. -/
example :
    let modPerm : ZMod (2 ^ 4) → ZMod (2 ^ 4) := fun x => x + 5
    additiveModeDistinguisher (additiveModeCipher modPerm 1 7 0 0) = false ∧
      additiveModeDistinguisher (additiveModeCipher modPerm 1 7 0 (-1)) = true ∧
      additiveModeDistinguisher (additiveModeCipher samplePerm4 sampleMask4 iv4 0 0) = false ∧
      additiveModeDistinguisher
        (additiveModeCipher samplePerm4 sampleMask4 iv4 0 (-sampleMask4)) = true := by
  decide
/-! ### Indexed OFB / CTR decryption against list-mode ciphertexts -/
/-- Nonconstant one-bit counter schedule: counter value `i` is the bit `i % 2`. -/
def parityCounter1 (_ : BitString 1) (i : ℕ) : BitString 1 := fun _ => decide (i % 2 = 1)
/-- The indexed ciphertext stream of a list-mode ciphertext: position `0` holds the IV and
  position `j + 1` holds list block `j`. -/
def indexedStream {n : ℕ} (iv : BitString n) (cs : List (BitString n)) : ℕ → BitString n :=
  fun j => if j = 0 then iv else cs.getD (j - 1) 0
/-- One-bit plaintext with alternating blocks. -/
def msgs1 : List (BitString 1) := [0, 0, 1, 1]
/-- Indexed CTR decryption with the identity block function, the parity counter schedule and the
  zero IV recovers every block of the actual list CTR ciphertext. -/
example :
    (List.range msgs1.length).map (fun j =>
      maskBlockDecrypt (ctrBlockMask id parityCounter1) 0
        (indexedStream 0 (ctrEncryptBlocks id parityCounter1 0 msgs1)) (j + 1)) = msgs1 := by
  decide
/-- The same agreement for OFB, with the nonlinear block function `samplePerm4`. -/
example :
    (List.range 3).map (fun j =>
      maskBlockDecrypt (ofbBlockMask samplePerm4) iv4
        (indexedStream iv4 (ofbEncryptBlocks samplePerm4 iv4 [msgA, msgB, msgC])) (j + 1)) =
      [msgA, msgB, msgC] := by
  decide
/-- The general CTR agreement theorem applied to the parity counter schedule. -/
example (j : ℕ) (hj : j < msgs1.length) :
    maskBlockDecrypt (ctrBlockMask id parityCounter1) 0
      (indexedStream 0 (ctrEncryptBlocks id parityCounter1 0 msgs1)) (j + 1) = msgs1[j] :=
  maskBlockDecrypt_ctrBlockMask_ctrEncryptBlocks id parityCounter1 0 msgs1 _
    (fun k hk => by
      simp only [indexedStream, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk),
        Option.getD_some]) j hj
/-! ### Concrete probabilistic and error-propagation instantiations -/
example (D : (Fin 2 → BitString 4) → Game) (m₀ m₁ : Fin 2 → BitString 4) :
    Game.advantage
      (((PMF.uniformOfFintype (BitString 4 → BitString 4)).map
        (fun g i => g (BitString.zeroExtend (BitString.indexBits i)) + m₀ i)).bind D)
      (((PMF.uniformOfFintype (BitString 4 → BitString 4)).map
        (fun g i => g (BitString.zeroExtend (BitString.indexBits i)) + m₁ i)).bind D) = 0 :=
  advantage_xorEvalPoints_eq_zero
    ((BitString.zeroExtend_injective (by decide)).comp BitString.indexBits_injective) m₀ m₁ D
example :
    ((PMF.uniformOfFintype (BitString 4)).bind fun iv =>
      (uniformBlocks (n := 4) [0, sampleMask4].length).map (iv, ·)).toOuterMeasure
      {p : BitString 4 × List (BitString 4) | ¬goodChain [0] p.1 [0, sampleMask4] p.2} ≤
    6 * ((2 : ℝ≥0∞) ^ 4)⁻¹ := by
  simpa using toOuterMeasure_badChain_le [0, sampleMask4] [0]
example :
    Game.advantage
      (streamIVReuseRealGame (PMF.uniformOfFintype (BitString 4)) 0 sampleMask4)
      (streamIVReuseIdealGame (n := 4) 0 sampleMask4) = 1 - ((2 : ℝ≥0) ^ 4)⁻¹ ∧
    Game.advantage
      (overlappingStreamRealGame samplePerm4 samplePerm4 (PMF.uniformOfFintype (BitString 4)))
      (overlappingStreamIdealGame 4) = 1 - ((2 : ℝ≥0) ^ 4)⁻¹ ∧
    Game.advantage
      (cbcPredictableIVGame samplePerm4 0 sampleMask4 0 sampleMask4 false)
      (cbcPredictableIVGame samplePerm4 0 sampleMask4 0 sampleMask4 true) = 1 :=
  ⟨advantage_streamIVReuseGame_eq _ 0 sampleMask4,
   advantage_overlappingStreamGame_eq samplePerm4 samplePerm4 _,
   advantage_cbcPredictableIVGame_eq_one samplePerm4.injective 0 sampleMask4 0 sampleMask4
     (by decide)⟩
example (c : ℕ → BitString 4) :
    maskBlockDecrypt (ofbBlockMask samplePerm4) 0 (flipCipherBlockBit c 1 0) 1 0 =
      !(maskBlockDecrypt (ofbBlockMask samplePerm4) 0 c 1 0) ∧
    cbcBlockDecrypt samplePerm4.symm (flipCipherBlockBit c 1 0) 2 0 =
      !(cbcBlockDecrypt samplePerm4.symm c 2 0) ∧
    cfbBlockDecrypt samplePerm4 (flipCipherBlockBit c 1 0) 1 0 =
      !(cfbBlockDecrypt samplePerm4 c 1 0) ∧
    cbcBlockDecrypt samplePerm4.symm (dropCipherBlock c 1) 2 =
      cbcBlockDecrypt samplePerm4.symm c 3 ∧
    cfbBlockDecrypt samplePerm4 (dropCipherBlock c 1) 2 =
      cfbBlockDecrypt samplePerm4 c 3 :=
  ⟨(maskBlockDecrypt_flipBit (ofbBlockMask samplePerm4) 0 c 1 0).1,
   (cbcBlockDecrypt_flipBit samplePerm4.symm c 1 le_rfl 0).2.1,
   (cfbBlockDecrypt_flipBit samplePerm4 c 1 le_rfl 0).1,
   (cbcBlockDecrypt_dropBlock samplePerm4.symm c 1 le_rfl).2.2 2 (by decide),
   (cfbBlockDecrypt_dropBlock samplePerm4 c 1 le_rfl).2.2 2 (by decide)⟩
/-! ### Axiom guards for choice-free round-trip theorems -/
/--
info: 'Cslib.Crypto.cbcDecryptBlocks_cbcEncryptBlocks' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms cbcDecryptBlocks_cbcEncryptBlocks
/--
info: 'Cslib.Crypto.ofbDecryptBlocks_ofbEncryptBlocks' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ofbDecryptBlocks_ofbEncryptBlocks
/--
info: 'Cslib.Crypto.cfbDecryptBlocks_cfbEncryptBlocks' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms cfbDecryptBlocks_cfbEncryptBlocks
/--
info: 'Cslib.Crypto.ctrDecryptBlocks_ctrEncryptBlocks' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ctrDecryptBlocks_ctrEncryptBlocks
end Cslib.Crypto.BlockCipherModes.Tests
