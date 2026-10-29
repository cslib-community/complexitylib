/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation
public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.PolyTime

/-!
# Uniform native GSW decryption and NAND

The actual serialized operations have uniform native polynomial-time certificates. Dimensions
and loop indices are unary; modular values and signed differences are binary. Complete input
words, intermediate sums and all output bits are charged. The certificates apply to arbitrary
raw words, without shape, noise, support or security assumptions.

## Main results

* `computableInPolyTime_decryptSerialized`: the actual total raw-word decryption test.
* `computableInPolyTime_nandSerialized`: the complete actual NAND ciphertext computation.

## References

* [Gentry, Sahai and Waters, Sections 3.1 and 3.3][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n w i k j : α → ℕ}

private theorem computableInPolyTime_matrixBinaryEntry {β : Type} {encIn : β ↪ List Bool}
    {cols width row col : β → ℕ} {word : β → List Bool}
    (_hcols : ComputableInPolyTime cols encIn encUnary)
    (hwidth : ComputableInPolyTime width encIn encUnary)
    (hword : ComputableInPolyTime word encIn encBits)
    (_hrow : ComputableInPolyTime row encIn encUnary)
    (_hcol : ComputableInPolyTime col encIn encUnary) :
    ComputableInPolyTime
      (fun a => Matrix.binaryEntry (cols a) (width a) (word a) (row a) (col a))
      encIn encNat :=
  bitsToNat.comp (bitsRowWithInput hwidth (by fun_prop) hword)

private theorem computableInPolyTime_intBin_emodNat'
    {value : α → ℤ} {modulus : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    ComputableInPolyTime (fun a => (value a % (modulus a : ℤ)).toNat) input encNat := by
  have hsign : ComputableInPolyTime (fun a => decide (value a < 0)) input encBool :=
    ((headD (encA := encBool) (encL := encBits) false).comp hvalue.encoding_comp).of_enc_eq
      fun a => by simp
  have habs : ComputableInPolyTime (fun a => (value a).natAbs) input encNat :=
    (bitsTail.comp hvalue.encoding_comp).of_enc_eq fun a => by simp
  have hrem := binary_mod.comp (habs.prod hmodulus)
  have h := hsign.ite'
    (binary_mod.comp ((binary_sub.comp (hmodulus.prod hrem)).prod hmodulus)) hrem
  refine h.of_enc_eq fun a => congrArg encNat ?_
  by_cases hz : value a < 0
  · simp only [Function.comp_apply, hz, decide_true, ↓reduceIte]
    by_cases hq : modulus a = 0
    · simp only [hq, Nat.cast_zero, Int.emod_zero, Nat.zero_sub, Nat.mod_zero]
      omega
    · rw [Int.emod_natAbs_of_neg hz hq]
      split_ifs with hdiv
      · simp [Int.emod_eq_zero_of_dvd hdiv]
      · have hlt : (value a % (modulus a : ℤ)).toNat < modulus a := by
          have := Int.emod_lt_of_pos (value a) (by omega : 0 < (modulus a : ℤ))
          omega
        rw [Nat.sub_sub_self hlt.le, Nat.mod_eq_of_lt hlt]
  · simp only [Function.comp_apply, hz, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (Int.emod_natAbs_of_nonneg (by omega : 0 ≤ value a)).symm

/-- Compute the selected phase uniformly from every pair of raw secret and ciphertext words. -/
@[fun_prop]
theorem computableInPolyTime_decryptResidue {secret ciphertext : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecret : ComputableInPolyTime secret input encBits)
    (hciphertext : ComputableInPolyTime ciphertext input encBits) :
    ComputableInPolyTime
      (fun a => decryptResidue (n a) (w a) (secret a) (ciphertext a)) input encNat := by
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ => Matrix.binaryEntry (n p.1 + 1) (w p.1) (ciphertext p.1)
        (w p.1 - 1) (p.2 + 1) * Matrix.binaryEntry (n p.1) (w p.1) (secret p.1) 0 p.2)
      (encPair input encUnary) encNat := by
    apply binary_mul'
    · exact computableInPolyTime_matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)
    · exact computableInPolyTime_matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (const 0) (snd input encUnary)
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a j => Matrix.binaryEntry (n a + 1) (w a) (ciphertext a) (w a - 1) (j + 1) *
        Matrix.binaryEntry (n a) (w a) (secret a) 0 j) (range.comp hn) hterm)
  have hfirst := computableInPolyTime_matrixBinaryEntry (by fun_prop) hw hciphertext
    (by fun_prop) (const 0) (cols := fun a => n a + 1) (row := fun a => w a - 1)
  unfold decryptResidue
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    computableInPolyTime_intBin_emodNat'
      (intBin_sub.comp ((intBin_natCast.comp hfirst).prod (intBin_natCast.comp hsum)))
      (binary_pow' (const 2) hw)

/-- The total decoder is polynomial-time on the complete inputs, including malformed words. -/
@[fun_prop]
theorem computableInPolyTime_decryptSerialized {secret ciphertext : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hsecret : ComputableInPolyTime secret input encBits)
    (hciphertext : ComputableInPolyTime ciphertext input encBits) :
    ComputableInPolyTime
      (fun a => decryptSerialized (n a) (w a) (secret a) (ciphertext a)) input encBool := by
  have hvalue := computableInPolyTime_decryptResidue hn hw hsecret hciphertext
  have hq := binary_pow' (const 2) hw
  have hfour := binary_mul' (const 4) hvalue
  have htest : ComputableInPolyTime
      (fun a => decide (2 ^ w a ≤ 4 * decryptResidue (n a) (w a) (secret a) (ciphertext a) ∧
        4 * decryptResidue (n a) (w a) (secret a) (ciphertext a) < 3 * 2 ^ w a))
      input encBool :=
    decide_and (binary_le' hq hfour) (binary_lt' hfour (binary_mul' (const 3) hq))
  simpa only [decryptSerialized, beq_iff_eq] using
    (beq hw (const 0)).ite' (const false) htest

/-- Compute one actual NAND residue, keeping the complete binary sum before signed reduction. -/
@[fun_prop]
theorem computableInPolyTime_nandEntry {left right : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hleft : ComputableInPolyTime left input encBits)
    (hright : ComputableInPolyTime right input encBits)
    (hi : ComputableInPolyTime i input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime
      (fun a => nandEntry (n a) (w a) (left a) (right a) (i a) (k a) (j a)) input encNat := by
  have hterm : ComputableInPolyTime
      (fun p : α × ℕ =>
        if (left p.1).getD ((i p.1 * w p.1 + k p.1) * ((n p.1 + 1) * w p.1) + p.2) false
        then Matrix.binaryEntry (n p.1 + 1) (w p.1) (right p.1) p.2 (j p.1) else 0)
      (encPair input encUnary) encNat := by
    apply ((bitsGetD false).comp ((hleft.comp (fst input encUnary)).prod (by fun_prop))).ite'
    · exact computableInPolyTime_matrixBinaryEntry (by fun_prop) (by fun_prop) (by fun_prop)
        (snd input encUnary) (by fun_prop)
    · exact const 0
  have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (mapWithInput
      (f := fun a r => if (left a).getD ((i a * w a + k a) * ((n a + 1) * w a) + r) false
        then Matrix.binaryEntry (n a + 1) (w a) (right a) r (j a) else 0)
      (range.comp (show ComputableInPolyTime (fun a => (n a + 1) * w a)
        input encUnary by fun_prop)) hterm)
  have hgadget : ComputableInPolyTime
      (fun a => if i a = j a then 2 ^ k a else 0) input encNat := by
    simpa only [beq_iff_eq] using
      (beq hi hj).ite' (binary_pow' (const 2) hk) (const 0)
  unfold nandEntry
  simpa only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat] using
    computableInPolyTime_intBin_emodNat'
      (intBin_sub.comp ((intBin_natCast.comp hgadget).prod (intBin_natCast.comp hsum)))
      (binary_pow' (const 2) hw)

/-- Compute the full square ciphertext with a single uniform native polynomial clock. -/
@[fun_prop]
theorem computableInPolyTime_nandSerialized {left right : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hleft : ComputableInPolyTime left input encBits)
    (hright : ComputableInPolyTime right input encBits) :
    ComputableInPolyTime
      (fun a => nandSerialized (n a) (w a) (left a) (right a)) input encBits := by
  unfold nandSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  fun_prop

end Cslib.Crypto.Homomorphic.GSW
