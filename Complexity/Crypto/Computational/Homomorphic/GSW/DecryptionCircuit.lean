/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation
public import Complexity.Computability.Circuit.Boolean.Modular.InnerProduct
public import Complexity.Computability.Circuit.Boolean.Modular.Subtract
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.List.GetD

/-!
# Selected-row GSW decryption circuits

The input order is the complete serialized secret followed by the complete serialized ciphertext.
The row selected by the existing total decoder is used on every input, without a key-generation
or noise hypothesis. Arithmetic circuits preserve residues modulo the word modulus.

## Main definitions

* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.inputWidth`: the complete raw input length.
* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.circuit`: the actual total raw-input decryptor.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.correct`: agreement with serialized decryption
  on every well-sized raw input, including widths zero and one and both half-open decoder ties.
* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.depth_circuit_le`: explicit logarithmic depth.
* `Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit.size_circuit_le`: explicit polynomial gate count.

## References

* [C. Gentry, A. Sahai, B. Waters][GentrySahaiWaters2013], Sections 3.1 and 3.4.
* [C. Gentry][Gentry2009], Definition 4: augmented decryption takes all key and ciphertext bits.
-/

public section

namespace Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString
open scoped BigOperators

variable {n w : ℕ}

/-- Secret bits precede all square-matrix ciphertext bits. -/
abbrev inputWidth (n w : ℕ) : ℕ := n * w + ((n + 1) * w) * ((n + 1) * w)

/-- Interpret the raw first block with the same total decoder as the serialized scheme. -/
private def inputSecret (x : BitString (inputWidth n w)) : Fin n → ZMod (2 ^ w) :=
  decodeSecret n w (List.ofFn (fstBits x))

/-- Interpret every raw ciphertext bit, including ciphertexts outside encryption support. -/
private def inputCiphertext (x : BitString (inputWidth n w)) : Ciphertext n w :=
  decodeCiphertext n w (List.ofFn (sndBits x))

private theorem inputSecret_apply (x : BitString (inputWidth n w)) (j : Fin n) :
    inputSecret x j = ((BitString.equivFin w (block (fstBits x) j) : ℕ) : ZMod (2 ^ w)) := by
  simp only [inputSecret, decodeSecret, Cslib.Matrix.ofBinary_apply,
    Cslib.Matrix.binaryEntry, Fin.val_zero, zero_mul, zero_add,
    listRow_eq_ofFn w j, ofList_ofFn, Nat.foldr_bit_ofFn, BitString.val_equivFin_eq_sum]

/-- Recompose any row's binary word by the same place values as the circuit word convention. -/
private theorem rowWord_cast (C : Ciphertext n w) (row : Fin (n + 1) × Fin w) (j : Fin (n + 1)) :
    ((BitString.equivFin w (fun l => C row (j, l)) : ℕ) : ZMod (2 ^ w)) =
      recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) C) row j := by
  simp only [BitString.val_equivFin_eq_sum, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, recomposeMatrix, bitCompose, bitMatrix_apply]

private theorem inputCiphertext_apply (x : BitString (inputWidth n w))
    (i j : Fin (n + 1)) (k l : Fin w) :
    inputCiphertext x (i, k) (j, l) = x (Fin.natAdd (n * w)
      (finProdFinEquiv (finProdFinEquiv (i, k), finProdFinEquiv (j, l)))) := by
  rw [inputCiphertext, decodeCiphertext_apply]
  let p := finProdFinEquiv (finProdFinEquiv (i, k), finProdFinEquiv (j, l))
  have hp : (i.val * w + k.val) * ((n + 1) * w) + j.val * w + l.val = p.val := by
    simp only [p, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk]
    ring
  rw [hp, List.getD_ofFn, sndBits_apply]

/-- The selected row is the last binary digit of the leading expanded-secret coordinate. -/
private def selectedRow (n w : ℕ) (hw : 0 < w) : Fin (n + 1) × Fin w :=
  (0, ⟨w - 1, by omega⟩)

/-- Wire one selected-row word directly out of the complete ciphertext input. -/
private def rowInputs (n w : ℕ) (hw : 0 < w) (j : Fin (n + 1)) :
    Fin w → Fin (inputWidth n w) :=
  fun l => Fin.natAdd (n * w)
    (finProdFinEquiv (finProdFinEquiv (selectedRow n w hw), finProdFinEquiv (j, l)))

private theorem eval_rowInputs (x : BitString (inputWidth n w)) (hw : 0 < w) (j : Fin (n + 1)) :
    (Circuit.wiring signature (rowInputs n w hw j)).eval interpretation x =
      fun l => inputCiphertext x (selectedRow n w hw) (j, l) := by
  funext l
  rw [Circuit.eval_wiring]
  exact (inputCiphertext_apply x 0 j ⟨w - 1, by omega⟩ l).symm

/-- Consecutive selected-row words paired with the unexpanded secret, omitting column zero. -/
private def rowTail (x : BitString (inputWidth n w)) (hw : 0 < w) : BitString (n * w) :=
  fun i => inputCiphertext x (selectedRow n w hw)
    ((finProdFinEquiv.symm i).1.succ, (finProdFinEquiv.symm i).2)

private theorem block_rowTail (x : BitString (inputWidth n w)) (hw : 0 < w) (j : Fin n) :
    block (rowTail x hw) j = fun l => inputCiphertext x (selectedRow n w hw) (j.succ, l) := by
  funext l
  simp only [rowTail, block, Equiv.symm_apply_apply]

/-- Feed the complete secret and the non-leading selected-row words to the inner product. -/
private def productInputs (n w : ℕ) (hw : 0 < w) : Fin (n * w + n * w) → Fin (inputWidth n w) :=
  Fin.append (m := n * w) (n := n * w)
    (Fin.castAdd (((n + 1) * w) * ((n + 1) * w)))
    (fun i => rowInputs n w hw (finProdFinEquiv.symm i).1.succ (finProdFinEquiv.symm i).2)

private theorem append_comp_productInputs (x : BitString (inputWidth n w)) (hw : 0 < w) :
    x ∘ productInputs n w hw = Fin.append (fstBits x) (rowTail x hw) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, productInputs, Fin.append_left, fstBits_apply]
  · simp only [Function.comp_apply, productInputs, Fin.append_right, rowTail]
    exact (inputCiphertext_apply x 0 (finProdFinEquiv.symm j).1.succ
      ⟨w - 1, by omega⟩ (finProdFinEquiv.symm j).2).symm

/-- The actual selected-row modular inner product, reading directly from raw inputs. -/
private def productSum (n w : ℕ) (hw : 0 < w) : Circuit signature (inputWidth n w) w :=
  (Modular.innerProduct n w).comp (Circuit.wiring signature (productInputs n w hw))

private theorem productSum_cast (x : BitString (inputWidth n w)) (hw : 0 < w) :
    ((BitString.equivFin w ((productSum n w hw).eval interpretation x) : ℕ) : ZMod (2 ^ w)) =
      ∑ j : Fin n, recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (inputCiphertext x))
        (selectedRow n w hw) j.succ * inputSecret x j := by
  rw [productSum, Circuit.eval_comp, Circuit.eval_wiring, append_comp_productInputs,
    Modular.val_eval_innerProduct, ZMod.natCast_mod, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.cast_mul, ← inputSecret_apply, block_rowTail, rowWord_cast, mul_comm]

/-- Subtract the selected row's inner product from its leading word, modulo `2 ^ w`. -/
private def phase (n w : ℕ) (hw : 0 < w) : Circuit signature (inputWidth n w) w :=
  (Modular.subtract w).comp
    ((Circuit.wiring signature (rowInputs n w hw 0)).append (productSum n w hw))

/-- The raw circuit phase is exactly the original selected-row residue on every input. -/
private theorem phase_cast (x : BitString (inputWidth n w)) (hw : 0 < w) :
    ((BitString.equivFin w ((phase n w hw).eval interpretation x) : ℕ) : ZMod (2 ^ w)) =
      decryptionPhase (inputSecret x) (inputCiphertext x) (selectedRow n w hw) := by
  let a := (Circuit.wiring signature (rowInputs n w hw 0)).eval interpretation x
  let b := (productSum n w hw).eval interpretation x
  have ha : ((BitString.equivFin w a : ℕ) : ZMod (2 ^ w)) =
      recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (inputCiphertext x)) (selectedRow n w hw) 0 := by
    dsimp only [a]
    rw [eval_rowInputs]
    exact rowWord_cast _ _ _
  have hb := productSum_cast x hw
  change ((BitString.equivFin w b : ℕ) : ZMod (2 ^ w)) = _ at hb
  have hv : (BitString.equivFin w ((phase n w hw).eval interpretation x) : ℕ) =
      (2 ^ w - (BitString.equivFin w b : ℕ) + (BitString.equivFin w a : ℕ)) % 2 ^ w := by
    simpa only [phase, Circuit.eval_comp, Circuit.eval_append] using Modular.val_eval_subtract a b
  rw [hv, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.le_of_lt (BitString.equivFin w b).isLt), ZMod.natCast_self]
  simp only [ha, hb, decryptionPhase, sub_eq_add_neg, add_comm, zero_add]

private theorem testBit_wordValue (x : BitString w) (i : Fin w) :
    (BitString.equivFin w x : ℕ).testBit i.val = x i := by
  simpa only [BitVec.getLsbD, toNat_word_eq_equivFin] using getLsbD_word x i

/-- Implement the actual width-zero, width-one and top-two-bit decoder cases. -/
private def decodeWord (w : ℕ) : Circuit signature w 1 :=
  if h₀ : w = 0 then Circuit.oneGate (.const false) Fin.elim0
  else if h₁ : w = 1 then Circuit.wiring signature (fun _ => ⟨0, by omega⟩)
  else ((Formula.input ⟨w - 1, by omega⟩).xor (.input ⟨w - 2, by omega⟩)).toCircuit

/-- The scalar decoder is computed on every modular word, including both quarter ties. -/
private theorem eval_decodeWord (x : BitString w) :
    (decodeWord w).eval interpretation x 0 =
      decode w ((BitString.equivFin w x : ℕ) : ZMod (2 ^ w)) := by
  have hv : (((BitString.equivFin w x : ℕ) : ZMod (2 ^ w)).val) =
      (BitString.equivFin w x : ℕ) := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (BitString.equivFin w x).isLt]
  by_cases h₀ : w = 0
  · subst w
    simp [decodeWord, interpretation]
  · by_cases h₁ : w = 1
    · subst w
      simp only [decodeWord, Nat.one_ne_zero, ↓reduceDIte, Circuit.eval_wiring,
        Function.comp_apply, decode_one, hv]
      exact (testBit_wordValue x 0).symm
    · have hw : 2 ≤ w := by omega
      rw [decode_eq_xor_highBits hw, hv]
      simp only [decodeWord, h₀, h₁, ↓reduceDIte, Formula.eval_toCircuit,
        Formula.eval_xor, Formula.eval_input]
      rw [testBit_wordValue x ⟨w - 1, by omega⟩,
        testBit_wordValue x ⟨w - 2, by omega⟩]

private theorem depth_decodeWord_le (w : ℕ) : (decodeWord w).depth ≤ 3 := by
  unfold decodeWord
  split_ifs
  · simp
  · simp
  · exact (Formula.depth_toCircuit_le _).trans
      ((Formula.depth_xor_le _ _).trans (by simp))

private theorem size_decodeWord_le (w : ℕ) : (decodeWord w).size ≤ 5 := by
  unfold decodeWord
  split_ifs <;> simp

/-- The actual total GSW decryptor, with all raw secret and ciphertext bits as inputs. -/
def circuit (n w : ℕ) : Circuit signature (inputWidth n w) 1 :=
  if hw : 0 < w then (decodeWord w).comp (phase n w hw)
  else Circuit.oneGate (.const false) Fin.elim0

/-- All raw inputs agree with typed GSW decryption, without generation or noise hypotheses. -/
private theorem eval_circuit (x : BitString (inputWidth n w)) :
    (circuit n w).eval interpretation x 0 = decrypt (inputSecret x) (inputCiphertext x) := by
  by_cases hw : 0 < w
  · rw [circuit, dite_eq_left hw, Circuit.eval_comp, eval_decodeWord, phase_cast x hw,
      decrypt_eq_decode_decryptionPhase hw]
    rfl
  · have hz : w = 0 := by omega
    subst w
    simp [circuit, interpretation]

/-- The selected-row construction has logarithmic depth in both parameter dimensions. -/
theorem depth_circuit_le (n w : ℕ) :
    (circuit n w).depth ≤ 28 + 18 * Nat.clog 2 (w + 1) + 12 * Nat.clog 2 n := by
  have hp : ∀ hw, (productSum n w hw).depth ≤
      17 + 16 * Nat.clog 2 (w + 1) + 12 * Nat.clog 2 n := by
    intro hw
    exact (Circuit.depth_comp_le _ _).trans (by
      simpa only [Circuit.depth_wiring, add_zero] using Modular.depth_innerProduct_le n w)
  have hphase : ∀ hw, (phase n w hw).depth ≤
      25 + 18 * Nat.clog 2 (w + 1) + 12 * Nat.clog 2 n := by
    intro hw
    have ha := Circuit.depth_append_le
      (Circuit.wiring signature (rowInputs n w hw 0)) (productSum n w hw)
    simp only [Circuit.depth_wiring, zero_max] at ha
    have hc := Circuit.depth_comp_le (Modular.subtract w)
      ((Circuit.wiring signature (rowInputs n w hw 0)).append (productSum n w hw))
    have hs := Modular.depth_subtract_le w
    have hi := hp hw
    change (phase n w hw).depth ≤ _ at hc
    omega
  unfold circuit
  split_ifs with hw
  · have hc := Circuit.depth_comp_le (decodeWord w) (phase n w hw)
    have hd := depth_decodeWord_le w
    have hp := hphase hw
    omega
  · simp only [Circuit.depth_oneGate]
    omega

/-- Polynomial gate count includes all unused fallback gates in the balanced construction. -/
theorem size_circuit_le (n w : ℕ) :
    (circuit n w).size ≤ 131 * (n + 1) * (w + 1) ^ 2 := by
  unfold circuit
  split_ifs with hw
  · simp only [Circuit.size_comp, phase, productSum, Circuit.size_append,
      Circuit.size_wiring, zero_add]
    have hd := size_decodeWord_le w
    have hs := Modular.size_subtract_le w
    have hi := Modular.size_innerProduct_le n w
    nlinarith [Nat.zero_le n, Nat.zero_le (n * w), Nat.zero_le (n * w ^ 2)]
  · simp only [Circuit.size_oneGate]
    nlinarith [Nat.zero_le n, Nat.zero_le (n * w), Nat.zero_le (n * w ^ 2)]

/-- The serialized contract required by generic refresh: every well-sized raw pair is covered. -/
theorem correct (n w : ℕ) (secret ciphertext : List Bool)
    (hs : secret.length = n * w)
    (hc : ciphertext.length = ((n + 1) * w) * ((n + 1) * w)) :
    (circuit n w).eval interpretation (ofList (inputWidth n w) (secret ++ ciphertext)) 0 =
      decryptSerialized n w secret ciphertext := by
  change (circuit n w).eval interpretation
    (ofList (n * w + ((n + 1) * w) * ((n + 1) * w)) (secret ++ ciphertext)) 0 = _
  rw [ofList_append hs hc, eval_circuit, decryptSerialized_eq]
  simp only [inputSecret, inputCiphertext, fstBits_append, sndBits_append,
    ofFn_ofList hs, ofFn_ofList hc]

end Cslib.Crypto.Homomorphic.GSW.DecryptionCircuit
