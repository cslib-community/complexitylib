/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact row arithmetic for GSW decryption

The expanded-secret product used by `GSW.decrypt` equals one recomposed ciphertext row
paired with the unexpanded secret. Its first coordinate is subtracted by the sum of the
remaining coordinates times the secret entries. For width at least two, decryption is
exclusive-or of the two highest bits of this residue.

These identities hold on every typed secret and Boolean ciphertext. They require no key
generation, encryption support or noise hypothesis, as needed for a decryption circuit
correct on all well-sized raw inputs. They do not yet construct that circuit or bound its depth.

## Main definitions

* `decryptionPhase`: the recomposed row's modular inner product with the secret vector.

## Main results

* `decryptionPhase_eq_mulVec`: the row expression equals the original expanded-secret product.
* `decrypt_eq_decode_decryptionPhase`: decryption uses the highest row of the leading coordinate.
* `decrypt_eq_xor_highBits`: the two highest bits determine decryption at width at least two.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*][GentrySahaiWaters2013],
  Sections 3.1 and 3.4.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open _root_.Matrix
open scoped _root_.Matrix

/-- Recompose one ciphertext row, then take its inner product with `(1,-t)`. -/
def decryptionPhase {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w)
    (row : Fin (n + 1) × Fin w) : ZMod (2 ^ w) :=
  recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) C) row 0 -
    ∑ j : Fin n, recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) C) row j.succ * t j

/-- Row recomposition preserves the original multiplication by the expanded secret. -/
theorem decryptionPhase_eq_mulVec {n w : ℕ} (t : Fin n → ZMod (2 ^ w))
    (C : Ciphertext n w) (row : Fin (n + 1) × Fin w) :
    decryptionPhase t C row =
      (bitMatrix (ZMod (2 ^ w)) C *ᵥ powersOfTwo w (secretVector t)) row := by
  rw [← recomposeMatrix_mulVec]
  simp [decryptionPhase, Matrix.mulVec, dotProduct, secretVector, Fin.sum_univ_succ,
    sub_eq_add_neg]

/-- The total width-zero decryption routine returns `false`. -/
@[simp] theorem decrypt_zero {n : ℕ} (t : Fin n → ZMod (2 ^ 0)) (C : Ciphertext n 0) :
    decrypt t C = false := by
  simp [decrypt]

/-- At positive width, decryption reads the highest digit of the leading coordinate. -/
theorem decrypt_eq_decode_decryptionPhase {n w : ℕ} (hw : 0 < w)
    (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w) :
    decrypt t C = decode w (decryptionPhase t C (0, ⟨w - 1, by omega⟩)) := by
  rw [decryptionPhase_eq_mulVec]
  simp [decrypt, hw]

/-- At width one, decryption is the sole bit of the selected row's phase. -/
theorem decrypt_one {n : ℕ} (t : Fin n → ZMod (2 ^ 1)) (C : Ciphertext n 1) :
    decrypt t C = (decryptionPhase t C (0, 0)).val.testBit 0 := by
  rw [decrypt_eq_decode_decryptionPhase (by decide), decode_one]
  rfl

/-- At width at least two, all raw ciphertexts decrypt by exclusive-or of two phase bits. -/
theorem decrypt_eq_xor_highBits {n w : ℕ} (hw : 2 ≤ w)
    (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w) :
    decrypt t C =
      ((decryptionPhase t C (0, ⟨w - 1, by omega⟩)).val.testBit (w - 1) ^^
        (decryptionPhase t C (0, ⟨w - 1, by omega⟩)).val.testBit (w - 2)) := by
  rw [decrypt_eq_decode_decryptionPhase (by omega), decode_eq_xor_highBits hw]

end Cslib.Crypto.Homomorphic.GSW
