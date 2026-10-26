/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Decoding
public import Complexity.Crypto.Computational.Homomorphic.GSW.Noise
public import Complexity.Crypto.Computational.LWE.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The deterministic GSW encryption core

This module constructs the actual public matrix, encryption with explicit binary coins, and
NAND operation of [Gentry, Sahai and Waters][GentrySahaiWaters2013]. The modulus is `2 ^ w`,
with `w` digits per secret coordinate and `N = (n + 1) * w` ciphertext rows and columns.
As documented in `GSW.Gadget`, this omits the paper's redundant top digit at this modulus.
Ciphertexts are Boolean matrices, so encryption and NAND preserve their dimensions and binary
entry invariant by construction. Integer errors witness the modular approximate-eigenvector
equations; their magnitudes are bounded separately.

The inputs to key construction and encryption are explicit. No distribution, computational
security, native complexity bound, admissible parameter family or bootstrappability theorem is
asserted here. In particular, the pointwise error bounds do not follow merely from a negligible
probability of excessive noise.

## Main definitions

* `Ciphertext`, `secretVector`, `publicMatrix`: the bit-matrix ciphertext and actual key formulas.
* `encryptWithCoins`, `nand`, `decrypt`: the actual deterministic algorithms.
* `HasError`: the modular equation witnessed by an explicit integer error vector.

## Main results

* `encryptWithCoins_hasError`: the encryption error is the integer subset sum `R * error`.
* `recomposeMatrix_encryptWithCoins`: the public ciphertext recomposes to `μ * G + R * A`.
* `encryptWithCoins_eq_decomposeMatrix`: the ciphertext is the bit decomposition of that matrix.
* `nand_hasError`: the actual NAND operation has the stated propagated integer error.
* `decrypt_eq_of_hasError`: the decoder recovers a bit below its explicit noise threshold.
* `decrypt_encryptWithCoins`, `decrypt_nand`: correctness from input noise bounds.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Sections 3.1--3.4]
  [GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open _root_.Matrix
open scoped _root_.Matrix

/-- A square Boolean ciphertext with `(n + 1) * w` rows and columns. -/
abbrev Ciphertext (n w : ℕ) := Matrix (Fin (n + 1) × Fin w) (Fin (n + 1) × Fin w) Bool

/-- The secret vector has leading coordinate one, followed by the negated secret entries. -/
def secretVector {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) : Fin (n + 1) → ZMod (2 ^ w) :=
  Fin.cons 1 (-t)

/-- The public matrix is `[B * t + error | B]`, with integer errors cast modulo `2 ^ w`. -/
def publicMatrix {n m w : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ℤ) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) :=
  LWE.publicMatrix B t fun i => (error i : ZMod (2 ^ w))

/-- The constructed public matrix has exactly the chosen error against the secret vector. -/
theorem publicMatrix_mulVec_secretVector {n m w : ℕ}
    (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (t : Fin n → ZMod (2 ^ w)) (error : Fin m → ℤ) :
    publicMatrix B t error *ᵥ secretVector t = fun i => (error i : ZMod (2 ^ w)) := by
  ext i
  simp [publicMatrix, LWE.publicMatrix, secretVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The public gadget matrix obtained by recomposing the identity. -/
def gadgetMatrix (n w : ℕ) : Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w)) :=
  recomposeMatrix w 1

/-- A gadget row contains its binary place value at its original coordinate and zero elsewhere. -/
theorem gadgetMatrix_apply {n w : ℕ} (i : Fin (n + 1)) (k : Fin w) (j : Fin (n + 1)) :
    gadgetMatrix n w (i, k) j = if i = j then 2 ^ k.val else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [gadgetMatrix, recomposeMatrix, bitCompose, _root_.Matrix.one_apply, Prod.mk.injEq]
  · simp [gadgetMatrix, recomposeMatrix, bitCompose, Prod.mk.injEq, h]

/-- Encrypt using only the public matrix, the Boolean message, and binary coins. -/
def encryptWithCoins {n m w : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))
    (μ : Bool) (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) : Ciphertext n w :=
  flattenMatrix w ((μ.toNat : ZMod (2 ^ w)) • 1 +
    bitMatrix (ZMod (2 ^ w)) (decomposeMatrix w (bitMatrix (ZMod (2 ^ w)) R * A)))

/-- The actual ciphertext is the canonical decomposition of its message shift and subset sums. -/
theorem encryptWithCoins_eq_decomposeMatrix {n m w : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (μ : Bool)
    (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    encryptWithCoins A μ R = decomposeMatrix w
      ((μ.toNat : ZMod (2 ^ w)) • gadgetMatrix n w + bitMatrix (ZMod (2 ^ w)) R * A) := by
  simp only [encryptWithCoins, flattenMatrix, recomposeMatrix_add, recomposeMatrix_smul,
    recomposeMatrix_decomposeMatrix, gadgetMatrix]

/-- Homomorphic NAND, with dimensions and binary output entries preserved structurally. -/
def nand {n w : ℕ} (C₁ C₂ : Ciphertext n w) : Ciphertext n w :=
  flattenMatrix w (1 - bitMatrix (ZMod (2 ^ w)) C₁ * bitMatrix (ZMod (2 ^ w)) C₂)

/-- The ciphertext's modular product equals the encoded message plus an explicit integer error.
This relation does not impose a size bound on the error. -/
def HasError {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w)
    (μ : Bool) (error : Fin (n + 1) × Fin w → ℤ) : Prop :=
  bitMatrix (ZMod (2 ^ w)) C *ᵥ powersOfTwo w (secretVector t) =
    (μ.toNat : ZMod (2 ^ w)) • powersOfTwo w (secretVector t) +
      fun i => (error i : ZMod (2 ^ w))

/-- Decode the highest digit of the leading secret coordinate. Width zero returns `false`. -/
def decrypt {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w) : Bool :=
  if hw : 0 < w then
    decode w ((bitMatrix (ZMod (2 ^ w)) C *ᵥ powersOfTwo w (secretVector t))
      (0, ⟨w - 1, by omega⟩))
  else false

/-- Recomposition exposes the exact public form used by the later security reduction. -/
theorem recomposeMatrix_encryptWithCoins {n m w : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w))) (μ : Bool)
    (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (encryptWithCoins A μ R)) =
      (μ.toNat : ZMod (2 ^ w)) • gadgetMatrix n w + bitMatrix (ZMod (2 ^ w)) R * A := by
  rw [encryptWithCoins, recomposeMatrix_flattenMatrix, recomposeMatrix_add,
    recomposeMatrix_smul, recomposeMatrix_decomposeMatrix]
  rfl

/-- Encryption with the actual public key has the exact integer error selected by its coins. -/
theorem encryptWithCoins_hasError {n m w : ℕ}
    (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w))) (t : Fin n → ZMod (2 ^ w))
    (error : Fin m → ℤ) (μ : Bool) (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool) :
    HasError t (encryptWithCoins (publicMatrix B t error) μ R) μ (encryptionError R error) := by
  unfold HasError encryptWithCoins
  rw [flattenMatrix_mulVec, add_mulVec, smul_mulVec, one_mulVec, decomposeMatrix_mulVec,
    ← mulVec_mulVec, publicMatrix_mulVec_secretVector, bitMatrix_mulVec_intCast]

/-- The actual NAND formula has error `-μ₂ * error₁ - C₁ * error₂` over the integers. -/
theorem nand_hasError {n w : ℕ} (t : Fin n → ZMod (2 ^ w))
    (C₁ C₂ : Ciphertext n w) (μ₁ μ₂ : Bool)
    (error₁ error₂ : Fin (n + 1) × Fin w → ℤ)
    (hC₁ : HasError t C₁ μ₁ error₁) (hC₂ : HasError t C₂ μ₂ error₂) :
    HasError t (nand C₁ C₂) (!(μ₁ && μ₂)) (nandError C₁ μ₂ error₁ error₂) := by
  unfold HasError at hC₁ hC₂ ⊢
  rw [nand, flattenMatrix_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hC₂,
    mulVec_add, mulVec_smul, hC₁, bitMatrix_mulVec_intCast]
  funext i
  cases μ₁ <;> cases μ₂ <;> simp [nandError, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Every Boolean ciphertext satisfying the actual modular equation decrypts correctly under
the strict integer noise margin, whether it is fresh or produced by prior NAND operations. -/
theorem decrypt_eq_of_hasError {n w : ℕ} (hw : 0 < w)
    (t : Fin n → ZMod (2 ^ w)) (C : Ciphertext n w) (μ : Bool)
    (error : Fin (n + 1) × Fin w → ℤ) (hC : HasError t C μ error)
    (herror : ∀ i, 4 * (error i).natAbs < 2 ^ w) : decrypt t C = μ := by
  let i : Fin (n + 1) × Fin w := (0, ⟨w - 1, by omega⟩)
  simp only [decrypt, dite_eq_left hw]
  rw [hC]
  simpa [i, powersOfTwo, secretVector] using
    decode_eq_of_error hw μ (error i) (herror i)

/-- Fresh encryption is correct whenever the sum bound on its integer errors fits below
one quarter of the modulus. This holds for every binary choice of encryption coins. -/
theorem decrypt_encryptWithCoins {n m w bound : ℕ}
    (B : Matrix (Fin m) (Fin n) (ZMod (2 ^ w))) (t : Fin n → ZMod (2 ^ w))
    (error : Fin m → ℤ) (μ : Bool) (R : Matrix (Fin (n + 1) × Fin w) (Fin m) Bool)
    (hw : 0 < w) (herror : ∀ j, (error j).natAbs ≤ bound)
    (hmargin : 4 * (m * bound) < 2 ^ w) :
    decrypt t (encryptWithCoins (publicMatrix B t error) μ R) = μ := by
  apply decrypt_eq_of_hasError hw t _ μ _ (encryptWithCoins_hasError B t error μ R)
  intro i
  have hbound : (encryptionError R error i).natAbs ≤ m * bound := by
    simpa using encryptionError_natAbs_le R error herror i
  exact (Nat.mul_le_mul_left 4 hbound).trans_lt hmargin

/-- NAND is correct under its actual propagated noise bound. The inputs can themselves be
outputs of earlier operations, provided their integer error equations and bounds hold. -/
theorem decrypt_nand {n w bound₁ bound₂ : ℕ}
    (t : Fin n → ZMod (2 ^ w)) (C₁ C₂ : Ciphertext n w) (μ₁ μ₂ : Bool)
    (error₁ error₂ : Fin (n + 1) × Fin w → ℤ)
    (hC₁ : HasError t C₁ μ₁ error₁) (hC₂ : HasError t C₂ μ₂ error₂)
    (hw : 0 < w)
    (herror₁ : ∀ i, (error₁ i).natAbs ≤ bound₁)
    (herror₂ : ∀ i, (error₂ i).natAbs ≤ bound₂)
    (hmargin : 4 * (bound₁ + ((n + 1) * w) * bound₂) < 2 ^ w) :
    decrypt t (nand C₁ C₂) = !(μ₁ && μ₂) := by
  apply decrypt_eq_of_hasError hw t _ _ _ (nand_hasError t C₁ C₂ μ₁ μ₂ error₁ error₂ hC₁ hC₂)
  intro i
  have hbound : (nandError C₁ μ₂ error₁ error₂ i).natAbs ≤
      bound₁ + ((n + 1) * w) * bound₂ := by
    simpa using nandError_natAbs_le C₁ μ₂ error₁ error₂ herror₁ herror₂ i
  exact (Nat.mul_le_mul_left 4 hbound).trans_lt hmargin

end Cslib.Crypto.Homomorphic.GSW
