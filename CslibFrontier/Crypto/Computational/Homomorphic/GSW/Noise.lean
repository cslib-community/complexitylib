/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Gadget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Integer noise witnesses for GSW encryption

The modular ciphertext equations use explicit integer errors. A binary matrix sends an error
vector to a subset sum in each row. Fresh encryption therefore has error at most the sum of the
input magnitudes. For NAND, the first ciphertext multiplies the second error, and the second
message multiplies the first error. These bounds use the structural Boolean-entry invariant.

## Main definitions

* `encryptionError`: the integer subset sums selected by the encryption coins.
* `nandError`: the exact propagated integer error for the NAND operation.

## Main results

* `encryptionError_natAbs_le`: `m` errors bounded by `B` give fresh error at most `m * B`.
* `nandError_natAbs_le`: errors bounded by `B₁`, `B₂` give NAND error at most `B₁ + N * B₂`.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Sections 3.1 and 3.3]
  [GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Finset
open scoped Matrix

/-- The integer error selected by each binary row of encryption coins. -/
def encryptionError {ι κ : Type*} [Fintype κ] (R : Matrix ι κ Bool)
    (error : κ → ℤ) : ι → ℤ :=
  bitMatrix ℤ R *ᵥ error

/-- Each fresh error is bounded by the sum of the original integer error magnitudes. -/
theorem encryptionError_natAbs_le_sum {ι κ : Type*} [Fintype κ]
    (R : Matrix ι κ Bool) (error : κ → ℤ) (i : ι) :
    (encryptionError R error i).natAbs ≤ ∑ j, (error j).natAbs := by
  change (∑ j, ((R i j).toNat : ℤ) * error j).natAbs ≤ _
  refine (Int.natAbs_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  cases R i j <;> simp

/-- A uniform bound on the input errors gives the usual fresh-encryption noise bound. -/
theorem encryptionError_natAbs_le {ι κ : Type*} [Fintype κ]
    (R : Matrix ι κ Bool) (error : κ → ℤ) {bound : ℕ}
    (herror : ∀ j, (error j).natAbs ≤ bound) (i : ι) :
    (encryptionError R error i).natAbs ≤ Fintype.card κ * bound := by
  refine (encryptionError_natAbs_le_sum R error i).trans ?_
  simpa using sum_le_sum (s := univ) (fun j _ => herror j)

/-- Casting the integer subset sums agrees with the modular matrix computation. -/
theorem bitMatrix_mulVec_intCast {ι κ : Type*} [Fintype κ] (w : ℕ)
    (R : Matrix ι κ Bool) (error : κ → ℤ) :
    bitMatrix (ZMod (2 ^ w)) R *ᵥ (fun j => (error j : ZMod (2 ^ w))) =
      fun i => (encryptionError R error i : ZMod (2 ^ w)) := by
  ext i
  simp [encryptionError, bitMatrix, Matrix.mulVec, dotProduct, Int.cast_sum]

/-- The exact NAND error: the second message scales the first error, while the first
ciphertext multiplies the second error. -/
def nandError {ι : Type*} [Fintype ι] (C₁ : Matrix ι ι Bool)
    (μ₂ : Bool) (error₁ error₂ : ι → ℤ) : ι → ℤ :=
  fun i => -((μ₂.toNat : ℤ) * error₁ i) - encryptionError C₁ error₂ i

/-- NAND increases error from `B₁`, `B₂` to at most `B₁ + N * B₂`. -/
theorem nandError_natAbs_le {ι : Type*} [Fintype ι]
    (C₁ : Matrix ι ι Bool) (μ₂ : Bool) (error₁ error₂ : ι → ℤ)
    {bound₁ bound₂ : ℕ}
    (herror₁ : ∀ i, (error₁ i).natAbs ≤ bound₁)
    (herror₂ : ∀ i, (error₂ i).natAbs ≤ bound₂) (i : ι) :
    (nandError C₁ μ₂ error₁ error₂ i).natAbs ≤ bound₁ + Fintype.card ι * bound₂ := by
  refine (Int.natAbs_sub_le _ _).trans (Nat.add_le_add ?_
    (encryptionError_natAbs_le C₁ error₂ herror₂ i))
  cases μ₂
  · simp
  · simpa using herror₁ i

end Cslib.Crypto.Homomorphic.GSW
