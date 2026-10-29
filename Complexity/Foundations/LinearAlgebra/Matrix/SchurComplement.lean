/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Invertibility and Schur complements for 2×2 block matrices over general rings

This module establishes invertibility criteria and factorizations for 2×2 block matrices over
arbitrary (possibly noncommutative) rings `R`.

Mathlib's `Mathlib.LinearAlgebra.Matrix.SchurComplement` proves analogous results
(`fromBlocks_eq_of_invertible₁₁`, `isUnit_fromBlocks_iff_of_invertible₁₁`,
`isUnit_fromBlocks_zero₂₁`) for commutative rings (`[CommRing α]`). The lemmas here generalize those
results to the $D = 0$ cases over arbitrary rings `[Ring R]`, which is required when the matrix
entries themselves are matrices (e.g. in rational circuit evaluations).

## Main results

* `Matrix.isUnit_fromBlocks_one_zero₂₁`: an upper unitriangular block matrix is invertible.
* `Matrix.isUnit_fromBlocks_one_zero₁₂`: a lower unitriangular block matrix is invertible.
* `Matrix.isUnit_fromBlocks_diagonal_iff`: a block diagonal matrix is invertible iff both diagonal
  blocks are.
* `Matrix.fromBlocks_zero₂₂_schur_factor`: Schur factorization of a block matrix with a zero
  corner and an invertible corner.
* `Matrix.isUnit_fromBlocks_zero₂₂_iff`: invertibility of a block matrix with a zero corner via
  its Schur complement.
* `Matrix.inv_smul_mul_smul`, `Matrix.inv_smul_mul_smul_of_ne_zero`: rescaling two matrices by the
  same invertible scalar cancels in `(c • A)⁻¹ * (c • B) = A⁻¹ * B`.

## References

* [OpenAI2026RationalHitting]
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- An upper unitriangular block matrix is invertible. -/
theorem isUnit_fromBlocks_one_zero₂₁ (B : Matrix ι κ R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) B 0 (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 (-B) 0 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A lower unitriangular block matrix is invertible. -/
theorem isUnit_fromBlocks_one_zero₁₂ (C : Matrix κ ι R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 0 (-C) 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A block diagonal matrix is invertible exactly when both diagonal blocks are. -/
theorem isUnit_fromBlocks_diagonal_iff (A : Matrix ι ι R) (D : Matrix κ κ R) :
    IsUnit (fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [isUnit_iff_exists]
  constructor
  · rintro ⟨B, hAB, hBA⟩
    rw [← fromBlocks_toBlocks B, fromBlocks_multiply, ← fromBlocks_one] at hAB hBA
    simp only [fromBlocks_inj, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hAB hBA
    exact ⟨⟨B.toBlocks₁₁, hAB.1, hBA.1⟩, ⟨B.toBlocks₂₂, hAB.2.2.2, hBA.2.2.2⟩⟩
  · rintro ⟨⟨A', hAA', hA'A⟩, ⟨D', hDD', hD'D⟩⟩
    refine ⟨fromBlocks A' 0 0 D', ?_, ?_⟩ <;>
      simp [fromBlocks_multiply, hAA', hA'A, hDD', hD'D]

/-- The Schur factorization of a block matrix with a zero corner and an invertible corner. -/
theorem fromBlocks_zero₂₂_schur_factor (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    fromBlocks A B C 0 =
      fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-C * A' * B) *
      fromBlocks 1 (A' * B) 0 1 := by
  simp only [fromBlocks_multiply, add_zero, zero_add,
    one_mul, mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc A A' B, hAA', Matrix.one_mul, Matrix.mul_assoc C A' A, hA'A,
    Matrix.mul_one]
  simp [Matrix.mul_assoc, Matrix.neg_mul]

/-- A block matrix with a zero corner and an invertible corner is invertible exactly when its
Schur complement is. -/
theorem isUnit_fromBlocks_zero₂₂_iff (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    IsUnit (fromBlocks A B C 0) ↔ IsUnit (C * A' * B) := by
  rw [fromBlocks_zero₂₂_schur_factor A A' B C hAA' hA'A]
  obtain ⟨u, hu⟩ := isUnit_fromBlocks_one_zero₂₁ (A' * B)
  obtain ⟨v, hv⟩ := isUnit_fromBlocks_one_zero₁₂ (C * A')
  rw [← hu, ← hv, Units.isUnit_mul_units, Units.isUnit_units_mul, isUnit_fromBlocks_diagonal_iff]
  have hA : IsUnit A := isUnit_iff_exists.mpr ⟨A', hAA', hA'A⟩
  simp [hA, Matrix.neg_mul, IsUnit.neg_iff]

/-- Rescaling two matrices by the same invertible scalar cancels in `(c • A)⁻¹ * (c • B) = A⁻¹ * B`
when `A.det` is a unit. -/
theorem inv_smul_mul_smul {S : Type*} [CommRing S] {m : Type*} (A : Matrix ι ι S)
    (B : Matrix ι m S) (hA : IsUnit A.det) (c : S) [Invertible c] :
    (c • A)⁻¹ * (c • B) = A⁻¹ * B := by
  have hi : (c • A)⁻¹ = ⅟c • A⁻¹ := Matrix.inv_smul (A := A) c hA
  rw [hi, Matrix.smul_mul, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul]

/-- Over a field, rescaling two matrices by the same nonzero scalar cancels in
`(c • A)⁻¹ * (c • B) = A⁻¹ * B` when `A.det ≠ 0`. -/
theorem inv_smul_mul_smul_of_ne_zero {K : Type*} [Field K] {m : Type*} (A : Matrix ι ι K)
    (B : Matrix ι m K) (hA : A.det ≠ 0) {c : K} (hc : c ≠ 0) :
    (c • A)⁻¹ * (c • B) = A⁻¹ * B := by
  let : Invertible c := invertibleOfNonzero hc
  exact inv_smul_mul_smul A B (isUnit_iff_ne_zero.mpr hA) c

end Matrix
