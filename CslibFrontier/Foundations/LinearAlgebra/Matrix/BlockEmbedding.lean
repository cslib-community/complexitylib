/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Entrywise representations as block matrices

A ring homomorphism from `R` to square matrices over `S` extends entrywise to a ring homomorphism
from square matrices over `R` to flattened block matrices over `S`. The extension is faithful when
the entry representation is faithful.

## Main definitions

* `Matrix.blockEmbedding`: extend a matrix representation entrywise to block matrices.

## Main results

* `Matrix.blockEmbedding_apply`: evaluate an entry of the flattened block matrix.
* `Matrix.blockEmbedding_injective`: an injective entry representation gives an injective block
  representation.

## References

The definition is extracted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a
([BlockDivision.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BlockDivision.lean)),
via the complexitylib port [Schlesinger2026RationalHitting] at revision
add0aca8ee0d71e68969f2cb45cf91554a50f787.

The same construction is the block lift `ϕ` in the *QR-UOV Round-3 Specification*
[QRUOV2026], §4.1, p. 16, applied to the injective regular representation of quotient-ring
multiplication from Equation (4) and Lemma 1 in §3.2, p. 12.
-/

public section

namespace Matrix

variable {R S m κ : Type*} [Semiring R] [Semiring S]
  [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-- Extend a matrix representation entrywise to flattened block matrices. Its body is exposed so
ordinary importing modules can use the entrywise evaluation law. -/
@[expose] def blockEmbedding (φ : R →+* Matrix κ κ S) :
    Matrix m m R →+* Matrix (m × κ) (m × κ) S where
  toFun A i j := φ (A i.1 j.1) i.2 j.2
  map_zero' := by ext i j; simp
  map_one' := by
    ext ⟨i, α⟩ ⟨j, β⟩
    simp only [Matrix.one_apply, Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases hab : α = β <;> simp [hij, hab]
  map_add' A B := by
    ext i j
    change φ (A i.1 j.1 + B i.1 j.1) i.2 j.2 = _ + _
    simp
  map_mul' A B := by
    ext ⟨i, α⟩ ⟨j, β⟩
    change φ (∑ k, A i k * B k j) α β =
      ∑ k : m × κ, φ (A i k.1) α k.2 * φ (B k.1 j) k.2 β
    simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_prod_type]

/-- An entry of the flattened block matrix is the corresponding entry of the represented source
entry. -/
theorem blockEmbedding_apply (φ : R →+* Matrix κ κ S) (A : Matrix m m R) (i j : m × κ) :
    blockEmbedding φ A i j = φ (A i.1 j.1) i.2 j.2 :=
  rfl

/-- Extending an injective entry representation to block matrices remains injective. -/
theorem blockEmbedding_injective (φ : R →+* Matrix κ κ S) (hφ : Function.Injective φ) :
    Function.Injective (blockEmbedding (m := m) φ) := by
  intro A B hAB
  ext i j
  apply hφ
  ext α β
  exact congrFun (congrFun hAB (i, α)) (j, β)

end Matrix
