/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.BlockEmbedding
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Tests for faithful block-matrix embeddings

An ordinary importing module checks the exact QR-UOV composition: Mathlib's regular
representation records multiplication in a basis, and its entrywise block lift is injective.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.MatrixBlockEmbedding

open Module Matrix

variable {R S m κ : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]

/-- Equation (4) of the QR-UOV specification: a regular-representation entry is the coefficient
of multiplication by the represented element. -/
example (b : Basis κ R S) (A : Matrix m m S) (i j : m) (α β : κ) :
    blockEmbedding (Algebra.leftMulMatrix b).toRingHom A (i, α) (j, β) =
      b.repr (A i j * b β) α := by
  rw [blockEmbedding_apply]
  change Algebra.leftMulMatrix b (A i j) α β = b.repr (A i j * b β) α
  exact Algebra.leftMulMatrix_eq_repr_mul b (A i j) α β

/-- Lemma 1's faithful regular representation remains faithful after the source's block lift
`ϕ`. -/
example (b : Basis κ R S) : Function.Injective
    (blockEmbedding (m := m) (Algebra.leftMulMatrix b).toRingHom) :=
  blockEmbedding_injective _ (Algebra.leftMulMatrix_injective b)

end CslibFrontierTests.Foundations.MatrixBlockEmbedding
