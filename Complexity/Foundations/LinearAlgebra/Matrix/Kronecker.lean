/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, the rank of a Kronecker product)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
import Complexity.Foundations.LinearAlgebra.Matrix.Rank

/-!
# The rank of a Kronecker product

Over a field, a matrix of rank `r` factors through `r`-dimensional space
(`Matrix.exists_eq_mul_rank`). Applying this to both factors of a Kronecker product and using
`Matrix.mul_kronecker_mul` bounds the rank of `A ⊗ₖ B` by `A.rank * B.rank`
(`Matrix.rank_kronecker_le`). Equality holds as well, but only the upper bound is proved here.

## Main results

* `Matrix.rank_kronecker_le`: `(A ⊗ₖ B).rank ≤ A.rank * B.rank`.

## References

These are standard facts of linear algebra. The Kronecker bound is the "≤" half of the
multiplicativity of rank used for Claim 7(3) of
[N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
circuits*][LimayeSrinivasanTavenas2021], pp. 6–7.
-/

@[expose] public section

namespace Matrix

open Kronecker

variable {K : Type*} [Field K] {l m n p : Type*}

/-- **The rank of a Kronecker product** is at most the product of the ranks. -/
theorem rank_kronecker_le [Fintype m] [Fintype p] (A : Matrix l m K) (B : Matrix n p K) :
    (A ⊗ₖ B).rank ≤ A.rank * B.rank := by
  obtain ⟨C, D, hA⟩ := A.exists_eq_mul_rank
  obtain ⟨E, F, hB⟩ := B.exists_eq_mul_rank
  calc (A ⊗ₖ B).rank = (C ⊗ₖ E * D ⊗ₖ F).rank := by rw [← mul_kronecker_mul, ← hA, ← hB]
    _ ≤ (C ⊗ₖ E).rank := rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin A.rank × Fin B.rank) := rank_le_card_width _
    _ = A.rank * B.rank := by simp

end Matrix
