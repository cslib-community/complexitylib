/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, the rank and the action on vectors of a Kronecker product)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# The rank of a Kronecker product, and its action on vectors

Over a commutative semiring, a Kronecker product acts on vectors indexed by pairs factor by factor:
`(A ⊗ₖ B) v` is computed by applying `A` to the first index and `B` to the second
(`Matrix.kronecker_mulVec_mul` for a product vector `v (i, k) = x i * y k`). With an identity
factor, `A ⊗ₖ 1` acts as `A` on the first index (`Matrix.kronecker_one_mulVec_apply`) and `1 ⊗ₖ B`
as `B` on the second (`Matrix.one_kronecker_mulVec_apply`).

Over a field, a matrix of rank `r` factors through `r`-dimensional space
(`Matrix.exists_eq_mul_rank`). Applying this to both factors of a Kronecker product and using
`Matrix.mul_kronecker_mul` bounds the rank of `A ⊗ₖ B` by `A.rank * B.rank`
(`Matrix.rank_kronecker_le`). Equality holds as well, but only the upper bound is proved here.

## Main results

* `Matrix.kronecker_mulVec_mul`: `(A ⊗ₖ B)(x ⊗ y) = Ax ⊗ By`.
* `Matrix.kronecker_one_mulVec_apply`, `Matrix.one_kronecker_mulVec_apply`: the action of `A ⊗ₖ 1`
  and `1 ⊗ₖ B`.
* `Matrix.rank_kronecker_le`: `(A ⊗ₖ B).rank ≤ A.rank * B.rank`.

## References

These are standard facts of linear algebra. The Kronecker bound is the "≤" half of the
multiplicativity of rank used for Claim 7(3) of
[N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
circuits*][LimayeSrinivasanTavenas2021], pp. 6–7.
-/

public section

namespace Matrix

open Kronecker

section MulVec

variable {R : Type*} {l m n p : Type*}

/-- `(A ⊗ₖ B)(x ⊗ y) = Ax ⊗ By`: a Kronecker product maps a product vector to the product of the
images. -/
theorem kronecker_mulVec_mul [CommSemiring R] [Fintype m] [Fintype p] (A : Matrix l m R)
    (B : Matrix n p R) (x : m → R) (y : p → R) :
    (A ⊗ₖ B) *ᵥ (fun q => x q.1 * y q.2) = fun q => (A *ᵥ x) q.1 * (B *ᵥ y) q.2 := by
  funext q
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- `A ⊗ₖ 1` acts as `A` on the first index. -/
theorem kronecker_one_mulVec_apply [NonAssocSemiring R] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix l m R) (v : m × n → R) (q : l × n) :
    ((A ⊗ₖ (1 : Matrix n n R)) *ᵥ v) q = (A *ᵥ fun i => v (i, q.2)) q.1 := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single q.2 (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp

/-- `1 ⊗ₖ B` acts as `B` on the second index. -/
theorem one_kronecker_mulVec_apply [NonAssocSemiring R] [Fintype m] [Fintype p] [DecidableEq m]
    (B : Matrix n p R) (v : m × p → R) (q : m × n) :
    (((1 : Matrix m m R) ⊗ₖ B) *ᵥ v) q = (B *ᵥ fun k => v (q.1, k)) q.2 := by
  rw [mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single q.1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp [mulVec, dotProduct]

end MulVec

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
