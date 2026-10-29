/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (Mathlib, subadditivity of matrix rank and rank factorization)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Subadditivity of matrix rank and rank factorization

Over a field, the column space of `A + B` lies in the sum of the column spaces of `A` and `B`, so
the rank of a sum of matrices is at most the sum of their ranks (`Matrix.rank_add_le`). Negation
does not change the rank (`Matrix.rank_neg`), and scaling does not increase it, over any commutative
semiring with the strong rank condition (`Matrix.rank_smul_le`). The natural matrix rank also
agrees with the cardinal rank of `Matrix.toLin'` (`Matrix.natCast_rank_eq_rank_toLin'`), and a
matrix of rank `r` factors through `r`-dimensional space (`Matrix.exists_eq_mul_rank`).

## Main results

* `Matrix.rank_add_le`, `Matrix.rank_sub_le`: rank is subadditive.
* `Matrix.rank_neg`: negation preserves rank.
* `Matrix.rank_smul_le`: scaling does not increase rank.
* `Matrix.natCast_rank_eq_rank_toLin'`: the natural matrix rank agrees with linear-map rank.
* `Matrix.exists_eq_mul_rank`: rank factorization `A = C * D` through `Fin A.rank`.

## References

These are standard facts of linear algebra; they are used to compare the ranks of communication
matrices in [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997].
`Matrix.natCast_rank_eq_rank_toLin'` is ported from LinearAlgebra/Rank.lean in
[S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Matrix

variable {m n K : Type*} [Fintype n]

/-- Negation does not change the rank of a matrix. -/
@[simp] theorem rank_neg {R : Type*} [CommRing R] (A : Matrix m n R) : (-A).rank = A.rank := by
  rw [← neg_one_smul R A]
  exact rank_smul_of_mem_nonZeroDivisors A isUnit_one.neg.mem_nonZeroDivisors

/-- Scaling a matrix does not increase its rank, over any commutative semiring with the strong rank
condition, such as a nontrivial commutative ring: `c • A = A (c • 1)`. -/
theorem rank_smul_le {R : Type*} [CommSemiring R] [StrongRankCondition R] (c : R)
    (A : Matrix m n R) : (c • A).rank ≤ A.rank := by
  classical
  simpa [Matrix.mul_smul] using rank_mul_le_left A (c • (1 : Matrix n n R))

variable [Field K]

/-- **Subadditivity of rank**: the rank of a sum of matrices over a field is at most the sum of
their ranks. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, rank, rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a difference of matrices over a field is at most the sum of their ranks. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  simpa [sub_eq_add_neg] using rank_add_le A (-B)

/-- **Rank factorization**: a matrix with finitely many columns is the product of a matrix with
`A.rank` columns and a matrix with `A.rank` rows. The first factor lists a basis of the column
space; the second records the coordinates of each column in that basis. -/
theorem exists_eq_mul_rank (A : Matrix m n K) :
    ∃ (C : Matrix m (Fin A.rank) K) (D : Matrix (Fin A.rank) n K), A = C * D := by
  classical
  have := Module.Finite.span_of_finite K (Set.finite_range A.col)
  let b := (Module.finBasis K (Submodule.span K (Set.range A.col))).reindex
    (finCongr A.rank_eq_finrank_span_cols.symm)
  let col (j : n) : Submodule.span K (Set.range A.col) :=
    ⟨A.col j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨of fun i k => (b k : m → K) i, of fun k j => b.repr (col j) k, ?_⟩
  ext i j
  have h := congrArg (fun v : Submodule.span K (Set.range A.col) => (v : m → K) i)
    (b.sum_repr (col j))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  simpa [mul_apply, col, mul_comm] using h.symm

/-- The natural rank of a finite matrix agrees with the cardinal rank of its linear map. -/
theorem natCast_rank_eq_rank_toLin' [DecidableEq n] (M : Matrix m n K) :
    (M.rank : Cardinal) = M.toLin'.rank := by
  rw [Matrix.rank, Matrix.toLin'_apply']
  exact Module.finrank_eq_rank _ _

end Matrix
