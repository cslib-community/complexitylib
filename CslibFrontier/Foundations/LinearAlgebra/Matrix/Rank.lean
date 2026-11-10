/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (Mathlib, subadditivity of matrix rank and rank factorization)

public import CslibFrontier.Init
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
* `Matrix.rank_map_of_field`: the rank over a field is invariant under a change of scalars.
* `Matrix.rank_eq_zero_iff`: only the zero matrix has rank zero.

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
  simpa [Matrix.mul_apply, col, mul_comm] using h.symm

/-- A matrix over a field whose rank is its number of rows has a right inverse. -/
theorem exists_mul_eq_one_of_rank_eq_card [Fintype m] [DecidableEq m] {A : Matrix m n K}
    (h : A.rank = Fintype.card m) : ∃ B : Matrix n m K, A * B = 1 := by
  refine mulVec_surjective_iff_exists_right_inverse.1 fun y => ?_
  have hA : LinearMap.range A.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fintype_fun_eq_card K).symm)
  exact LinearMap.range_eq_top.1 hA y

/-- The rank of a matrix over a field does not change when its entries are mapped along a ring
homomorphism, in particular under a field extension. Both directions use a rank factorization
`A = C * D`: its image factors `A.map f`, and one-sided inverses of `C` and `D` map to one-sided
inverses, so the identity of size `A.rank` factors through `A.map f`. -/
theorem rank_map_of_field [Finite m] {L : Type*} [CommSemiring L] [StrongRankCondition L]
    (f : K →+* L) (A : Matrix m n K) : (A.map f).rank = A.rank := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨r, hr, C, D, hA⟩ : ∃ r, r = A.rank ∧ ∃ (C : Matrix m (Fin r) K)
      (D : Matrix (Fin r) n K), A = C * D := ⟨_, rfl, A.exists_eq_mul_rank⟩
  have hmap : A.map f = C.map f * D.map f := by rw [hA, Matrix.map_mul]
  have hD : D.rank = Fintype.card (Fin r) :=
    le_antisymm D.rank_le_card_height <| by
      calc Fintype.card (Fin r) = A.rank := (Fintype.card_fin r).trans hr
        _ = (C * D).rank := congrArg rank hA
        _ ≤ D.rank := rank_mul_le_right C D
  have hC : Cᵀ.rank = Fintype.card (Fin r) := by
    rw [rank_transpose]
    refine le_antisymm C.rank_le_card_width ?_
    calc Fintype.card (Fin r) = A.rank := (Fintype.card_fin r).trans hr
      _ = (C * D).rank := congrArg rank hA
      _ ≤ C.rank := rank_mul_le_left C D
  obtain ⟨D', hD'⟩ := exists_mul_eq_one_of_rank_eq_card hD
  obtain ⟨E, hE⟩ := exists_mul_eq_one_of_rank_eq_card hC
  have hE' : Eᵀ * C = 1 := by rw [← transpose_transpose C, ← transpose_mul, hE, transpose_one]
  have hone : Eᵀ.map f * A.map f * D'.map f = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hA, ← Matrix.mul_assoc, hE', Matrix.one_mul, hD',
      Matrix.map_one _ f.map_zero f.map_one]
  refine le_antisymm ?_ ?_
  · calc (A.map f).rank ≤ (C.map f).rank := hmap ▸ rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin r) := rank_le_card_width _
      _ = A.rank := (Fintype.card_fin r).trans hr
  · calc A.rank = (1 : Matrix (Fin r) (Fin r) L).rank := by rw [rank_one, Fintype.card_fin, hr]
      _ = (Eᵀ.map f * A.map f * D'.map f).rank := by rw [hone]
      _ ≤ (Eᵀ.map f * A.map f).rank := rank_mul_le_left _ _
      _ ≤ (A.map f).rank := rank_mul_le_right _ _

/-- The natural rank of a finite matrix agrees with the cardinal rank of its linear map. -/
theorem natCast_rank_eq_rank_toLin' [DecidableEq n] (M : Matrix m n K) :
    (M.rank : Cardinal) = M.toLin'.rank := by
  rw [Matrix.rank, Matrix.toLin'_apply']
  exact Module.finrank_eq_rank _ _

/-- A matrix over a field has rank zero exactly when it is zero. -/
theorem rank_eq_zero_iff {C : Matrix m n K} : C.rank = 0 ↔ C = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ rank_zero⟩
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
  rwa [mulVecLin_apply, mulVec_single_one, col_apply] at this

end Matrix
