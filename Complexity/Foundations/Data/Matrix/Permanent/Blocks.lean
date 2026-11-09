/-
Copyright (c) 2026 Kenny Lau, Chris Hughes, Anne Baanen, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import Complexity.Init
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Finite

/-!
# Reindexing, multilinearity and block identities for the permanent

The permanent is unchanged by independent row and column reindexing, commutes with ring and
algebra homomorphisms, and is additive in each row and column. On a block triangular matrix
with square diagonal blocks, it is the product of their permanents. These identities work over
every commutative semiring, including empty index types.

## Main results

* `Matrix.permanent_submatrix_equiv_equiv`: independent row and column reindexing.
* `Matrix.permanent_updateRow_add`, `Matrix.permanent_updateCol_add`: multilinearity.
* `RingHom.map_permanent`, `AlgHom.map_permanent`: compatibility with homomorphisms.
* `Matrix.permanent_fromBlocks_zero₂₁`, `Matrix.permanent_fromBlocks_zero₁₂`: triangular blocks.

## References

The block proof adapts Mathlib's `Matrix.det_fromBlocks_zero₂₁` in
`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, retaining its authors' credit. Other proof
material is adapted from the saved Complexitylib development at revision `5b8acca7`.
-/

@[expose] public section

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Reindexing both rows and columns of a square matrix by the same equivalence preserves its
permanent. -/
@[simp] theorem permanent_submatrix_equiv {m' : Type*} [Fintype m'] [DecidableEq m'] (e : m' ≃ m)
    (A : Matrix m m R) : (A.submatrix e e).permanent = A.permanent := by
  rw [permanent, permanent, ← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← e.prod_comp]
  exact Finset.prod_congr rfl fun i _ => by simp [submatrix_apply, Equiv.permCongr_apply]

/-- Reindexing the rows and columns of a square matrix by any two equivalences preserves its
permanent. -/
theorem permanent_submatrix_equiv_equiv {m' : Type*} [Fintype m'] [DecidableEq m']
    (e₁ e₂ : m' ≃ m) (A : Matrix m m R) : (A.submatrix e₁ e₂).permanent = A.permanent := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₂ e₂).submatrix (e₁.trans e₂.symm) id := by
    ext i j
    simp [submatrix_apply]
  rw [h, permanent_permute_cols, permanent_submatrix_equiv]

/-- Multilinearity of the permanent in a column. -/
@[simp] theorem permanent_updateCol_add (M : Matrix m m R) (j : m) (u v : m → R) :
    (M.updateCol j (u + v)).permanent =
      (M.updateCol j u).permanent + (M.updateCol j v).permanent := by
  simp only [permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), updateCol_self,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1 <;>
    refine Finset.sum_congr rfl fun p _ =>
      congrArg (_ * ·) (Finset.prod_congr rfl fun i hi => ?_) <;>
    simp only [ne_eq, Finset.ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

/-- Multilinearity of the permanent in a row. -/
@[simp] theorem permanent_updateRow_add (M : Matrix m m R) (i : m) (u v : m → R) :
    (M.updateRow i (u + v)).permanent =
      (M.updateRow i u).permanent + (M.updateRow i v).permanent := by
  rw [← permanent_transpose, ← updateCol_transpose, permanent_updateCol_add,
    updateCol_transpose, updateCol_transpose, permanent_transpose, permanent_transpose]

/-- If two matrices `M₁, M₂` agree with `M` outside row `r` and their `r`-th rows sum to row `r`
of `M`, then `M.permanent = M₁.permanent + M₂.permanent`. -/
theorem permanent_add_of_row_eq (M M₁ M₂ : Matrix m m R) (r : m)
    (hr : ∀ j, M r j = M₁ r j + M₂ r j)
    (h₁ : ∀ i ≠ r, ∀ j, M₁ i j = M i j)
    (h₂ : ∀ i ≠ r, ∀ j, M₂ i j = M i j) :
    M.permanent = M₁.permanent + M₂.permanent := by
  have hM : M = M.updateRow r (M₁ r + M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp [hr j]
    · simp [hir]
  have hM₁ : M₁ = M.updateRow r (M₁ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₁ i hir j]
  have hM₂ : M₂ = M.updateRow r (M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₂ i hir j]
  conv_lhs => rw [hM]
  rw [permanent_updateRow_add, ← hM₁, ← hM₂]

/-- Applying a ring homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.RingHom.map_permanent {S : Type*} [CommSemiring S] (f : R →+* S)
    (M : Matrix m m R) : f M.permanent = (M.map f).permanent := by
  simp [permanent, map_sum, map_prod]

/-- Applying an algebra homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.AlgHom.map_permanent {R₀ A B : Type*} [CommSemiring R₀] [CommSemiring A]
    [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B] (f : A →ₐ[R₀] B) (M : Matrix m m A) :
    f M.permanent = (M.map f).permanent :=
  f.toRingHom.map_permanent M

/-- The permanent of a `2 × 2` block matrix with the lower-left block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) : (fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [permanent]
  convert
    Eq.symm <|
      sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
  · simp_rw [Finset.sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      exact Set.mem_toFinset.mpr ⟨σ₁₂, rfl⟩
    · intro σ₁ _ σ₂ _ h
      have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
        DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
        Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      exact ⟨σ₁₂, mem_univ _, by simpa using hσ₁₂⟩
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
        fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
        mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · exact absurd hx.symm ((not_exists.mp ha) a2)
    · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))]
      rw [hx, fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The permanent of a `2 × 2` block matrix with the upper-right block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) : (fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← permanent_transpose, fromBlocks_transpose, transpose_zero, permanent_fromBlocks_zero₂₁,
    permanent_transpose, permanent_transpose]

/-- The permanent of a block-diagonal `2 × 2` matrix is the product of the permanents of its
diagonal blocks. -/
theorem permanent_fromBlocks_zero (A : Matrix m m R) (D : Matrix n n R) :
    (fromBlocks A (0 : Matrix m n R) 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero₂₁ A 0 D

end Matrix
