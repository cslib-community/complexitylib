/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Sylvester–Bareiss minor identity and fraction-free Gauss–Jordan)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Bareiss fraction-free Gauss–Jordan elimination and Sylvester minor identities

This module develops the pure matrix theory behind fraction-free (Bareiss / Edmonds) Gauss–Jordan
elimination and reduced row echelon form over fields and the integers:

* Bordering determinants (`Matrix.border`) satisfy the Schur-complement expansion
  `Matrix.det_border`, yielding both the 2×2 Sylvester / Desnanot–Jacobi identity
  (`Matrix.det_mul_det_fromBlocks_fin2`) and the upward Gauss–Jordan minor identity
  (`Matrix.det_mul_det_border_updateCol`).
* For a matrix `A : Matrix (Fin m) (Fin n) R` and pivot selections `S : Fin k → Fin m`,
  `C : Fin k → Fin n`, `Matrix.bareissMatrix A S C` stores the exact `k × k` minor determinants on
  pivoted rows `S a` and `(k + 1) × (k + 1)` minor determinants on unpivoted rows.
* Over `ℤ`, every Bareiss–Jordan step preserves exact integer divisibility by `pivotDet A S C`
  (`Matrix.pivotDet_dvd_bareissStep_int`), computes the next minor via `Int.ediv`
  (`Matrix.bareissStep_ediv_eq_int`), and obeys the Hadamard/factorial minor bound
  (`Matrix.abs_bareissMatrix_le`).
* Over any field `K`, scaling by `(pivotDet A S C)⁻¹` yields `Matrix.rrefOfBareiss A S C`, which
  preserves row space, rank, and kernel, produces a `LinearIndependent` row basis, a
  `LinearIndependent` kernel basis (`Matrix.kernelBasisVec`) spanning `LinearMap.ker A.mulVecLin`,
  a `Matrix.IsReducedRowEchelon` / `Matrix.IsPivotedBy` presentation under row permutation, and a
  canonical solution vector `Matrix.solveVec A S C b` whenever `A *ᵥ x = b` is consistent.

## References

* A. Schrijver, *Theory of Linear and Integer Programming* [Schrijver1986].
-/

public section

namespace Matrix

open Finset Submodule
open scoped Matrix BigOperators

/-! ### Block bordering and Sylvester / Cramer–Jordan determinant identities -/

section Identities

variable {R : Type*} {k : ℕ}

/-- Border a `k × k` matrix `A` on the right by column `b`, below by row `c`, and in the
bottom-right corner by scalar `d`. -/
@[expose] def border (A : Matrix (Fin k) (Fin k) R) (b c : Fin k → R) (d : R) :
    Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) R :=
  fromBlocks A (of fun i _ => b i) (of fun _ j => c j) (of fun _ _ => d)

@[simp]
theorem map_border {S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin k) (Fin k) R) (b c : Fin k → R) (d : R) :
    (border A b c d).map f = border (A.map f) (f ∘ b) (f ∘ c) (f d) := by
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> rfl

variable {K : Type*} [Field K]

/-- Schur-complement determinant expansion of a bordered matrix around an invertible leading block
`A`. -/
theorem det_border {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0) (b c : Fin k → K) (d : K) :
    (border A b c d).det = A.det * (d - c ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  let _ : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  rw [border, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  change d - ((of fun _ j => c j) * A⁻¹ * (of fun i _ => b i)) default default =
    d - c ⬝ᵥ (A⁻¹ *ᵥ b)
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [of_apply, Matrix.mul_apply, dotProduct, mulVec]

/-- **Sylvester / Desnanot–Jacobi 2×2 determinant identity**: multiplying a `(k + 2) × (k + 2)`
block matrix determinant by its invertible `k × k` leading principal minor equals the 2×2
determinant of its `(k + 1) × (k + 1)` bordered minors. -/
theorem det_mul_det_fromBlocks_fin2 {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0)
    (b₀ b₁ c₀ c₁ : Fin k → K) (d₀₀ d₀₁ d₁₀ d₁₁ : K) :
    A.det *
        (fromBlocks A
          (of fun i (j : Fin 2) => if j = 0 then b₀ i else b₁ i)
          (of fun (i : Fin 2) j => if i = 0 then c₀ j else c₁ j)
          ![![d₀₀, d₀₁], ![d₁₀, d₁₁]]).det =
      (border A b₀ c₀ d₀₀).det * (border A b₁ c₁ d₁₁).det -
        (border A b₀ c₁ d₁₀).det * (border A b₁ c₀ d₀₁).det := by
  let _ : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  set B : Matrix (Fin k) (Fin 2) K := of fun i j => if j = 0 then b₀ i else b₁ i
  set C : Matrix (Fin 2) (Fin k) K := of fun i j => if i = 0 then c₀ j else c₁ j
  set D : Matrix (Fin 2) (Fin 2) K := ![![d₀₀, d₀₁], ![d₁₀, d₁₁]]
  set S : Matrix (Fin 2) (Fin 2) K := D - C * A⁻¹ * B
  have hS : ∀ u v : Fin 2, A.det * S u v =
      (border A (fun i => B i v) (C u) (D u v)).det := by
    intro u v
    rw [det_border hA]
    congr 1
    change D u v - (C * A⁻¹ * B) u v = D u v - C u ⬝ᵥ (A⁻¹ *ᵥ fun i => B i v)
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [dotProduct, mulVec]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Matrix.mul_apply]
  have hB0 : (fun i => B i 0) = b₀ := funext fun i => by simp only [B, of_apply, ↓reduceIte]
  have hB1 : (fun i => B i 1) = b₁ :=
    funext fun i => by simp only [B, of_apply, Fin.isValue, one_ne_zero, ↓reduceIte]
  have hC0 : C 0 = c₀ := funext fun j => by simp only [C, of_apply, ↓reduceIte]
  have hC1 : C 1 = c₁ :=
    funext fun j => by simp only [C, of_apply, Fin.isValue, one_ne_zero, ↓reduceIte]
  have hS00 : (border A b₀ c₀ d₀₀).det = A.det * S 0 0 := by
    have h := (hS 0 0).symm
    rw [hB0, hC0] at h
    exact h
  have hS01 : (border A b₁ c₀ d₀₁).det = A.det * S 0 1 := by
    have h := (hS 0 1).symm
    rw [hB1, hC0] at h
    exact h
  have hS10 : (border A b₀ c₁ d₁₀).det = A.det * S 1 0 := by
    have h := (hS 1 0).symm
    rw [hB0, hC1] at h
    exact h
  have hS11 : (border A b₁ c₁ d₁₁).det = A.det * S 1 1 := by
    have h := (hS 1 1).symm
    rw [hB1, hC1] at h
    exact h
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  change A.det * (A.det * S.det) = _
  rw [det_fin_two S, hS00, hS01, hS10, hS11]
  ring

/-- **Cramer–Jordan upward elimination minor identity**: updating column `a` of an invertible
`(k + 1) × (k + 1)` bordered matrix `M = border A b₁ c d₁` by `(b₂, d₂)` satisfies the
fraction-free Gauss–Jordan identity
`A.det * det M' = det M * det (A[a ↦ b₂]) - det(border A b₂ c d₂) * det (A[a ↦ b₁])`. -/
theorem det_mul_det_border_updateCol {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0)
    (b₁ c : Fin k → K) (d₁ : K) (hM : (border A b₁ c d₁).det ≠ 0)
    (b₂ : Fin k → K) (d₂ : K) (a : Fin k) :
    A.det * ((border A b₁ c d₁).updateCol (Sum.inl a) (Sum.elim b₂ fun _ => d₂)).det =
      (border A b₁ c d₁).det * (A.updateCol a b₂).det -
        (border A b₂ c d₂).det * (A.updateCol a b₁).det := by
  set M := border A b₁ c d₁
  set v : Fin k ⊕ Unit → K := Sum.elim b₂ fun _ => d₂
  set x : Fin k ⊕ Unit → K := M⁻¹ *ᵥ v
  have hMx : M *ᵥ x = v := by
    rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), one_mulVec]
  let x₁ : Fin k → K := x ∘ Sum.inl
  let x₂ : K := x (Sum.inr ())
  have hblock₁ : A *ᵥ x₁ = b₂ - x₂ • b₁ := by
    funext t
    have ht := congrFun hMx (Sum.inl t)
    simp only [M, border, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, of_apply, Fintype.sum_unique, PUnit.default_eq_unit, v, Sum.elim_inl]
      at ht
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact eq_sub_of_add_eq (by
      simpa only [mulVec, dotProduct, x₁, x₂, Function.comp_apply, mul_comm] using ht)
  have hx₁ : x₁ = A⁻¹ *ᵥ b₂ - x₂ • (A⁻¹ *ᵥ b₁) := by
    calc x₁ = (A⁻¹ * A) *ᵥ x₁ := by
            rw [nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), one_mulVec]
      _ = A⁻¹ *ᵥ (A *ᵥ x₁) := by rw [mulVec_mulVec]
      _ = A⁻¹ *ᵥ (b₂ - x₂ • b₁) := by rw [hblock₁]
      _ = A⁻¹ *ᵥ b₂ - x₂ • (A⁻¹ *ᵥ b₁) := by rw [mulVec_sub, mulVec_smul]
  have hx₂ : x₂ * M.det = (border A b₂ c d₂).det := by
    have hr := congrFun hMx (Sum.inr ())
    simp only [M, border, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, of_apply, Fintype.sum_unique, PUnit.default_eq_unit, v, Sum.elim_inr]
      at hr
    have hdot₁ : ∑ i : Fin k, c i * x (Sum.inl i) =
        c ⬝ᵥ (A⁻¹ *ᵥ b₂) - x₂ * (c ⬝ᵥ (A⁻¹ *ᵥ b₁)) := by
      change c ⬝ᵥ x₁ = _
      rw [hx₁, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change (∑ i : Fin k, c i * x (Sum.inl i)) + d₁ * x₂ = d₂ at hr
    rw [hdot₁] at hr
    have hdiff : x₂ * (d₁ - c ⬝ᵥ (A⁻¹ *ᵥ b₁)) = d₂ - c ⬝ᵥ (A⁻¹ *ᵥ b₂) := by
      rw [← hr]
      ring
    have hmul : A.det * (x₂ * (d₁ - c ⬝ᵥ (A⁻¹ *ᵥ b₁))) = A.det * (d₂ - c ⬝ᵥ (A⁻¹ *ᵥ b₂)) :=
      congrArg (A.det * ·) hdiff
    rw [← det_border hA b₂ c d₂] at hmul
    dsimp only [M]
    rw [← hmul, det_border hA b₁ c d₁]
    ring
  have hcrM : M.det * x (Sum.inl a) = (M.updateCol (Sum.inl a) v).det := by
    have h := congrFun (det_smul_inv_mulVec_eq_cramer M v (isUnit_iff_ne_zero.mpr hM)) (Sum.inl a)
    simpa only [x, Pi.smul_apply, smul_eq_mul, cramer_apply] using h
  have hcr₂ : A.det * (A⁻¹ *ᵥ b₂) a = (A.updateCol a b₂).det := by
    have h := congrFun (det_smul_inv_mulVec_eq_cramer A b₂ (isUnit_iff_ne_zero.mpr hA)) a
    simpa only [Pi.smul_apply, smul_eq_mul, cramer_apply] using h
  have hcr₁ : A.det * (A⁻¹ *ᵥ b₁) a = (A.updateCol a b₁).det := by
    have h := congrFun (det_smul_inv_mulVec_eq_cramer A b₁ (isUnit_iff_ne_zero.mpr hA)) a
    simpa only [Pi.smul_apply, smul_eq_mul, cramer_apply] using h
  have hcoord : x (Sum.inl a) = (A⁻¹ *ᵥ b₂) a - x₂ * (A⁻¹ *ᵥ b₁) a := congrFun hx₁ a
  calc A.det * (M.updateCol (Sum.inl a) v).det
      = A.det * (M.det * x (Sum.inl a)) := by rw [hcrM]
    _ = M.det * (A.det * (A⁻¹ *ᵥ b₂) a) - (x₂ * M.det) * (A.det * (A⁻¹ *ᵥ b₁) a) := by
        rw [hcoord]
        ring
    _ = M.det * (A.updateCol a b₂).det - (border A b₂ c d₂).det * (A.updateCol a b₁).det := by
        rw [hcr₂, hx₂, hcr₁]

end Identities

/-! ### Minor-scaled Bareiss–Jordan matrices -/

section MinorMatrix

variable {m n k : ℕ}

/-- Determinant of the `k × k` pivot submatrix indexed by row selection `S` and column selection
`C`. -/
@[expose] def pivotDet {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : R :=
  (A.submatrix S C).det

@[simp]
theorem pivotDet_zero {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin 0 → Fin m) (C : Fin 0 → Fin n) : pivotDet A S C = 1 :=
  det_fin_zero

@[simp]
theorem map_pivotDet {R S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    f (pivotDet A S C) = pivotDet (A.map f) S C := by
  rw [pivotDet, pivotDet, RingHom.map_det]
  rfl

/-- If `pivotDet A S C ≠ 0`, both the row selection `S` and the column selection `C` are
injective. -/
theorem injective_of_pivotDet_ne_zero {R : Type*} [CommRing R] {A : Matrix (Fin m) (Fin n) R}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (h : pivotDet A S C ≠ 0) :
    Function.Injective S ∧ Function.Injective C := by
  constructor
  · intro a₁ a₂ ha
    by_contra hne
    exact h (det_zero_of_row_eq hne (funext fun b => by simp only [submatrix_apply, ha]))
  · intro b₁ b₂ hb
    by_contra hne
    exact h (det_zero_of_column_eq hne (fun a => by simp only [submatrix_apply, hb]))

/-- The minor-scaled Bareiss–Jordan matrix associated with pivot rows `S` and pivot columns `C`.
For a pivoted row `i = S a`, entry `(i, j)` is the `k × k` minor obtained by replacing column `C a`
with `j`. For an unpivoted row `i ∉ range S`, entry `(i, j)` is the `(k + 1) × (k + 1)` minor
obtained by bordering `A.submatrix S C` with row `i` and column `j`. -/
noncomputable def bareissMatrix {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : Matrix (Fin m) (Fin n) R := by
  classical
  exact Matrix.of fun i j =>
    if h : ∃ a : Fin k, S a = i then
      (A.submatrix S (Function.update C h.choose j)).det
    else
      (A.submatrix (Fin.snoc S i) (Fin.snoc C j)).det

/-- Entry of `bareissMatrix A S C` on a pivoted row `S a`. -/
theorem bareissMatrix_pivot {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n)
    (a : Fin k) (j : Fin n) :
    bareissMatrix A S C (S a) j = (A.submatrix S (Function.update C a j)).det := by
  classical
  simp only [bareissMatrix, Matrix.of_apply]
  split_ifs with h'
  · rw [hS h'.choose_spec]
  · exact absurd ⟨a, rfl⟩ h'

/-- Entry of `bareissMatrix A S C` on an unpivoted row `i`. -/
theorem bareissMatrix_nonPivot {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (C : Fin k → Fin n) {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (j : Fin n) :
    bareissMatrix A S C i j = (A.submatrix (Fin.snoc S i) (Fin.snoc C j)).det := by
  classical
  simp only [bareissMatrix, Matrix.of_apply]
  split_ifs with h'
  · exact absurd h'.choose_spec (hi h'.choose)
  · rfl

@[simp]
theorem bareissMatrix_zero {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin 0 → Fin m) (C : Fin 0 → Fin n) :
    bareissMatrix A S C = A := by
  ext i j
  rw [bareissMatrix_nonPivot A C (fun a => a.elim0) j, det_fin_one]
  rfl

/-- Mapping a matrix by a ring homomorphism commutes with `bareissMatrix`. -/
theorem map_bareissMatrix {R S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    (bareissMatrix A S C).map f = bareissMatrix (A.map f) S C := by
  classical
  ext i j
  simp only [bareissMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · rw [RingHom.map_det]
    rfl
  · rw [RingHom.map_det]
    rfl

/-- On a pivoted row `S a`, entry `(S a, C a)` equals `pivotDet A S C`. -/
theorem bareissMatrix_pivot_col_self {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n) (a : Fin k) :
    bareissMatrix A S C (S a) (C a) = pivotDet A S C := by
  rw [bareissMatrix_pivot A hS C a (C a), Function.update_eq_self]
  rfl

/-- On a pivoted row `S a`, every other pivot column `C b` (`a ≠ b`) vanishes. -/
theorem bareissMatrix_pivot_col_ne {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n)
    {a b : Fin k} (hab : a ≠ b) :
    bareissMatrix A S C (S a) (C b) = 0 := by
  rw [bareissMatrix_pivot A hS C a (C b)]
  exact det_zero_of_column_eq hab fun t => by
    simp only [submatrix_apply, Function.update_self, Function.update_of_ne hab.symm]

/-- On an unpivoted row `i`, every pivot column `C b` vanishes. -/
theorem bareissMatrix_nonPivot_col {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (C : Fin k → Fin n) {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (b : Fin k) :
    bareissMatrix A S C i (C b) = 0 := by
  rw [bareissMatrix_nonPivot A C hi (C b)]
  exact det_zero_of_column_eq b.castSucc_ne_last fun t => by
    simp only [submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last]

private def sumUnitEquiv (k : ℕ) : Fin k ⊕ Unit ≃ Fin (k + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin k)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

private theorem sumUnitEquiv_inl (k : ℕ) (a : Fin k) : sumUnitEquiv k (Sum.inl a) = a.castSucc :=
  rfl

private theorem sumUnitEquiv_inr (k : ℕ) (u : Unit) : sumUnitEquiv k (Sum.inr u) = Fin.last k := by
  cases u
  simp only [sumUnitEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]
  rfl

private theorem det_snoc_eq_det_border {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (p : Fin m) (q : Fin n) :
    (A.submatrix (Fin.snoc S p) (Fin.snoc C q)).det =
      (border (A.submatrix S C) (fun a => A (S a) q) (fun b => A p (C b)) (A p q)).det := by
  have heq : border (A.submatrix S C) (fun a => A (S a) q) (fun b => A p (C b)) (A p q) =
      (A.submatrix (Fin.snoc S p) (Fin.snoc C q)).submatrix (sumUnitEquiv k) (sumUnitEquiv k) := by
    ext i j
    rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · simp only [border, fromBlocks_apply₁₁, submatrix_apply, sumUnitEquiv_inl, Fin.snoc_castSucc]
    · simp only [border, fromBlocks_apply₁₂, of_apply, submatrix_apply, sumUnitEquiv_inl,
        sumUnitEquiv_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [border, fromBlocks_apply₂₁, of_apply, submatrix_apply, sumUnitEquiv_inl,
        sumUnitEquiv_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [border, fromBlocks_apply₂₂, of_apply, submatrix_apply, sumUnitEquiv_inr,
        Fin.snoc_last]
  rw [heq, det_submatrix_equiv_self]

/-- **Main Bareiss–Jordan identity over any field `K`:** appending a pivot `(p, q)` with
`p ∉ range S` and `bareissMatrix A S C p q ≠ 0` updates every row `i ≠ p` via the Sylvester /
Cramer–Jordan quotient by `pivotDet A S C`, and keeps row `p` unchanged. -/
theorem pivotDet_mul_bareissMatrix_snoc {K : Type*} [Field K] (A : Matrix (Fin m) (Fin n) K)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (i : Fin m) (j : Fin n) :
    (i = p → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = bareissMatrix A S C p j) ∧
      (i ≠ p →
        pivotDet A S C * bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j =
          bareissMatrix A S C p q * bareissMatrix A S C i j -
            bareissMatrix A S C i q * bareissMatrix A S C p j) := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  have hS'inj : Function.Injective (Fin.snoc S p) :=
    Fin.snoc_injective_of_injective hSinj fun ⟨a, ha⟩ => hp a ha
  have hpq_det : (A.submatrix (Fin.snoc S p) (Fin.snoc C q)).det = bareissMatrix A S C p q :=
    (bareissMatrix_nonPivot A C hp q).symm
  have hM_det : (border (A.submatrix S C) (fun a => A (S a) q) (fun b => A p (C b))
      (A p q)).det ≠ 0 := by
    rw [← det_snoc_eq_det_border, hpq_det]
    exact hΔ'
  constructor
  · rintro rfl
    have h1 := bareissMatrix_pivot A hS'inj (Fin.snoc C q) (Fin.last k) j
    rw [Fin.snoc_last] at h1
    rw [h1, bareissMatrix_nonPivot A C hp j]
    have hupd : Function.update (Fin.snoc C q) (Fin.last k) j =
        Fin.snoc (α := fun _ => Fin n) C j := by
      ext x
      induction x using Fin.lastCases with
      | last => simp only [Function.update_self, Fin.snoc_last]
      | cast a =>
        simp only [Function.update_of_ne a.castSucc_ne_last, Fin.snoc_castSucc]
    rw [hupd]
  · intro hne
    by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      have h1 := bareissMatrix_pivot A hS'inj (Fin.snoc C q) a.castSucc j
      rw [Fin.snoc_castSucc] at h1
      rw [h1, bareissMatrix_pivot A hSinj C a j, bareissMatrix_pivot A hSinj C a q,
        bareissMatrix_nonPivot A C hp q, bareissMatrix_nonPivot A C hp j]
      have hupd : (border (A.submatrix S C) (fun t => A (S t) q) (fun t => A p (C t))
            (A p q)).updateCol (Sum.inl a) (Sum.elim (fun t => A (S t) j) fun _ => A p j) =
          (A.submatrix (Fin.snoc S p) (Function.update (Fin.snoc C q) a.castSucc j)).submatrix
            (sumUnitEquiv k) (sumUnitEquiv k) := by
        ext u v
        rcases u with u | ⟨⟩ <;> rcases v with v | ⟨⟩
        · by_cases hv : v = a
          · subst hv
            simp only [border, updateCol_apply, sumUnitEquiv_inl, ↓reduceIte, Sum.elim_inl,
              submatrix_apply, Fin.snoc_castSucc, Function.update_self]
          · have hne' : v.castSucc ≠ a.castSucc := fun h => hv (Fin.castSucc_inj.1 h)
            simp only [border, updateCol_apply, sumUnitEquiv_inl, Sum.inl.injEq, hv, ↓reduceIte,
              fromBlocks_apply₁₁, submatrix_apply, Fin.snoc_castSucc, Function.update_of_ne hne']
        · simp only [border, updateCol_apply, sumUnitEquiv_inl, sumUnitEquiv_inr, reduceCtorEq,
            ↓reduceIte, fromBlocks_apply₁₂, of_apply, submatrix_apply, Fin.snoc_castSucc,
            Function.update_of_ne (a.castSucc_ne_last).symm, Fin.snoc_last]
        · by_cases hv : v = a
          · subst hv
            simp only [border, updateCol_apply, sumUnitEquiv_inl, sumUnitEquiv_inr, ↓reduceIte,
              Sum.elim_inr, submatrix_apply, Fin.snoc_last, Function.update_self]
          · have hne' : v.castSucc ≠ a.castSucc := fun h => hv (Fin.castSucc_inj.1 h)
            simp only [border, updateCol_apply, sumUnitEquiv_inl, sumUnitEquiv_inr, Sum.inl.injEq,
              hv, ↓reduceIte, fromBlocks_apply₂₁, of_apply, submatrix_apply, Fin.snoc_last,
              Fin.snoc_castSucc, Function.update_of_ne hne']
        · simp only [border, updateCol_apply, sumUnitEquiv_inr, reduceCtorEq, ↓reduceIte,
            fromBlocks_apply₂₂, of_apply, submatrix_apply, Fin.snoc_last,
            Function.update_of_ne (a.castSucc_ne_last).symm]
      have hleft := congrArg Matrix.det hupd
      rw [det_submatrix_equiv_self] at hleft
      rw [← hleft, pivotDet, det_mul_det_border_updateCol hΔ (fun t => A (S t) q)
        (fun t => A p (C t)) (A p q) hM_det (fun t => A (S t) j) (A p j) a]
      rw [det_snoc_eq_det_border A S C p q]
      have hupd₂ : (A.submatrix S C).updateCol a (fun t => A (S t) j) =
          A.submatrix S (Function.update C a j) := by
        ext u v
        by_cases hv : v = a
        · subst hv; simp only [updateCol_apply, ↓reduceIte, submatrix_apply, Function.update_self]
        · simp only [updateCol_apply, hv, ↓reduceIte, submatrix_apply, Function.update_of_ne hv]
      have hupd₁ : (A.submatrix S C).updateCol a (fun t => A (S t) q) =
          A.submatrix S (Function.update C a q) := by
        ext u v
        by_cases hv : v = a
        · subst hv; simp only [updateCol_apply, ↓reduceIte, submatrix_apply, Function.update_self]
        · simp only [updateCol_apply, hv, ↓reduceIte, submatrix_apply, Function.update_of_ne hv]
      rw [hupd₂, hupd₁, det_snoc_eq_det_border A S C p j]
      ring
    · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
      have hi' : ∀ x : Fin (k + 1), (Fin.snoc S p : Fin (k + 1) → Fin m) x ≠ i := by
        intro x
        by_cases hx : x.val < k
        · have hx' : x = Fin.castSucc ⟨x.val, hx⟩ := rfl
          rw [hx', Fin.snoc_castSucc]
          exact hi ⟨x.val, hx⟩
        · have hx' : x = Fin.last k := Fin.ext (by have := x.isLt; rw [Fin.val_last]; omega)
          rw [hx', Fin.snoc_last]
          exact hne.symm
      rw [bareissMatrix_nonPivot A (Fin.snoc C q) hi' j,
        bareissMatrix_nonPivot A C hp q, bareissMatrix_nonPivot A C hi j,
        bareissMatrix_nonPivot A C hi q, bareissMatrix_nonPivot A C hp j]
      have hblk :
          fromBlocks (A.submatrix S C)
            (of fun u (v : Fin 2) => if v = 0 then A (S u) q else A (S u) j)
            (of fun (u : Fin 2) v => if u = 0 then A p (C v) else A i (C v))
            ![![A p q, A p j], ![A i q, A i j]] =
          (A.submatrix (Fin.snoc (Fin.snoc S p) i) (Fin.snoc (Fin.snoc C q) j)).submatrix
            (finSumFinEquiv (m := k) (n := 2)) (finSumFinEquiv (m := k) (n := 2)) := by
        have hleft_eq : ∀ t : Fin k, finSumFinEquiv (m := k) (n := 2) (Sum.inl t) =
            t.castSucc.castSucc := fun _ => rfl
        have h0_eq : ∀ h : 0 < 2,
            finSumFinEquiv (m := k) (n := 2) (Sum.inr ⟨0, h⟩) = (Fin.last k).castSucc :=
          fun _ => rfl
        have h1_eq : ∀ h : 1 < 2,
            finSumFinEquiv (m := k) (n := 2) (Sum.inr ⟨1, h⟩) = Fin.last (k + 1) :=
          fun _ => rfl
        ext u v
        simp only [submatrix_apply]
        rcases u with u | u <;> rcases v with v | v
        · simp only [hleft_eq, Fin.snoc_castSucc]
          rfl
        · fin_cases v
          · dsimp only; rw [hleft_eq, h0_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
          · dsimp only; rw [hleft_eq, h1_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
        · fin_cases u
          · dsimp only; rw [hleft_eq, h0_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
          · dsimp only; rw [hleft_eq, h1_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
        · fin_cases u <;> fin_cases v
          · dsimp only; rw [h0_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
          · dsimp only; rw [h0_eq, h1_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
          · dsimp only; rw [h1_eq, h0_eq]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rfl
          · dsimp only; rw [h1_eq]; simp only [Fin.snoc_last]; rfl
      have hdet := congrArg Matrix.det hblk
      rw [det_submatrix_equiv_self] at hdet
      rw [pivotDet, ← hdet, det_mul_det_fromBlocks_fin2 hΔ (fun t => A (S t) q)
        (fun t => A (S t) j) (fun t => A p (C t)) (fun t => A i (C t)) (A p q) (A p j) (A i q)
        (A i j)]
      rw [det_snoc_eq_det_border A S C p q, det_snoc_eq_det_border A S C i j,
        det_snoc_eq_det_border A S C i q, det_snoc_eq_det_border A S C p j]

/-- Over `ℤ`, every Bareiss–Jordan update identity holds identically, giving exact divisibility by
`pivotDet A S C`. -/
theorem pivotDet_mul_bareissMatrix_snoc_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (i : Fin m) (j : Fin n) :
    (i = p → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = bareissMatrix A S C p j) ∧
      (i ≠ p →
        pivotDet A S C * bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j =
          bareissMatrix A S C p q * bareissMatrix A S C i j -
            bareissMatrix A S C i q * bareissMatrix A S C p j) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have hΔQ : pivotDet (A.map f) S C ≠ 0 := by
    rw [← map_pivotDet f A S C]
    exact Int.cast_ne_zero.mpr hΔ
  have hΔ'Q : bareissMatrix (A.map f) S C p q ≠ 0 := by
    rw [← map_bareissMatrix f A S C]
    change f (bareissMatrix A S C p q) ≠ 0
    exact Int.cast_ne_zero.mpr hΔ'
  have hQ := pivotDet_mul_bareissMatrix_snoc (A.map f) hΔQ hp q hΔ'Q i j
  constructor
  · intro hip
    have h := hQ.1 hip
    rw [← map_bareissMatrix f A (Fin.snoc S p) (Fin.snoc C q), ← map_bareissMatrix f A S C] at h
    exact Int.cast_injective h
  · intro hip
    have h := hQ.2 hip
    rw [← map_pivotDet f A S C, ← map_bareissMatrix f A (Fin.snoc S p) (Fin.snoc C q),
      ← map_bareissMatrix f A S C] at h
    simp only [Matrix.map_apply, ← RingHom.map_mul, ← RingHom.map_sub] at h
    exact Int.cast_injective h

/-- Exact integer divisibility in a Bareiss–Jordan elimination step. -/
theorem pivotDet_dvd_bareissStep_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) {i : Fin m} (hip : i ≠ p) (j : Fin n) :
    pivotDet A S C ∣
      bareissMatrix A S C p q * bareissMatrix A S C i j -
        bareissMatrix A S C i q * bareissMatrix A S C p j :=
  ⟨bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j,
    ((pivotDet_mul_bareissMatrix_snoc_int A hΔ hp q hΔ' i j).2 hip).symm⟩

/-- Exact quotient (`Int.ediv`) in a Bareiss–Jordan elimination step recovers
`bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j`. -/
theorem bareissStep_ediv_eq_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) {i : Fin m} (hip : i ≠ p) (j : Fin n) :
    (bareissMatrix A S C p q * bareissMatrix A S C i j -
        bareissMatrix A S C i q * bareissMatrix A S C p j) / pivotDet A S C =
      bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j := by
  have heq := ((pivotDet_mul_bareissMatrix_snoc_int A hΔ hp q hΔ' i j).2 hip).symm
  rw [heq]
  exact Int.mul_ediv_cancel_left _ hΔ

/-- Any predicate `Q` on rows that includes the new pivot row `p` and already makes column `j`
vanish in `bareissMatrix A S C` continues to make column `j` vanish after pivoting on `(p, q)`. -/
theorem bareissMatrix_snoc_zero_of_forall {K : Type*} [Field K] (A : Matrix (Fin m) (Fin n) K)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (j : Fin n) (Q : Fin m → Prop) (hQp : Q p)
    (hQzero : ∀ i : Fin m, Q i → bareissMatrix A S C i j = 0) :
    ∀ i : Fin m, Q i → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = 0 := by
  intro i hQi
  by_cases hip : i = p
  · subst hip
    rw [(pivotDet_mul_bareissMatrix_snoc A hΔ hp q hΔ' i j).1 rfl]
    exact hQzero i hQp
  · have hmul := (pivotDet_mul_bareissMatrix_snoc A hΔ hp q hΔ' i j).2 hip
    rw [hQzero i hQi, hQzero p hQp, mul_zero, mul_zero, sub_zero] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hΔ

/-! ### Hadamard / factorial minor bounds over `ℤ` -/

/-- Entry magnitude bound on pivoted rows of `bareissMatrix` over `ℤ`: `k! * B ^ k`. -/
theorem abs_bareissMatrix_pivot_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (hS : Function.Injective S)
    (C : Fin k → Fin n) (a : Fin k) (j : Fin n) :
    |bareissMatrix A S C (S a) j| ≤ (k.factorial * B ^ k : ℕ) := by
  rw [bareissMatrix_pivot A hS C a j]
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow] using
    det_le (abv := AbsoluteValue.abs) (A := A.submatrix S (Function.update C a j))
      fun u v => hA _ _

/-- Entry magnitude bound on unpivoted rows of `bareissMatrix` over `ℤ`:
`(k + 1)! * B ^ (k + 1)`. -/
theorem abs_bareissMatrix_nonPivot_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (C : Fin k → Fin n)
    {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (j : Fin n) :
    |bareissMatrix A S C i j| ≤ ((k + 1).factorial * B ^ (k + 1) : ℕ) := by
  rw [bareissMatrix_nonPivot A C hi j]
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow] using
    det_le (abv := AbsoluteValue.abs) (A := A.submatrix (Fin.snoc S i) (Fin.snoc C j))
      fun u v => hA _ _

/-- Uniform entry magnitude bound for any stage of `bareissMatrix` over `ℤ`. -/
theorem abs_bareissMatrix_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (hS : Function.Injective S)
    (C : Fin k → Fin n) (i : Fin m) (j : Fin n) :
    |bareissMatrix A S C i j| ≤ ((k + 1).factorial * (B + 1) ^ (k + 1) : ℕ) := by
  by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    refine (abs_bareissMatrix_pivot_le A hA hS C a j).trans ?_
    exact_mod_cast Nat.mul_le_mul (Nat.factorial_le (Nat.le_succ k))
      ((Nat.pow_le_pow_left (Nat.le_succ B) k).trans
        (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.le_succ k)))
  · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
    refine (abs_bareissMatrix_nonPivot_le A hA C hi j).trans ?_
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ B) (k + 1))

/-- Pivot determinant magnitude bound: `|pivotDet A S C| ≤ k! * B ^ k`. -/
theorem abs_pivotDet_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    |pivotDet A S C| ≤ (k.factorial * B ^ k : ℕ) := by
  simpa only [pivotDet, AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow] using
    det_le (abv := AbsoluteValue.abs) (A := A.submatrix S C) fun u v => hA _ _

/-! ### Rational RREF, row space, rank, row basis, kernel basis, and linear solver -/

section FieldResults

variable {K : Type*} [Field K]

/-- Rational reduced form `(pivotDet A S C)⁻¹ • bareissMatrix A S C`. -/
@[expose] noncomputable def rrefOfBareiss (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : Matrix (Fin m) (Fin n) K :=
  (pivotDet A S C)⁻¹ • bareissMatrix A S C

/-- Entry of `rrefOfBareiss A S C` on a pivoted row `S a`. -/
theorem rrefOfBareiss_pivot_entry {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (a : Fin k) (j : Fin n) :
    rrefOfBareiss A S C (S a) j = ((A.submatrix S C)⁻¹ *ᵥ (fun t => A (S t) j)) a := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  have hcr := congrFun (det_smul_inv_mulVec_eq_cramer (A.submatrix S C) (fun t => A (S t) j)
    (isUnit_iff_ne_zero.mpr hΔ)) a
  simp only [Pi.smul_apply, smul_eq_mul, cramer_apply] at hcr
  have hupd : (A.submatrix S C).updateCol a (fun t => A (S t) j) =
      A.submatrix S (Function.update C a j) := by
    ext u v
    by_cases hv : v = a
    · subst hv; simp only [updateCol_apply, ↓reduceIte, submatrix_apply, Function.update_self]
    · simp only [updateCol_apply, hv, ↓reduceIte, submatrix_apply, Function.update_of_ne hv]
  change (pivotDet A S C)⁻¹ * bareissMatrix A S C (S a) j = _
  rw [bareissMatrix_pivot A hSinj C a j, ← hupd, ← hcr, pivotDet]
  exact inv_mul_cancel_left₀ hΔ _

/-- Each pivot entry `(S a, C a)` in `rrefOfBareiss A S C` equals `1`. -/
theorem rrefOfBareiss_pivot_col_self {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    rrefOfBareiss A S C (S a) (C a) = 1 := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  change (pivotDet A S C)⁻¹ * bareissMatrix A S C (S a) (C a) = 1
  rw [bareissMatrix_pivot_col_self A hSinj C a, inv_mul_cancel₀ hΔ]

/-- Entries of `rrefOfBareiss A S C` in other pivot columns vanish on pivot rows. -/
theorem rrefOfBareiss_pivot_col_ne {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) {a b : Fin k}
    (hab : a ≠ b) : rrefOfBareiss A S C (S a) (C b) = 0 := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  change (pivotDet A S C)⁻¹ * bareissMatrix A S C (S a) (C b) = 0
  rw [bareissMatrix_pivot_col_ne A hSinj C hab, mul_zero]

/-- Entries of `rrefOfBareiss A S C` in pivot columns vanish on unpivoted rows. -/
theorem rrefOfBareiss_nonPivot_col {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i)
    (b : Fin k) : rrefOfBareiss A S C i (C b) = 0 := by
  change (pivotDet A S C)⁻¹ * bareissMatrix A S C i (C b) = 0
  rw [bareissMatrix_nonPivot_col A C hi b, mul_zero]

/-- Row elimination formula for unpivoted rows of `rrefOfBareiss A S C`. -/
theorem rrefOfBareiss_nonPivot_row {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) :
    rrefOfBareiss A S C i = A i - ∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a) := by
  ext j
  change (pivotDet A S C)⁻¹ * bareissMatrix A S C i j = _
  rw [bareissMatrix_nonPivot A C hi j, det_snoc_eq_det_border, det_border hΔ]
  change (pivotDet A S C)⁻¹ * (pivotDet A S C * (A i j - _)) = _
  rw [inv_mul_cancel_left₀ hΔ]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rrefOfBareiss_pivot_entry hΔ a j]

/-- Each pivot row of `rrefOfBareiss A S C` is a linear combination of the pivot rows of `A`. -/
theorem rrefOfBareiss_pivot_eq_sum {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    rrefOfBareiss A S C (S a) = ∑ b : Fin k, (A.submatrix S C)⁻¹ a b • A (S b) := by
  ext j
  simp only [rrefOfBareiss_pivot_entry hΔ a j, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

/-- Each pivot row of `A` is a linear combination of the pivot rows of `rrefOfBareiss A S C`. -/
theorem row_pivot_eq_sum_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    A (S a) = ∑ b : Fin k, A (S a) (C b) • rrefOfBareiss A S C (S b) := by
  ext j
  have hinv := congrFun (congrArg (fun M => M *ᵥ (fun t => A (S t) j))
    (mul_nonsing_inv (A.submatrix S C) (isUnit_iff_ne_zero.mpr hΔ))) a
  rw [one_mulVec, ← mulVec_mulVec] at hinv
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rrefOfBareiss_pivot_entry hΔ]
  simpa only [mulVec, dotProduct, submatrix_apply] using hinv.symm

/-- `rrefOfBareiss` has the exact same row space as `A`. -/
theorem span_row_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    Submodule.span K (Set.range (rrefOfBareiss A S C)) = Submodule.span K (Set.range A) := by
  have hpivot_mem : ∀ a : Fin k, rrefOfBareiss A S C (S a) ∈ Submodule.span K (Set.range A) := by
    intro a
    rw [rrefOfBareiss_pivot_eq_sum hΔ a]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨S b, rfl⟩)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      exact hpivot_mem a
    · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
      rw [rrefOfBareiss_nonPivot_row hΔ hi]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
        (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hpivot_mem a))
  · rintro _ ⟨i, rfl⟩
    by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      rw [row_pivot_eq_sum_rrefOfBareiss hΔ a]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨S b, rfl⟩)
    · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
      have hsub := rrefOfBareiss_nonPivot_row hΔ hi
      have hAi : A i = rrefOfBareiss A S C i +
          ∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a) := by
        rw [hsub, sub_add_cancel]
      rw [hAi]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩)
        (Submodule.sum_mem _ fun a _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨S a, rfl⟩))

/-- `rrefOfBareiss` has the same rank as `A`. -/
theorem rank_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    (rrefOfBareiss A S C).rank = A.rank := by
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row]
  change Module.finrank K (Submodule.span K (Set.range (rrefOfBareiss A S C))) =
    Module.finrank K (Submodule.span K (Set.range A))
  rw [span_row_rrefOfBareiss hΔ]

private theorem dotProduct_eq_zero_of_mem_span {M : Matrix (Fin m) (Fin n) K} {v : Fin n → K}
    (hv : ∀ i, M i ⬝ᵥ v = 0) {w : Fin n → K} (hw : w ∈ Submodule.span K (Set.range M)) :
    w ⬝ᵥ v = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hv i
  | zero => exact zero_dotProduct v
  | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]

/-- `rrefOfBareiss` has the exact same kernel as `A`. -/
theorem ker_mulVecLin_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    LinearMap.ker (rrefOfBareiss A S C).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, funext_iff, mulVec, Pi.zero_apply]
  have hspan := span_row_rrefOfBareiss hΔ
  constructor
  · intro hv i
    have hi : A i ∈ Submodule.span K (Set.range (rrefOfBareiss A S C)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact dotProduct_eq_zero_of_mem_span hv hi
  · intro hv i
    have hi : rrefOfBareiss A S C i ∈ Submodule.span K (Set.range A) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact dotProduct_eq_zero_of_mem_span hv hi

/-- The selected pivot rows `A ∘ S` are linearly independent whenever `pivotDet A S C ≠ 0`. -/
theorem linearIndependent_row_of_pivotDet_ne_zero {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    LinearIndependent K (fun a : Fin k => A (S a)) := by
  refine Fintype.linearIndependent_iff.2 fun c hc a => ?_
  have hc' : (c ᵥ* A.submatrix S C) = 0 := by
    ext b
    simpa only [vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      submatrix_apply, Pi.zero_apply] using congrFun hc (C b)
  have hmul := congrArg (fun u => u ᵥ* (A.submatrix S C)⁻¹) hc'
  rw [vecMul_vecMul, mul_nonsing_inv (A.submatrix S C) (isUnit_iff_ne_zero.mpr hΔ),
    vecMul_one, zero_vecMul] at hmul
  exact congrFun hmul a

/-- When all unpivoted rows vanish in `bareissMatrix`, the pivot rows `A ∘ S` span the entire
row space of `A`. -/
theorem span_rowBasis_eq_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    Submodule.span K (Set.range fun a : Fin k => A (S a)) = Submodule.span K (Set.range A) := by
  rw [← span_row_rrefOfBareiss hΔ]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    rw [span_row_rrefOfBareiss hΔ]
    exact Submodule.subset_span ⟨S a, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      rw [rrefOfBareiss_pivot_eq_sum hΔ a]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
      have hz : rrefOfBareiss A S C i = 0 := by
        ext j
        change (pivotDet A S C)⁻¹ * bareissMatrix A S C i j = 0
        rw [hterm i hi j, mul_zero]
      rw [hz]
      exact Submodule.zero_mem _

/-- When all unpivoted rows vanish, `A.rank = k`. -/
theorem rank_eq_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    A.rank = k := by
  rw [rank_eq_finrank_span_row]
  change Module.finrank K (Submodule.span K (Set.range A)) = k
  rw [← span_rowBasis_eq_of_bareiss_terminal hΔ hterm,
    finrank_span_eq_card (linearIndependent_row_of_pivotDet_ne_zero hΔ), Fintype.card_fin]

/-- Under a row permutation `σ` placing the pivot rows `S` in positions `0, …, k - 1`, strictly
increasing pivot columns `C`, and vanishing left-of-pivot entries `hzero`, the permuted
`rrefOfBareiss` is in Mathlib's `Matrix.IsPivotedBy` and `Matrix.IsReducedRowEchelon` form. -/
theorem isReducedRowEchelon_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hC : StrictMono C)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (hzero : ∀ a : Fin k, ∀ j : Fin n, j < C a → bareissMatrix A S C (S a) j = 0)
    (σ : Equiv.Perm (Fin m)) (hσ : ∀ a : Fin k, σ ⟨a.val, a.isLt.trans_le (by
      have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
      simpa using Fintype.card_le_of_injective S hSinj)⟩ = S a) :
    let U := (rrefOfBareiss A S C).submatrix σ id
    let l : Fin m → WithTop (Fin n) := fun i =>
      if hi : i.val < k then (C ⟨i.val, hi⟩ : WithTop (Fin n)) else ⊤
    U.IsPivotedBy l ∧ U.IsReducedRowEchelon := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_injective S hSinj
  intro U l
  have hU_nonPivot : ∀ {i : Fin m}, ¬i.val < k → U i = 0 := by
    intro i hi
    have hnot : ∀ a : Fin k, S a ≠ σ i := by
      intro a ha
      rw [← hσ a] at ha
      have heq := σ.injective ha
      have : a.val = i.val := congrArg Fin.val heq
      omega
    ext j
    change (pivotDet A S C)⁻¹ * bareissMatrix A S C (σ i) j = 0
    rw [hterm (σ i) hnot j, mul_zero]
  have hU_pivot : ∀ (a : Fin k) (j : Fin n),
      U ⟨a.val, a.isLt.trans_le hkm⟩ j = rrefOfBareiss A S C (S a) j := by
    intro a j
    simp only [U, submatrix_apply, id_eq, hσ a]
  have hU_lead : ∀ (a : Fin k) (j : Fin n), j < C a → U ⟨a.val, a.isLt.trans_le hkm⟩ j = 0 := by
    intro a j hj
    rw [hU_pivot a j]
    change (pivotDet A S C)⁻¹ * bareissMatrix A S C (S a) j = 0
    rw [hzero a j hj, mul_zero]
  have hU_echelon : U.IsRowEchelon := by
    intro i₁ i₂ hlt j₂ hzero₁
    by_cases hi₂ : i₂.val < k
    · have hi₁ : i₁.val < k := Nat.lt_trans hlt hi₂
      let a₁ : Fin k := ⟨i₁.val, hi₁⟩
      let a₂ : Fin k := ⟨i₂.val, hi₂⟩
      have hlt_a : a₁ < a₂ := hlt
      have hj₂ : j₂ < C a₂ := by
        by_contra hle
        have hlt₁ : C a₁ < j₂ := lt_of_lt_of_le (hC hlt_a) (not_lt.mp hle)
        have hone := hzero₁ (C a₁) hlt₁
        have hpiv : U i₁ (C a₁) = 1 := by
          change U ⟨a₁.val, a₁.isLt.trans_le hkm⟩ (C a₁) = 1
          rw [hU_pivot a₁ (C a₁), rrefOfBareiss_pivot_col_self hΔ a₁]
        exact one_ne_zero (hpiv.symm.trans hone)
      exact hU_lead a₂ j₂ hj₂
    · exact congrFun (hU_nonPivot hi₂) j₂
  have hU_piv : U.IsPivotedBy l := by
    refine ⟨hU_echelon, fun i => ?_⟩
    by_cases hi : i.val < k
    · let a : Fin k := ⟨i.val, hi⟩
      have hl : l i = (C a : WithTop (Fin n)) := by simp only [l, hi, ↓reduceDIte, a]
      rw [hl]
      constructor
      · intro j hj
        exact hU_lead a j (WithTop.coe_lt_coe.mp hj)
      · intro c hc
        have hca : C a = c := WithTop.coe_injective hc
        subst hca
        change U ⟨a.val, a.isLt.trans_le hkm⟩ (C a) ≠ 0
        rw [hU_pivot a (C a), rrefOfBareiss_pivot_col_self hΔ a]
        exact one_ne_zero
    · have hl : l i = ⊤ := by simp only [l, hi, ↓reduceDIte]
      rw [hl]
      constructor
      · intro j _
        exact congrFun (hU_nonPivot hi) j
      · intro c hc
        exact absurd hc (by simp)
  have hU_rref : U.IsReducedRowEchelon := by
    refine ⟨hU_echelon, ?_, ?_⟩
    · intro i c hlead
      have hi : i.val < k := by
        by_contra hnot
        exact hlead.row_ne_zero (hU_nonPivot hnot)
      let a : Fin k := ⟨i.val, hi⟩
      have hlead' : U.IsLeadingEntry i (C a) :=
        hU_piv.isLeadingEntry (by simp only [l, hi, ↓reduceDIte, a])
      rw [hlead.unique hlead']
      change U ⟨a.val, a.isLt.trans_le hkm⟩ (C a) = 1
      rw [hU_pivot a (C a), rrefOfBareiss_pivot_col_self hΔ a]
    · intro i₁ i₂ c hlt hlead
      have hi₂ : i₂.val < k := by
        by_contra hnot
        exact hlead.row_ne_zero (hU_nonPivot hnot)
      have hi₁ : i₁.val < k := Nat.lt_trans hlt hi₂
      let a₁ : Fin k := ⟨i₁.val, hi₁⟩
      let a₂ : Fin k := ⟨i₂.val, hi₂⟩
      have hne : a₁ ≠ a₂ := Fin.ne_of_lt hlt
      have hlead' : U.IsLeadingEntry i₂ (C a₂) :=
        hU_piv.isLeadingEntry (by simp only [l, hi₂, ↓reduceDIte, a₂])
      rw [hlead.unique hlead']
      change U ⟨a₁.val, a₁.isLt.trans_le hkm⟩ (C a₂) = 0
      rw [hU_pivot a₁ (C a₂), rrefOfBareiss_pivot_col_ne hΔ hne]
  exact ⟨hU_piv, hU_rref⟩

/-- Canonical right-kernel basis vector associated with a non-pivot column `j`: has `-U (S a) j` in
each pivot column `C a`, `1` at coordinate `j`, and `0` at every other non-pivot column. -/
noncomputable def kernelBasisVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (j : Fin n) : Fin n → K := by
  classical
  exact fun c =>
    if hc : ∃ a : Fin k, C a = c then -rrefOfBareiss A S C (S hc.choose) j
    else if c = j then 1 else 0

theorem kernelBasisVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (j : Fin n) (a : Fin k) :
    kernelBasisVec A S C j (C a) = -rrefOfBareiss A S C (S a) j := by
  classical
  have ⟨_, hCinj⟩ := injective_of_pivotDet_ne_zero hΔ
  have hex : ∃ b : Fin k, C b = C a := ⟨a, rfl⟩
  rw [kernelBasisVec, dite_eq_left_of_eq_true (eq_true hex), hCinj hex.choose_spec]

theorem kernelBasisVec_nonPivot {A : Matrix (Fin m) (Fin n) K}
    (S : Fin k → Fin m) (C : Fin k → Fin n) (j c : Fin n) (hc : ∀ a : Fin k, C a ≠ c) :
    kernelBasisVec A S C j c = if c = j then 1 else 0 := by
  classical
  have hnex : ¬∃ a : Fin k, C a = c := fun ⟨a, ha⟩ => hc a ha
  rw [kernelBasisVec, dite_eq_right_of_eq_false (eq_false hnex)]

/-- Every `kernelBasisVec` associated with a non-pivot column `j` lies in `ker A.mulVecLin`. -/
theorem mulVec_kernelBasisVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ c : Fin n, bareissMatrix A S C i c = 0)
    {j : Fin n} (hj : ∀ a : Fin k, C a ≠ j) :
    A *ᵥ kernelBasisVec A S C j = 0 := by
  have hker := ker_mulVecLin_rrefOfBareiss (A := A) (S := S) (C := C) hΔ
  change A.mulVecLin (kernelBasisVec A S C j) = 0
  rw [← LinearMap.mem_ker, ← hker, LinearMap.mem_ker, mulVecLin_apply]
  ext i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    have hsum : ∑ c : Fin n, rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c =
        ∑ c ∈ Finset.univ \ Finset.image C Finset.univ,
            rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c +
          ∑ c ∈ Finset.image C Finset.univ,
            rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c :=
      (Finset.sum_sdiff (f := fun c => rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c)
        (Finset.subset_univ (Finset.image C Finset.univ))).symm
    have ⟨_, hCinj⟩ := injective_of_pivotDet_ne_zero hΔ
    have hpiv : ∑ c ∈ Finset.image C Finset.univ,
        rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c =
        -rrefOfBareiss A S C (S a) j := by
      rw [Finset.sum_image (fun x _ y _ hxy => hCinj hxy)]
      calc ∑ x : Fin k, rrefOfBareiss A S C (S a) (C x) * kernelBasisVec A S C j (C x)
          = rrefOfBareiss A S C (S a) (C a) * kernelBasisVec A S C j (C a) := by
            refine Finset.sum_eq_single a (fun b _ hba => ?_)
              (fun ha => absurd (Finset.mem_univ a) ha)
            rw [rrefOfBareiss_pivot_col_ne hΔ hba.symm, zero_mul]
        _ = -rrefOfBareiss A S C (S a) j := by
            rw [rrefOfBareiss_pivot_col_self hΔ a, one_mul, kernelBasisVec_pivot hΔ j a]
    have hnon : ∑ c ∈ Finset.univ \ Finset.image C Finset.univ,
        rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c =
        rrefOfBareiss A S C (S a) j := by
      have hjmem : j ∈ Finset.univ \ Finset.image C Finset.univ := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists]
        exact hj
      calc ∑ c ∈ Finset.univ \ Finset.image C Finset.univ,
            rrefOfBareiss A S C (S a) c * kernelBasisVec A S C j c
          = rrefOfBareiss A S C (S a) j * kernelBasisVec A S C j j := by
            refine Finset.sum_eq_single j (fun c hc hcj => ?_) (fun hnj => absurd hjmem hnj)
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and,
              not_exists] at hc
            simp only [kernelBasisVec_nonPivot S C j c hc, hcj, ↓reduceIte, mul_zero]
        _ = rrefOfBareiss A S C (S a) j := by
            simp only [kernelBasisVec_nonPivot S C j j hj, ↓reduceIte, mul_one]
    rw [hsum, hnon, hpiv, add_neg_cancel]
  · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
    refine Finset.sum_eq_zero fun c _ => ?_
    change ((pivotDet A S C)⁻¹ * bareissMatrix A S C i c) * kernelBasisVec A S C j c = 0
    rw [hterm i hi c, mul_zero, zero_mul]

/-- The family of `kernelBasisVec` indexed by non-pivot columns is linearly independent. -/
theorem linearIndependent_kernelBasisVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) :
    LinearIndependent K
      (fun j : { j : Fin n // ∀ a : Fin k, C a ≠ j } => kernelBasisVec A S C j.1) := by
  refine Fintype.linearIndependent_iff.2 fun g hg j => ?_
  have hj := congrFun hg j.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
  have hsum : (∑ x : { j : Fin n // ∀ a : Fin k, C a ≠ j }, g x * kernelBasisVec A S C x.1 j.1) =
      g j := by
    calc (∑ x : { j : Fin n // ∀ a : Fin k, C a ≠ j }, g x * kernelBasisVec A S C x.1 j.1)
        = g j * kernelBasisVec A S C j.1 j.1 := by
          refine Finset.sum_eq_single j (fun j' _ hjne => ?_)
            (fun hnj => absurd (Finset.mem_univ j) hnj)
          have hne : j.1 ≠ j'.1 := fun h => hjne (Subtype.ext h.symm)
          simp only [kernelBasisVec_nonPivot S C j'.1 j.1 j.2, hne, ↓reduceIte, mul_zero]
      _ = g j := by
          simp only [kernelBasisVec_nonPivot S C j.1 j.1 j.2, ↓reduceIte, mul_one]
  exact hsum ▸ hj

/-- The `kernelBasisVec` vectors over non-pivot columns span `LinearMap.ker A.mulVecLin`. -/
theorem span_kernelBasisVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ c : Fin n, bareissMatrix A S C i c = 0) :
    Submodule.span K
        (Set.range fun j : { j : Fin n // ∀ a : Fin k, C a ≠ j } =>
          kernelBasisVec A S C j.1) =
      LinearMap.ker A.mulVecLin := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact mulVec_kernelBasisVec hΔ hterm j.2
  · intro v hv
    rw [← ker_mulVecLin_rrefOfBareiss (A := A) (S := S) (C := C) hΔ] at hv
    rw [LinearMap.mem_ker, mulVecLin_apply] at hv
    have ⟨_, hCinj⟩ := injective_of_pivotDet_ne_zero hΔ
    have hv_eq : v = ∑ j : { j : Fin n // ∀ a : Fin k, C a ≠ j },
        v j.1 • kernelBasisVec A S C j.1 := by
      ext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hc : ∃ a : Fin k, C a = c
      · obtain ⟨a, rfl⟩ := hc
        have hrow := congrFun hv (S a)
        simp only [mulVec, dotProduct, Pi.zero_apply] at hrow
        have hsplit : ∑ x : Fin n, rrefOfBareiss A S C (S a) x * v x =
            ∑ x ∈ Finset.univ \ Finset.image C Finset.univ, rrefOfBareiss A S C (S a) x * v x +
              ∑ x ∈ Finset.image C Finset.univ, rrefOfBareiss A S C (S a) x * v x :=
          (Finset.sum_sdiff (f := fun x => rrefOfBareiss A S C (S a) x * v x)
            (Finset.subset_univ (Finset.image C Finset.univ))).symm
        have hpart₁ : ∑ x ∈ Finset.image C Finset.univ, rrefOfBareiss A S C (S a) x * v x =
            v (C a) := by
          rw [Finset.sum_image (fun x _ y _ hxy => hCinj hxy)]
          calc ∑ x : Fin k, rrefOfBareiss A S C (S a) (C x) * v (C x)
              = rrefOfBareiss A S C (S a) (C a) * v (C a) := by
                refine Finset.sum_eq_single a (fun b _ hba => ?_)
                  (fun ha => absurd (Finset.mem_univ a) ha)
                rw [rrefOfBareiss_pivot_col_ne hΔ hba.symm, zero_mul]
            _ = v (C a) := by rw [rrefOfBareiss_pivot_col_self hΔ a, one_mul]
        have hpart₂ : ∑ x ∈ Finset.univ \ Finset.image C Finset.univ,
            rrefOfBareiss A S C (S a) x * v x =
            -(∑ j : { j : Fin n // ∀ b : Fin k, C b ≠ j },
              v j.1 * kernelBasisVec A S C j.1 (C a)) := by
          rw [← Finset.sum_neg_distrib]
          symm
          refine Finset.sum_bij
            (fun (j : { j : Fin n // ∀ b : Fin k, C b ≠ j }) _ => j.1) ?_ ?_ ?_ ?_
          · intro j _
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists]
            exact j.2
          · intro j₁ _ j₂ _ h
            exact Subtype.ext h
          · intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and,
              not_exists] at hx
            exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
          · intro j _
            rw [kernelBasisVec_pivot hΔ j.1 a, mul_neg, neg_neg, mul_comm]
        rw [hsplit, hpart₁, hpart₂] at hrow
        exact eq_of_sub_eq_zero (by simpa only [← sub_eq_add_neg, add_comm] using hrow)
      · have hnot : ∀ a : Fin k, C a ≠ c := fun a ha => hc ⟨a, ha⟩
        symm
        calc (∑ j : { j : Fin n // ∀ a : Fin k, C a ≠ j }, v j.1 * kernelBasisVec A S C j.1 c)
            = v c * kernelBasisVec A S C c c := by
              refine Finset.sum_eq_single (⟨c, hnot⟩ : { j : Fin n // ∀ a : Fin k, C a ≠ j })
                (fun j _ hjne => ?_) (fun hmem => absurd (Finset.mem_univ _) hmem)
              have hne : c ≠ j.1 := fun h => hjne (Subtype.ext h.symm)
              simp only [kernelBasisVec_nonPivot S C j.1 c hnot, hne, ↓reduceIte, mul_zero]
          _ = v c := by simp only [kernelBasisVec_nonPivot S C c c hnot, ↓reduceIte, mul_one]
    rw [hv_eq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- At termination, `finrank K (LinearMap.ker A.mulVecLin) = n - k`. -/
theorem finrank_ker_mulVecLin_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    Module.finrank K (LinearMap.ker A.mulVecLin) = n - k := by
  have hrn := A.mulVecLin.finrank_range_add_finrank_ker
  have hrk := rank_eq_of_bareiss_terminal hΔ hterm
  change A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) = _ at hrn
  rw [hrk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
  omega

/-- Canonical solution vector supported on the pivot columns `C`, solving the pivot rows `A ∘ S`. -/
noncomputable def solveVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (b : Fin m → K) : Fin n → K := by
  classical
  exact fun c =>
    if hc : ∃ a : Fin k, C a = c then ((A.submatrix S C)⁻¹ *ᵥ (fun t => b (S t))) hc.choose
    else 0

theorem solveVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (b : Fin m → K) (a : Fin k) :
    solveVec A S C b (C a) = ((A.submatrix S C)⁻¹ *ᵥ (fun t => b (S t))) a := by
  classical
  have ⟨_, hCinj⟩ := injective_of_pivotDet_ne_zero hΔ
  have hex : ∃ t : Fin k, C t = C a := ⟨a, rfl⟩
  rw [solveVec, dite_eq_left_of_eq_true (eq_true hex), hCinj hex.choose_spec]

theorem solveVec_nonPivot (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (b : Fin m → K) {c : Fin n}
    (hc : ∀ a : Fin k, C a ≠ c) :
    solveVec A S C b c = 0 := by
  classical
  have hnex : ¬∃ a : Fin k, C a = c := fun ⟨a, ha⟩ => hc a ha
  rw [solveVec, dite_eq_right_of_eq_false (eq_false hnex)]

private theorem dotProduct_solveVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (f : Fin n → K) (b : Fin m → K) :
    f ⬝ᵥ solveVec A S C b = ∑ a : Fin k, f (C a) * solveVec A S C b (C a) := by
  have ⟨_, hCinj⟩ := injective_of_pivotDet_ne_zero hΔ
  have hsplit : f ⬝ᵥ solveVec A S C b =
      ∑ c ∈ Finset.univ \ Finset.image C Finset.univ, f c * solveVec A S C b c +
        ∑ c ∈ Finset.image C Finset.univ, f c * solveVec A S C b c :=
    (Finset.sum_sdiff (f := fun c => f c * solveVec A S C b c)
      (Finset.subset_univ (Finset.image C Finset.univ))).symm
  have hpiv : ∑ c ∈ Finset.image C Finset.univ, f c * solveVec A S C b c =
      ∑ a : Fin k, f (C a) * solveVec A S C b (C a) :=
    Finset.sum_image (fun x _ y _ hxy => hCinj hxy)
  have hnon : ∑ c ∈ Finset.univ \ Finset.image C Finset.univ, f c * solveVec A S C b c = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists] at hc
    rw [solveVec_nonPivot A S C b hc, mul_zero]
  rw [hsplit, hnon, hpiv, zero_add]

/-- `solveVec A S C b` always satisfies the pivot rows `(A *ᵥ x) (S a) = b (S a)`. -/
theorem mulVec_solveVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (b : Fin m → K) (a : Fin k) :
    (A *ᵥ solveVec A S C b) (S a) = b (S a) := by
  change A (S a) ⬝ᵥ solveVec A S C b = b (S a)
  rw [dotProduct_solveVec hΔ (A (S a)) b]
  have hinv := congrFun (congrArg (fun M => M *ᵥ (fun s => b (S s)))
    (mul_nonsing_inv (A.submatrix S C) (isUnit_iff_ne_zero.mpr hΔ))) a
  rw [one_mulVec, ← mulVec_mulVec] at hinv
  have hsum : ∑ t : Fin k, A (S a) (C t) * solveVec A S C b (C t) =
      ∑ t : Fin k, A (S a) (C t) * ((A.submatrix S C)⁻¹ *ᵥ (fun s => b (S s))) t :=
    Finset.sum_congr rfl fun t _ => by rw [solveVec_pivot hΔ b t]
  rw [hsum]
  simpa only [mulVec, dotProduct, submatrix_apply] using hinv

/-- `solveVec A S C b` solves `A *ᵥ x = b` iff `A *ᵥ x = b` is consistent. -/
theorem mulVec_solveVec_eq_iff_exists_mulVec_eq {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (b : Fin m → K) :
    A *ᵥ solveVec A S C b = b ↔ ∃ x : Fin n → K, A *ᵥ x = b := by
  refine ⟨fun h => ⟨solveVec A S C b, h⟩, ?_⟩
  rintro ⟨x, rfl⟩
  ext i
  have hspan := span_rowBasis_eq_of_bareiss_terminal hΔ hterm
  have hi : A i ∈ Submodule.span K (Set.range (Matrix.of fun a : Fin k => A (S a))) := by
    change A i ∈ Submodule.span K (Set.range fun a : Fin k => A (S a))
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have horth : ∀ a : Fin k, (Matrix.of fun t : Fin k => A (S t)) a ⬝ᵥ
      (x - solveVec A S C (A *ᵥ x)) = 0 := by
    intro a
    change A (S a) ⬝ᵥ (x - solveVec A S C (A *ᵥ x)) = 0
    rw [dotProduct_sub]
    change (A *ᵥ x) (S a) - (A *ᵥ solveVec A S C (A *ᵥ x)) (S a) = 0
    rw [mulVec_solveVec_pivot hΔ (A *ᵥ x) a, sub_self]
  have hdot := dotProduct_eq_zero_of_mem_span horth hi
  rw [dotProduct_sub] at hdot
  exact (sub_eq_zero.mp hdot).symm

/-- Augmented matrix `[A | b]`. -/
@[expose] def augmentCol {R : Type*} (A : Matrix (Fin m) (Fin n) R) (b : Fin m → R) :
    Matrix (Fin m) (Fin (n + 1)) R :=
  of fun i => Fin.snoc (A i) (b i)

/-- The Bareiss–Jordan reduction of `[A | b]` at `(S, Fin.castSucc ∘ C)` yields `solveVec A S C b`
on pivot rows in the last column, and vanishes on unpivoted rows iff `A *ᵥ solveVec A S C b = b`. -/
theorem rrefOfBareiss_augmentCol {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (b : Fin m → K) :
    let Aaug := augmentCol A b
    let Caug := Fin.castSucc ∘ C
    (∀ a : Fin k, rrefOfBareiss Aaug S Caug (S a) (Fin.last n) = solveVec A S C b (C a)) ∧
      (A *ᵥ solveVec A S C b = b ↔
        ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) →
          bareissMatrix Aaug S Caug i (Fin.last n) = 0) := by
  intro Aaug Caug
  have hsub : Aaug.submatrix S Caug = A.submatrix S C := by
    ext u v
    simp only [submatrix_apply, Aaug, augmentCol, of_apply, Caug, Function.comp_apply,
      Fin.snoc_castSucc]
  have hΔaug : pivotDet Aaug S Caug ≠ 0 := by
    change (Aaug.submatrix S Caug).det ≠ 0
    rw [hsub]
    exact hΔ
  have hcol : ∀ a : Fin k,
      rrefOfBareiss Aaug S Caug (S a) (Fin.last n) = solveVec A S C b (C a) := by
    intro a
    rw [rrefOfBareiss_pivot_entry hΔaug a (Fin.last n), solveVec_pivot hΔ b a]
    have hvec : (fun t => Aaug (S t) (Fin.last n)) = (fun t => b (S t)) := by
      ext t
      simp only [Aaug, augmentCol, of_apply, Fin.snoc_last]
    rw [hsub, hvec]
  refine ⟨hcol, ?_⟩
  have hnon : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) →
      rrefOfBareiss Aaug S Caug i (Fin.last n) = b i - (A *ᵥ solveVec A S C b) i := by
    intro i hi
    have hr := congrFun (rrefOfBareiss_nonPivot_row hΔaug hi) (Fin.last n)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr
    have hAi_aug : Aaug i (Fin.last n) = b i := by
      simp only [Aaug, augmentCol, of_apply, Fin.snoc_last]
    have hAiC : ∀ a : Fin k, Aaug i (Caug a) = A i (C a) := fun a => by
      simp only [Aaug, augmentCol, of_apply, Caug, Function.comp_apply, Fin.snoc_castSucc]
    have hUzero : rrefOfBareiss A S C i = 0 := by
      ext j
      change (pivotDet A S C)⁻¹ * bareissMatrix A S C i j = 0
      rw [hterm i hi j, mul_zero]
    have hAi_lin : A i = ∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a) := by
      have hrA := rrefOfBareiss_nonPivot_row hΔ hi
      rw [hUzero] at hrA
      exact sub_eq_zero.mp hrA.symm
    have hdot : ∀ a : Fin k,
        rrefOfBareiss A S C (S a) ⬝ᵥ solveVec A S C b = solveVec A S C b (C a) := by
      intro a
      rw [dotProduct_solveVec hΔ (rrefOfBareiss A S C (S a)) b]
      calc ∑ t : Fin k, rrefOfBareiss A S C (S a) (C t) * solveVec A S C b (C t)
          = rrefOfBareiss A S C (S a) (C a) * solveVec A S C b (C a) := by
            refine Finset.sum_eq_single a (fun t _ hta => ?_)
              (fun ha => absurd (Finset.mem_univ a) ha)
            rw [rrefOfBareiss_pivot_col_ne hΔ hta.symm, zero_mul]
        _ = solveVec A S C b (C a) := by rw [rrefOfBareiss_pivot_col_self hΔ a, one_mul]
    have hmulVec : (A *ᵥ solveVec A S C b) i =
        ∑ a : Fin k, A i (C a) * solveVec A S C b (C a) := by
      change A i ⬝ᵥ solveVec A S C b = _
      conv_lhs => rw [hAi_lin, sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul, hdot]
    rw [hr, hAi_aug, hmulVec]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hAiC a, hcol a]
  constructor
  · intro hsol i hi
    have hz := hnon i hi
    rw [hsol, sub_self] at hz
    change (pivotDet Aaug S Caug)⁻¹ * bareissMatrix Aaug S Caug i (Fin.last n) = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hΔaug)
  · intro hzeros
    ext i
    by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      exact mulVec_solveVec_pivot hΔ b a
    · have hi : ∀ a : Fin k, S a ≠ i := fun a ha => hrow ⟨a, ha⟩
      have hz := hnon i hi
      have hzr : rrefOfBareiss Aaug S Caug i (Fin.last n) = 0 := by
        change (pivotDet Aaug S Caug)⁻¹ * bareissMatrix Aaug S Caug i (Fin.last n) = 0
        rw [hzeros i hi, mul_zero]
      rw [hzr] at hz
      exact (sub_eq_zero.mp hz.symm).symm

end FieldResults

end MinorMatrix

end Matrix
