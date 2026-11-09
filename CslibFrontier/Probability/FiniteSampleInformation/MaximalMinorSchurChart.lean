/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.MaximalMinorDefs

/-!
# The fixed Schur chart for a wide generic matrix

We write the dimensions as `(k + 1) × (k + r)`.  The first `k` columns
form the pivot block.  A nonpivot column is indexed by `β : Fin r`; adjoining
that column after the pivot columns gives an increasing maximal-minor index,
so the corresponding bordered determinant has sign `+1`.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`MaximalMinorSchurChart.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace WidePolynomial

open GeneralAsymmetricC1

section Indices

/-- The inclusion of a pivot row into all rows. -/
@[expose] def pivotRow (k : ℕ) : Fin k → Fin (k + 1) := Fin.castSucc

/-- The last row of the fixed Schur chart. -/
@[expose] def schurLastRow (k : ℕ) : Fin (k + 1) := Fin.last k

/-- The inclusion of a pivot column into all columns. -/
@[expose] def pivotColumn (k r : ℕ) : Fin k → Fin (k + r) := Fin.castAdd r

/-- The inclusion of a nonpivot column into all columns. -/
@[expose] def freeColumn (k r : ℕ) : Fin r → Fin (k + r) := Fin.natAdd k

/-- The ordered list consisting of all pivot columns followed by `β`. -/
@[expose] def schurColumn (k r : ℕ) (β : Fin r) (j : Fin (k + 1)) : Fin (k + r) :=
  if h : j.val < k then
    ⟨j.val, lt_of_lt_of_le h (Nat.le_add_right k r)⟩
  else
    ⟨k + β.val, Nat.add_lt_add_left β.isLt k⟩

@[simp]
lemma schurColumn_castSucc (k r : ℕ) (β : Fin r) (j : Fin k) :
    schurColumn k r β j.castSucc = pivotColumn k r j := by
  apply Fin.ext
  simp [schurColumn, pivotColumn]

@[simp]
lemma schurColumn_last (k r : ℕ) (β : Fin r) :
    schurColumn k r β (Fin.last k) = freeColumn k r β := by
  simp [schurColumn, freeColumn, Fin.ext_iff]

/-- The canonical increasing column index for a fixed Schur minor. -/
@[expose] def schurMinorIndex (k r : ℕ) (β : Fin r) : MinorIndex (k + 1) (k + r) :=
  OrderEmbedding.ofStrictMono (schurColumn k r β) <| by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    simp only [schurColumn, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> simp only [Fin.mk_lt_mk] <;> omega

@[simp]
lemma schurMinorIndex_castSucc (k r : ℕ) (β : Fin r) (j : Fin k) :
    schurMinorIndex k r β j.castSucc = pivotColumn k r j :=
  schurColumn_castSucc k r β j

@[simp]
lemma schurMinorIndex_last (k r : ℕ) (β : Fin r) :
    schurMinorIndex k r β (Fin.last k) = freeColumn k r β :=
  schurColumn_last k r β

end Indices

section Blocks

variable {R : Type*}

/-- The leading `k × k` pivot block of a `(k+1) × (k+r)` matrix. -/
@[expose] def pivotBlock {k r : ℕ} (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) :
    Matrix (Fin k) (Fin k) R :=
  fun i j => U (pivotRow k i) (pivotColumn k r j)

/-- The top part of nonpivot column `β`. -/
@[expose] def schurTopColumn {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) (β : Fin r) :
    Matrix (Fin k) (Fin 1) R :=
  fun i _ => U (pivotRow k i) (freeColumn k r β)

/-- The last row restricted to the pivot columns. -/
@[expose] def schurBottomRow {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) :
    Matrix (Fin 1) (Fin k) R :=
  fun _ j => U (schurLastRow k) (pivotColumn k r j)

/-- The last entry of nonpivot column `β`, as a `1 × 1` block. -/
@[expose] def schurBottomEntry {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) (β : Fin r) :
    Matrix (Fin 1) (Fin 1) R :=
  fun _ _ => U (schurLastRow k) (freeColumn k r β)

/-- The bordered square matrix for nonpivot column `β`. -/
@[expose] def schurBorderedMatrix {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) (β : Fin r) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  fun i j => U i (schurColumn k r β j)

lemma schurBorderedMatrix_eq_submatrix {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) (β : Fin r) :
    schurBorderedMatrix U β = U.submatrix id (schurMinorIndex k r β) := by
  rfl

lemma schurBorderedMatrix_eq_reindex_fromBlocks {k r : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + r)) R) (β : Fin r) :
    schurBorderedMatrix U β =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (pivotBlock U) (schurTopColumn U β)
          (schurBottomRow U) (schurBottomEntry U β)) := by
  ext i j
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  have hcast (x : Fin k) : Fin.castAdd 1 x = x.castSucc := by
    apply Fin.ext
    rfl
  have hlast : Fin.natAdd k (0 : Fin 1) = Fin.last k := by
    apply Fin.ext
    simp
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize e.symm i = i'
  generalize e.symm j = j'
  cases i' with
  | inl i =>
      cases j' with
      | inl j =>
          simp [e, hcast, schurBorderedMatrix, pivotBlock, pivotRow, pivotColumn]
      | inr j =>
          fin_cases j
          simp [e, hcast, hlast, schurBorderedMatrix, schurTopColumn,
            pivotRow, freeColumn]
  | inr i =>
      fin_cases i
      cases j' with
      | inl j =>
          simp [e, hcast, hlast, schurBorderedMatrix, schurBottomRow,
            schurLastRow, pivotColumn]
      | inr j =>
          fin_cases j
          simp [e, hlast, schurBorderedMatrix, schurBottomEntry,
            schurLastRow, freeColumn]

/-- The bordered determinant identity over a field. -/
lemma det_fromBlocks_fin_one
    {K : Type*} [Field K] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) K)
    (B : Matrix (Fin k) (Fin 1) K)
    (C : Matrix (Fin 1) (Fin k) K)
    (D : Matrix (Fin 1) (Fin 1) K)
    (hA : A.det ≠ 0) :
    (Matrix.fromBlocks A B C D).det =
      A.det * D 0 0 - (C * A.adjugate * B) 0 0 := by
  let : Invertible A.det := invertibleOfNonzero hA
  let : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq]
  simp only [Matrix.sub_apply]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hinv : ⅟A.det * A.det = 1 := invOf_mul_self A.det
  calc
    A.det * (D 0 0 - ⅟A.det * (C * A.adjugate * B) 0 0) =
        A.det * D 0 0 - (⅟A.det * A.det) * (C * A.adjugate * B) 0 0 := by
      ring
    _ = A.det * D 0 0 - (C * A.adjugate * B) 0 0 := by
      rw [hinv, one_mul]

/-- The same identity over a domain, proved by embedding into its fraction
field.  This avoids expanding the determinant. -/
lemma det_fromBlocks_fin_one_of_det_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin 1) R)
    (C : Matrix (Fin 1) (Fin k) R)
    (D : Matrix (Fin 1) (Fin 1) R)
    (hA : A.det ≠ 0) :
    (Matrix.fromBlocks A B C D).det =
      A.det * D 0 0 - (C * A.adjugate * B) 0 0 := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  apply (IsFractionRing.injective R K)
  have hAmap : (A.map f).det ≠ 0 := by
    change (f.mapMatrix A).det ≠ 0
    rw [← f.map_det]
    intro hzero
    apply hA
    have hz : (algebraMap R K) A.det = (algebraMap R K) 0 := by
      change f A.det = f 0
      simpa using hzero
    exact IsFractionRing.injective R K hz
  have hfield := det_fromBlocks_fin_one
    (A.map f) (B.map f) (C.map f) (D.map f) hAmap
  calc
    f (Matrix.fromBlocks A B C D).det =
        (Matrix.fromBlocks (A.map f) (B.map f) (C.map f) (D.map f)).det := by
      rw [f.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]
    _ = (A.map f).det * (D.map f) 0 0 -
        (C.map f * (A.map f).adjugate * B.map f) 0 0 := hfield
    _ = f (A.det * D 0 0 - (C * A.adjugate * B) 0 0) := by
      rw [map_sub, map_mul]
      rw [f.map_det]
      change (A.map f).det * (D.map f) 0 0 -
          (C.map f * (A.map f).adjugate * B.map f) 0 0 =
        (A.map f).det * (D.map f) 0 0 -
          ((C * A.adjugate * B).map f) 0 0
      rw [Matrix.map_mul, Matrix.map_mul]
      rw [show A.adjugate.map f = (A.map f).adjugate by
        simpa only [RingHom.mapMatrix_apply] using f.map_adjugate A]

end Blocks

section GenericPolynomials

/-- The determinant of the leading `k × k` generic pivot block. -/
@[expose] def pivotMinor (k r : ℕ) : WidePoly (k + 1) (k + r) :=
  Matrix.det (pivotBlock
    (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ))

/-- The explicit Schur numerator `det(A) d - cᵀ adj(A) b`. -/
@[expose] def schurAdjugateNumerator (k r : ℕ) (β : Fin r) :
    WidePoly (k + 1) (k + r) :=
  let Xmat := Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ
  pivotMinor k r * (schurBottomEntry Xmat β) 0 0 -
    (schurBottomRow Xmat * (pivotBlock Xmat).adjugate *
      schurTopColumn Xmat β) 0 0

/-- The Schur numerator for nonpivot column `β`, defined as its ordered
maximal minor. -/
@[expose] def schurMinor (k r : ℕ) (β : Fin r) : WidePoly (k + 1) (k + r) :=
  maximalMinorPoly (schurMinorIndex k r β)

theorem schurMinor_eq_maximalMinor (k r : ℕ) (β : Fin r) :
    schurMinor k r β = maximalMinorPoly (schurMinorIndex k r β) :=
  rfl

lemma eval_pivotMinor {k r : ℕ} (U : Mat (k + 1) (k + r)) :
    MvPolynomial.eval (fun ia => U ia.1 ia.2) (pivotMinor k r) =
      Matrix.det (pivotBlock U) := by
  let e : WidePoly (k + 1) (k + r) →+* ℝ :=
    MvPolynomial.eval (fun ia => U ia.1 ia.2)
  change e (pivotMinor k r) = Matrix.det (pivotBlock U)
  rw [pivotMinor, e.map_det]
  congr 1
  ext i j
  simp [e, pivotBlock, pivotRow, pivotColumn]

lemma pivotMinor_ne_zero (k r : ℕ) : pivotMinor k r ≠ 0 := by
  let U : Mat (k + 1) (k + r) :=
    fun i a => if i.val = a.val then 1 else 0
  have hblock : pivotBlock U = (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    simp [U, pivotBlock, pivotRow, pivotColumn, Matrix.one_apply, Fin.ext_iff]
  intro hzero
  have heval := eval_pivotMinor (k := k) (r := r) U
  rw [hzero, map_zero, hblock, Matrix.det_one] at heval
  norm_num at heval

theorem schurMinor_eq_adjugateNumerator (k r : ℕ) (β : Fin r) :
    schurMinor k r β = schurAdjugateNumerator k r β := by
  let Xmat := Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ
  unfold schurMinor maximalMinorPoly maximalMinorMatrix schurMinorIndex
  change Matrix.det (schurBorderedMatrix Xmat β) = _
  rw [schurBorderedMatrix_eq_reindex_fromBlocks]
  rw [Matrix.det_reindex_self]
  exact det_fromBlocks_fin_one_of_det_ne_zero
    (pivotBlock Xmat) (schurTopColumn Xmat β)
      (schurBottomRow Xmat) (schurBottomEntry Xmat β)
      (pivotMinor_ne_zero k r)

lemma eval_schurMinor {k r : ℕ} (β : Fin r)
    (U : Mat (k + 1) (k + r)) :
    MvPolynomial.eval (fun ia => U ia.1 ia.2) (schurMinor k r β) =
      Matrix.det (schurBorderedMatrix U β) := by
  rw [schurMinor, eval_maximalMinorPoly]
  rfl

lemma schurMinor_mem_maximalMinorIdeal (k r : ℕ) (β : Fin r) :
    schurMinor k r β ∈ maximalMinorIdeal (k + 1) (k + r) := by
  exact maximalMinorPoly_mem_ideal (schurMinorIndex k r β)

end GenericPolynomials

end WidePolynomial


end

end Cslib.FiniteSampleInformation
