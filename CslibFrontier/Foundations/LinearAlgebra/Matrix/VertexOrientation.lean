/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/VertexOrientation.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Vertex
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

/-!
# Determinant signs across polyhedral vertex pivots

This module connects the basic feasible vertices of `Matrix.IsVertex` to matrix determinants and
establishes the sign-reversal law across pivot edges used by Shapley's orientation of
Lemke–Howson paths [Shapley1974].

## Main definitions

* `Matrix.pivotBasisEquiv`: the row-index equivalence across an edge replacing one tight row
  `l` of a vertex by an entering tight row `l'`.

## Main results

* `Matrix.IsVertex.det_submatrix_ne_zero`: any bijection onto a vertex's tight rows gives a
  nonsingular square basis matrix.
* `Matrix.isVertex_of_det_submatrix_ne_zero`: conversely, a feasible point with a nonsingular
  subset of tight rows is a vertex.
* `Matrix.IsVertex.det_updateRow_pivot_mul_lt_zero`: replacing the leaving tight row `l` by the
  entering tight row `l'` reverses the sign of the basis determinant.
* `Matrix.IsVertex.det_submatrix_pivot_mul_lt_zero`: the determinant sign relation across a pivot
  for arbitrary row enumerations `e₁`, `e₂`, weighted by `Equiv.Perm.sign`.

## References

* [L. S. Shapley, *A note on the Lemke–Howson algorithm*][Shapley1974]
-/

public section

namespace Matrix

section PivotEquiv

variable {κ ι : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Row-index equivalence for the adjacent basis `T₂` obtained by replacing `l ∈ T₁` with
`l' ∈ T₂` in an enumeration `e₁ : ι ≃ T₁`. -/
def pivotBasisEquiv {T₁ T₂ : Finset κ} (e₁ : ι ≃ T₁) {l l' : κ}
    (hl : l ∈ T₁) (hl' : l' ∈ T₂) (herase : T₁.erase l = T₂.erase l') : ι ≃ T₂ :=
  let i₀ := e₁.symm ⟨l, hl⟩
  have hmem_T2 : ∀ i : ι, i ≠ i₀ → (e₁ i : κ) ∈ T₂ := fun i hi => by
    have hne : (e₁ i : κ) ≠ l := fun h => by
      apply hi
      apply e₁.injective
      apply Subtype.ext
      simpa only [i₀, Equiv.apply_symm_apply] using h
    have hmem : (e₁ i : κ) ∈ T₁.erase l := Finset.mem_erase.2 ⟨hne, (e₁ i).2⟩
    rw [herase] at hmem
    exact (Finset.mem_erase.1 hmem).2
  have hmem_T1 : ∀ y : T₂, (y : κ) ≠ l' → (y : κ) ∈ T₁ := fun y hy => by
    have hmem : (y : κ) ∈ T₂.erase l' := Finset.mem_erase.2 ⟨hy, y.2⟩
    rw [← herase] at hmem
    exact (Finset.mem_erase.1 hmem).2
  { toFun := fun i => if hi : i = i₀ then ⟨l', hl'⟩ else ⟨(e₁ i : κ), hmem_T2 i hi⟩
    invFun := fun y => if hy : (y : κ) = l' then i₀ else e₁.symm ⟨(y : κ), hmem_T1 y hy⟩
    left_inv := fun i => by
      by_cases hi : i = i₀
      · simp [hi]
      · have hne' : (e₁ i : κ) ≠ l' := by
          have hne : (e₁ i : κ) ≠ l := fun h => by
            apply hi
            apply e₁.injective
            apply Subtype.ext
            simpa only [i₀, Equiv.apply_symm_apply] using h
          have hmem : (e₁ i : κ) ∈ T₁.erase l := Finset.mem_erase.2 ⟨hne, (e₁ i).2⟩
          rw [herase] at hmem
          exact (Finset.mem_erase.1 hmem).1
        simp [hi, hne']
    right_inv := fun y => by
      by_cases hy : (y : κ) = l'
      · simp only [hy, ↓reduceDIte]
        exact Subtype.ext hy.symm
      · have hne : e₁.symm ⟨(y : κ), hmem_T1 y hy⟩ ≠ i₀ := by
          intro heq
          have hval : (e₁ (e₁.symm ⟨(y : κ), hmem_T1 y hy⟩) : κ) = (e₁ i₀ : κ) :=
            congrArg (fun z : T₁ => (z : κ)) (congrArg e₁ heq)
          simp only [i₀, Equiv.apply_symm_apply] at hval
          have hmem : (y : κ) ∈ T₂.erase l' := Finset.mem_erase.2 ⟨hy, y.2⟩
          rw [← herase] at hmem
          exact (Finset.mem_erase.1 hmem).1 hval
        simp [hy, hne] }

@[simp]
theorem coe_pivotBasisEquiv_apply {T₁ T₂ : Finset κ} (e₁ : ι ≃ T₁) {l l' : κ}
    (hl : l ∈ T₁) (hl' : l' ∈ T₂) (herase : T₁.erase l = T₂.erase l') (i : ι) :
    (pivotBasisEquiv e₁ hl hl' herase i : κ) =
      if i = e₁.symm ⟨l, hl⟩ then l' else (e₁ i : κ) := by
  simp only [pivotBasisEquiv, Equiv.coe_fn_mk]
  split_ifs <;> rfl

end PivotEquiv

section Orientation

variable {κ ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [IsStrictOrderedRing K] [DecidableEq κ] in
/-- Any bijection onto the tight rows of a vertex gives a square basis matrix with nonzero
determinant. -/
theorem IsVertex.det_submatrix_ne_zero {A : Matrix κ ι K} {b : κ → K} {x : ι → K}
    (hx : IsVertex A b x) (e : ι ≃ tightRows A b x) :
    (A.submatrix (fun i => (e i : κ)) id).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine hv0 ((isVertex_iff.1 hx).2 v fun k hk => ?_)
  have hk' := congrFun hMv (e.symm ⟨k, hk⟩)
  have hk'' : (A *ᵥ v) (e (e.symm ⟨k, hk⟩) : κ) = 0 := by
    simpa only [mulVec, dotProduct, submatrix_apply, id_eq, Pi.zero_apply] using hk'
  simpa only [Equiv.apply_symm_apply] using hk''

omit [DecidableEq κ] in
/-- Conversely, a feasible point with a square nonsingular subset of tight rows is a vertex. -/
theorem isVertex_of_det_submatrix_ne_zero {A : Matrix κ ι K} {b : κ → K} {x : ι → K}
    (hle : A *ᵥ x ≤ b) {S : Finset κ} (hS : S ⊆ tightRows A b x) (e : ι ≃ S)
    (hdet : (A.submatrix (fun i => (e i : κ)) id).det ≠ 0) : IsVertex A b x := by
  refine isVertex_iff.2 ⟨hle, fun v hv => Matrix.mulVec_injective_of_det_ne_zero hdet ?_⟩
  ext i
  simp only [mulVec, dotProduct, submatrix_apply, id_eq, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]
  exact hv (e i : κ) (hS (e i).2)

/-- Replacing the leaving tight row `l` by the entering tight row `l'` across an adjacent pivot
reverses the sign of the square basis determinant. -/
theorem IsVertex.det_updateRow_pivot_mul_lt_zero
    {A : Matrix κ ι K} {b : κ → K} {x y : ι → K}
    (hx : IsVertex A b x) (hy : IsVertex A b y) (hne : x ≠ y)
    {l l' : κ} (hl : l ∈ tightRows A b x) (hl' : l' ∈ tightRows A b y)
    (herase : (tightRows A b x).erase l = (tightRows A b y).erase l')
    (e : ι ≃ tightRows A b x) :
    let M := A.submatrix (fun i => (e i : κ)) id
    M.det * (M.updateRow (e.symm ⟨l, hl⟩) (A l')).det < 0 := by
  intro M
  set i₀ := e.symm ⟨l, hl⟩
  have hdet0 : M.det ≠ 0 := hx.det_submatrix_ne_zero e
  have hl'_not_x : l' ∉ tightRows A b x := by
    intro hl'x
    have hsub : tightRows A b y ⊆ tightRows A b x := by
      intro k hk
      by_cases hkl' : k = l'
      · exact hkl' ▸ hl'x
      · have hmem : k ∈ (tightRows A b y).erase l' := Finset.mem_erase.2 ⟨hkl', hk⟩
        rw [← herase] at hmem
        exact (Finset.mem_erase.1 hmem).2
    exact hne (hy.eq_of_tightRows_subset hsub)
  have hl_not_y : l ∉ tightRows A b y := by
    intro hly
    have hsub : tightRows A b x ⊆ tightRows A b y := by
      intro k hk
      by_cases hkl : k = l
      · exact hkl ▸ hly
      · have hmem : k ∈ (tightRows A b x).erase l := Finset.mem_erase.2 ⟨hkl, hk⟩
        rw [herase] at hmem
        exact (Finset.mem_erase.1 hmem).2
    exact hne (hx.eq_of_tightRows_subset hsub).symm
  have hl'_diff : 0 < (A l') ⬝ᵥ (y - x) := by
    have hxlt : (A *ᵥ x) l' < b l' :=
      (hx.mulVec_le l').lt_of_ne (fun heq => hl'_not_x (mem_tightRows.2 heq))
    have hyeq : (A *ᵥ y) l' = b l' := mem_tightRows.1 hl'
    rw [dotProduct_sub]
    change 0 < (A *ᵥ y) l' - (A *ᵥ x) l'
    linarith
  have hl_diff : (A l) ⬝ᵥ (y - x) < 0 := by
    have hylt : (A *ᵥ y) l < b l :=
      (hy.mulVec_le l).lt_of_ne (fun heq => hl_not_y (mem_tightRows.2 heq))
    have hxeq : (A *ᵥ x) l = b l := mem_tightRows.1 hl
    rw [dotProduct_sub]
    change (A *ᵥ y) l - (A *ᵥ x) l < 0
    linarith
  have hother : ∀ i : ι, i ≠ i₀ → (M i) ⬝ᵥ (y - x) = 0 := by
    intro i hi
    have hne_l : (e i : κ) ≠ l := fun h => by
      apply hi
      apply e.injective
      apply Subtype.ext
      simpa only [i₀, Equiv.apply_symm_apply] using h
    have hmem_x : (e i : κ) ∈ tightRows A b x := (e i).2
    have hmem_y : (e i : κ) ∈ tightRows A b y := by
      have hm := Finset.mem_erase.2 ⟨hne_l, hmem_x⟩
      rw [herase] at hm
      exact (Finset.mem_erase.1 hm).2
    have hx_eq : (A *ᵥ x) (e i : κ) = b (e i : κ) := mem_tightRows.1 hmem_x
    have hy_eq : (A *ᵥ y) (e i : κ) = b (e i : κ) := mem_tightRows.1 hmem_y
    change (A (e i : κ)) ⬝ᵥ (y - x) = 0
    rw [dotProduct_sub]
    change (A *ᵥ y) (e i : κ) - (A *ᵥ x) (e i : κ) = 0
    rw [hy_eq, hx_eq, sub_self]
  let c : ι → K := Mᵀ.cramer (A l')
  have hMc : Mᵀ *ᵥ c = M.det • A l' := by
    simpa only [det_transpose] using Matrix.mulVec_cramer Mᵀ (A l')
  have hdot : (Mᵀ *ᵥ c) ⬝ᵥ (y - x) = (M.det • A l') ⬝ᵥ (y - x) := congrArg (· ⬝ᵥ (y - x)) hMc
  rw [← vecMul_transpose, transpose_transpose, ← dotProduct_mulVec, smul_dotProduct,
    smul_eq_mul] at hdot
  have hsum : c ⬝ᵥ (M *ᵥ (y - x)) = (A l) ⬝ᵥ (y - x) * c i₀ := by
    rw [dotProduct, Finset.sum_eq_single i₀]
    · have hi₀ : M i₀ = A l := by
        ext j
        simp [M, i₀]
      rw [mul_comm, ← hi₀]
      rfl
    · intro i _ hi
      change c i * ((M i) ⬝ᵥ (y - x)) = 0
      rw [hother i hi, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem
  have hc_i₀ : c i₀ = (M.updateRow i₀ (A l')).det := Matrix.cramer_transpose_apply M (A l') i₀
  have hrel : (A l) ⬝ᵥ (y - x) * (M.updateRow i₀ (A l')).det = M.det * ((A l') ⬝ᵥ (y - x)) := by
    rw [← hc_i₀, ← hsum, hdot]
  have hmul : (M.det * (M.updateRow i₀ (A l')).det) * ((A l) ⬝ᵥ (y - x)) =
      M.det ^ 2 * ((A l') ⬝ᵥ (y - x)) := by
    calc (M.det * (M.updateRow i₀ (A l')).det) * ((A l) ⬝ᵥ (y - x))
        = M.det * ((A l) ⬝ᵥ (y - x) * (M.updateRow i₀ (A l')).det) := by ring
      _ = M.det * (M.det * ((A l') ⬝ᵥ (y - x))) := by rw [hrel]
      _ = M.det ^ 2 * ((A l') ⬝ᵥ (y - x)) := by ring
  have hrhs_pos : 0 < M.det ^ 2 * ((A l') ⬝ᵥ (y - x)) :=
    mul_pos (sq_pos_of_ne_zero hdet0) hl'_diff
  rw [← hmul] at hrhs_pos
  exact neg_of_mul_pos_left hrhs_pos hl_diff.le

/-- Across an adjacent pivot edge from `x` to `y` (`l` leaving `x`, `l'` entering `y`), the
determinant signs with respect to arbitrary row bijections `e₁`, `e₂` satisfy
`Perm.sign σ * det M₁ * det M₂ < 0`, where `σ = e₂⁻¹ ∘ pivotBasisEquiv e₁`. -/
theorem IsVertex.det_submatrix_pivot_mul_lt_zero
    {A : Matrix κ ι K} {b : κ → K} {x y : ι → K}
    (hx : IsVertex A b x) (hy : IsVertex A b y) (hne : x ≠ y)
    {l l' : κ} (hl : l ∈ tightRows A b x) (hl' : l' ∈ tightRows A b y)
    (herase : (tightRows A b x).erase l = (tightRows A b y).erase l')
    (e₁ : ι ≃ tightRows A b x) (e₂ : ι ≃ tightRows A b y) :
    let σ : Equiv.Perm ι := (pivotBasisEquiv e₁ hl hl' herase).trans e₂.symm
    (Equiv.Perm.sign σ : K) *
      ((A.submatrix (fun i => (e₁ i : κ)) id).det *
        (A.submatrix (fun i => (e₂ i : κ)) id).det) < 0 := by
  intro σ
  set M₁ := A.submatrix (fun i => (e₁ i : κ)) id
  set M₂ := A.submatrix (fun i => (e₂ i : κ)) id
  have hup : M₁.updateRow (e₁.symm ⟨l, hl⟩) (A l') = M₂.submatrix σ id := by
    ext i j
    simp only [updateRow_apply, submatrix_apply, id_eq, M₁, M₂, σ, Equiv.trans_apply,
      Equiv.apply_symm_apply, coe_pivotBasisEquiv_apply]
    split_ifs <;> rfl
  have hdet : (M₁.updateRow (e₁.symm ⟨l, hl⟩) (A l')).det =
      (Equiv.Perm.sign σ : K) * M₂.det := by
    rw [hup, Matrix.det_permute σ M₂]
  have hneg := hx.det_updateRow_pivot_mul_lt_zero hy hne hl hl' herase e₁
  dsimp only at hneg
  change M₁.det * (M₁.updateRow (e₁.symm ⟨l, hl⟩) (A l')).det < 0 at hneg
  rw [hdet] at hneg
  simpa only [mul_left_comm, mul_assoc] using hneg

end Orientation

end Matrix
