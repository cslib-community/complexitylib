/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Characterization and invariance of the Gram–Schmidt process

Mathlib's `InnerProductSpace.gramSchmidt 𝕜 f` orthogonalizes a family `f : ι → E` indexed by a
locally finite linear order. This file adds the facts about it that lattice basis reduction uses.

`gramSchmidt 𝕜 f i` is the unique vector that differs from `f i` by an element of the span of the
earlier vectors and is orthogonal to that span
(`InnerProductSpace.eq_gramSchmidt_of_sub_mem_of_mem_orthogonal`). It follows that changing each
`f i` by a vector in the span of the earlier ones leaves the process unchanged
(`InnerProductSpace.gramSchmidt_eq_of_sub_mem_span`, `InnerProductSpace.gramSchmidt_update_add`).
Likewise each output vector depends only on the inputs up to its index
(`InnerProductSpace.gramSchmidt_congr_Iic`), and the process commutes with restriction to an
initial segment (`InnerProductSpace.gramSchmidt_comp`).

The coefficient `InnerProductSpace.gramSchmidtCoeff 𝕜 f i j = ⟪f*ⱼ, fᵢ⟫ / ‖f*ⱼ‖²`, where
`f*ⱼ = gramSchmidt 𝕜 f j`, gives `fᵢ = f*ᵢ + ∑_{j<i} μᵢⱼ f*ⱼ`
(`InnerProductSpace.gramSchmidt_add_sum_coeff`). This is the matrix `μ` of
[LenstraLenstraLovasz1982], (1.2)–(1.3). The Gram determinant is the product of the squared
lengths of the orthogonalized vectors (`InnerProductSpace.det_gram_eq_prod_norm_gramSchmidt_sq`),
and `‖f*ᵢ‖ ≤ ‖fᵢ‖` (`InnerProductSpace.norm_gramSchmidt_le`). Every nonzero integer combination
of the `fᵢ` is at least as long as some `f*ᵢ`
(`InnerProductSpace.exists_norm_gramSchmidt_le_of_mem_span_int`), which is the first step of the
proof of [LenstraLenstraLovasz1982], (1.11). None of these statements assumes linear independence.

## Main definitions

* `InnerProductSpace.gramSchmidtCoeff`: the Gram–Schmidt coefficient `μᵢⱼ`.

## Main results

* `InnerProductSpace.eq_gramSchmidt_of_sub_mem_of_mem_orthogonal`: the characterization of
  `gramSchmidt 𝕜 f i`.
* `InnerProductSpace.gramSchmidt_eq_of_sub_mem_span`: invariance under unitriangular changes.
* `InnerProductSpace.gramSchmidt_comp`: restriction to an initial segment.
* `InnerProductSpace.det_gram_eq_prod_norm_gramSchmidt_sq`: `det (gram f) = ∏ ‖f*ᵢ‖²`.
* `InnerProductSpace.exists_norm_gramSchmidt_le_of_mem_span_int`: nonzero integer combinations
  are at least as long as some `f*ᵢ`.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

open Finset Submodule Module

namespace InnerProductSpace

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (𝕜) in
/-- `f*ᵢ - fᵢ` lies in the span of the earlier vectors. -/
theorem gramSchmidt_sub_mem_span_Iio (f : ι → E) (i : ι) :
    gramSchmidt 𝕜 f i - f i ∈ span 𝕜 (f '' Set.Iio i) := by
  rw [← span_gramSchmidt_Iio 𝕜 f i, gramSchmidt_def 𝕜 f i, sub_sub_cancel_left]
  refine neg_mem (sum_mem fun j hj => ?_)
  rw [starProjection_singleton]
  exact smul_mem _ _ (subset_span ⟨j, Finset.mem_Iio.1 hj, rfl⟩)

variable (𝕜) in
/-- `f*ᵢ` is orthogonal to the span of the earlier vectors. -/
theorem gramSchmidt_mem_orthogonal_span_Iio (f : ι → E) (i : ι) :
    gramSchmidt 𝕜 f i ∈ (span 𝕜 (f '' Set.Iio i))ᗮ := by
  rw [mem_orthogonal']
  intro u hu
  refine span_induction ?_ (inner_zero_right _) (fun x y _ _ hx hy => ?_)
    (fun a x _ hx => ?_) hu
  · rintro _ ⟨j, hj, rfl⟩
    exact gramSchmidt_inv_triangular 𝕜 f hj
  · rw [inner_add_right, hx, hy, add_zero]
  · rw [inner_smul_right, hx, mul_zero]

/-- `gramSchmidt 𝕜 f i` is the unique vector that differs from `f i` by an element of the span
of the earlier vectors and is orthogonal to that span. -/
theorem eq_gramSchmidt_of_sub_mem_of_mem_orthogonal {f : ι → E} {i : ι} {v : E}
    (hsub : v - f i ∈ span 𝕜 (f '' Set.Iio i)) (horth : v ∈ (span 𝕜 (f '' Set.Iio i))ᗮ) :
    v = gramSchmidt 𝕜 f i := by
  have hK : v - gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iio i) := by
    rw [← sub_sub_sub_cancel_right v (gramSchmidt 𝕜 f i) (f i)]
    exact sub_mem hsub (gramSchmidt_sub_mem_span_Iio 𝕜 f i)
  have hKo := sub_mem horth (gramSchmidt_mem_orthogonal_span_Iio 𝕜 f i)
  exact sub_eq_zero.1 (disjoint_def.1 (orthogonal_disjoint _) _ hK hKo)

/-- Two families whose prefixes before `j` and `i` span the same subspace, and whose vectors
`g j` and `f i` differ by an element of it, have the same Gram–Schmidt vector there. -/
private theorem gramSchmidt_eq_of_span_eq {ι' : Type*} [LinearOrder ι'] [LocallyFiniteOrderBot ι']
    {f : ι → E} {g : ι' → E} {i : ι} {j : ι'}
    (hspan : span 𝕜 (g '' Set.Iio j) = span 𝕜 (f '' Set.Iio i))
    (hsub : g j - f i ∈ span 𝕜 (f '' Set.Iio i)) : gramSchmidt 𝕜 g j = gramSchmidt 𝕜 f i := by
  refine eq_gramSchmidt_of_sub_mem_of_mem_orthogonal ?_ ?_
  · rw [← sub_add_sub_cancel _ (g j)]
    exact add_mem (hspan ▸ gramSchmidt_sub_mem_span_Iio 𝕜 g j) hsub
  · exact hspan ▸ gramSchmidt_mem_orthogonal_span_Iio 𝕜 g j

/-- Changing each vector by an element of the span of the earlier ones does not change the
Gram–Schmidt orthogonalization. -/
theorem gramSchmidt_eq_of_sub_mem_span {f g : ι → E}
    (h : ∀ i, g i - f i ∈ span 𝕜 (f '' Set.Iio i)) : gramSchmidt 𝕜 g = gramSchmidt 𝕜 f := by
  funext i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    -- the outputs before `i` agree, hence so do the spans of the inputs before `i`
    refine gramSchmidt_eq_of_span_eq ?_ (h i)
    rw [← span_gramSchmidt_Iio 𝕜 g, ← span_gramSchmidt_Iio 𝕜 f,
      Set.image_congr (s := Set.Iio i) ih]

variable (𝕜) in
/-- The Gram–Schmidt coefficient `μᵢⱼ = ⟪f*ⱼ, fᵢ⟫ / ‖f*ⱼ‖²` of [LenstraLenstraLovasz1982], (1.2). -/
@[expose] noncomputable def gramSchmidtCoeff (f : ι → E) (i j : ι) : 𝕜 :=
  ⟪gramSchmidt 𝕜 f j, f i⟫ / (‖gramSchmidt 𝕜 f j‖ : 𝕜) ^ 2

/-- `fᵢ = f*ᵢ + ∑_{j<i} μᵢⱼ f*ⱼ`, [LenstraLenstraLovasz1982], (1.3). -/
theorem gramSchmidt_add_sum_coeff (f : ι → E) (i : ι) :
    f i = gramSchmidt 𝕜 f i +
      ∑ j ∈ Iio i, gramSchmidtCoeff 𝕜 f i j • gramSchmidt 𝕜 f j :=
  gramSchmidt_def'' 𝕜 f i

variable (𝕜) in
/-- `⟪f*ᵢ, fᵢ⟫ = ‖f*ᵢ‖²`. -/
theorem inner_gramSchmidt_self_right (f : ι → E) (i : ι) :
    ⟪gramSchmidt 𝕜 f i, f i⟫ = (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2 := by
  have h := gramSchmidt_mem_orthogonal_span_Iio 𝕜 f i
  rw [mem_orthogonal'] at h
  have hsub := h _ (neg_mem (gramSchmidt_sub_mem_span_Iio 𝕜 f i))
  rw [neg_sub, inner_sub_right, sub_eq_zero] at hsub
  rw [hsub, inner_self_eq_norm_sq_to_K]

variable (𝕜) in
/-- The diagonal coefficient `μᵢᵢ` is `1` when `f*ᵢ ≠ 0`. -/
theorem gramSchmidtCoeff_self {f : ι → E} {i : ι} (h : gramSchmidt 𝕜 f i ≠ 0) :
    gramSchmidtCoeff 𝕜 f i i = 1 := by
  rw [gramSchmidtCoeff, inner_gramSchmidt_self_right, div_self]
  simpa using h

variable (𝕜) in
/-- The coefficients above the diagonal vanish: `μⱼₗ = 0` for `j < l`. -/
theorem gramSchmidtCoeff_eq_zero_of_lt (f : ι → E) {j l : ι} (hjl : j < l) :
    gramSchmidtCoeff 𝕜 f j l = 0 := by
  rw [gramSchmidtCoeff, gramSchmidt_inv_triangular 𝕜 f hjl, zero_div]

variable (𝕜) in
/-- Orthogonalization does not increase lengths: `‖f*ᵢ‖ ≤ ‖fᵢ‖`. -/
theorem norm_gramSchmidt_le (f : ι → E) (i : ι) : ‖gramSchmidt 𝕜 f i‖ ≤ ‖f i‖ := by
  -- Cauchy–Schwarz applied to `‖f*ᵢ‖² = ⟪f*ᵢ, fᵢ⟫`
  have hcs := norm_inner_le_norm (𝕜 := 𝕜) (gramSchmidt 𝕜 f i) (f i)
  rw [inner_gramSchmidt_self_right, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at hcs
  rcases (norm_nonneg (gramSchmidt 𝕜 f i)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left hcs hpos

/-- `⟪f*ᵢ, ∑ⱼ cⱼ fⱼ⟫ = cᵢ ‖f*ᵢ‖²` for integer coefficients that vanish above `i`. -/
theorem inner_gramSchmidt_sum_zsmul [Fintype ι] (f : ι → E) (c : ι → ℤ) {i : ι}
    (hc : ∀ j, i < j → c j = 0) :
    ⟪gramSchmidt 𝕜 f i, ∑ j, c j • f j⟫ = (c i : 𝕜) * (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2 := by
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_right, inner_gramSchmidt_self_right]
  · intro j _ hji
    rw [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_right]
    rcases lt_or_gt_of_ne hji with h | h
    · rw [gramSchmidt_inv_triangular 𝕜 f h, mul_zero]
    · rw [hc j h, Int.cast_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- If `x = ∑ cⱼ fⱼ` with integer coefficients whose last nonzero entry is at `i`, then
`‖f*ᵢ‖ ≤ ‖x‖`. -/
theorem norm_gramSchmidt_le_norm_sum_zsmul [Fintype ι] (f : ι → E) (c : ι → ℤ) {i : ι}
    (hci : c i ≠ 0) (hc : ∀ j, i < j → c j = 0) :
    ‖gramSchmidt 𝕜 f i‖ ≤ ‖∑ j, c j • f j‖ := by
  set x := ∑ j, c j • f j with hx
  have hinner : ⟪gramSchmidt 𝕜 f i, x⟫ = (c i : 𝕜) * (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2 :=
    inner_gramSchmidt_sum_zsmul f c hc
  have hcs := norm_inner_le_norm (𝕜 := 𝕜) (gramSchmidt 𝕜 f i) x
  rw [hinner, norm_mul, norm_pow, RCLike.norm_ofReal, abs_norm] at hcs
  have hc1 : (1 : ℝ) ≤ ‖(c i : 𝕜)‖ := by
    rw [← RCLike.ofReal_intCast, RCLike.norm_ofReal]
    exact_mod_cast Int.one_le_abs hci
  rcases eq_or_ne (gramSchmidt 𝕜 f i) 0 with h0 | h0
  · rw [h0, norm_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖gramSchmidt 𝕜 f i‖ := norm_pos_iff.2 h0
    nlinarith [norm_nonneg x]

/-- Every nonzero vector of the integer span of a finite family `f` is at least as long as some
Gram–Schmidt vector `f*ᵢ`. -/
theorem exists_norm_gramSchmidt_le_of_mem_span_int [Finite ι] {f : ι → E} {x : E}
    (hx : x ∈ span ℤ (Set.range f)) (hx0 : x ≠ 0) : ∃ i, ‖gramSchmidt 𝕜 f i‖ ≤ ‖x‖ := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  have hne : (Finset.univ.filter fun j => c j ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hx0 (Finset.sum_eq_zero fun j _ => by rw [not_not.1 (h (Finset.mem_univ j)), zero_smul])
  refine ⟨_, norm_gramSchmidt_le_norm_sum_zsmul f c
    (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2 fun j hij => ?_⟩
  by_contra hcj
  exact absurd (Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hcj⟩))
    (not_le.2 hij)

/-- Gram–Schmidt vectors depend only on the vectors up to their index. -/
theorem gramSchmidt_congr_Iic {f g : ι → E} {i : ι} (h : ∀ j ≤ i, f j = g j) :
    gramSchmidt 𝕜 f i = gramSchmidt 𝕜 g i := by
  have himg : f '' Set.Iio i = g '' Set.Iio i :=
    Set.image_congr fun j hj => h j (le_of_lt hj)
  refine gramSchmidt_eq_of_span_eq (congrArg _ himg) ?_
  rw [h i le_rfl, sub_self]
  exact zero_mem _

/-- Gram–Schmidt commutes with restriction along an order embedding onto an initial segment. -/
theorem gramSchmidt_comp {ι' : Type*} [LinearOrder ι'] [LocallyFiniteOrderBot ι']
    (f : ι → E) {e : ι' → ι} (he : StrictMono e) (hlow : IsLowerSet (Set.range e)) (i : ι') :
    gramSchmidt 𝕜 (f ∘ e) i = gramSchmidt 𝕜 f (e i) := by
  have himg : (f ∘ e) '' Set.Iio i = f '' Set.Iio (e i) := by
    rw [Set.image_comp]
    congr 1
    ext j
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact he hj'
    · intro hj
      obtain ⟨j', rfl⟩ := hlow (le_of_lt hj) ⟨i, rfl⟩
      exact ⟨j', he.lt_iff_lt.1 hj, rfl⟩
  refine gramSchmidt_eq_of_span_eq (congrArg _ himg) ?_
  rw [Function.comp_apply, sub_self]
  exact zero_mem _

/-- The Gram determinant is the product of the squared lengths of the Gram–Schmidt vectors. -/
theorem det_gram_eq_prod_norm_gramSchmidt_sq [Fintype ι] [DecidableEq ι] (f : ι → E) :
    (Matrix.gram 𝕜 f).det = ∏ i, (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2 := by
  let L : Matrix ι ι 𝕜 := Matrix.of fun i j =>
    if j < i then gramSchmidtCoeff 𝕜 f i j else if i = j then 1 else 0
  have hf : ∀ i, f i = ∑ j, L i j • gramSchmidt 𝕜 f j := by
    intro i
    have hsplit : ∀ j, L i j • gramSchmidt 𝕜 f j =
        (if j ∈ Iio i then gramSchmidtCoeff 𝕜 f i j • gramSchmidt 𝕜 f j else 0) +
          (if i = j then gramSchmidt 𝕜 f j else 0) := by
      intro j
      simp only [L, Matrix.of_apply, Finset.mem_Iio]
      split_ifs with h1 h2 <;> simp_all
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [add_comm]
    exact gramSchmidt_add_sum_coeff f i
  have hentry : ∀ i k, ⟪f i, f k⟫ =
      ∑ j, star (L i j) * (‖gramSchmidt 𝕜 f j‖ : 𝕜) ^ 2 * L k j := by
    intro i k
    rw [hf i, hf k, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.star_def]
      ring
    · intro l _ hlj
      rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f hlj.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hG : Matrix.gram 𝕜 f =
      L.map star * Matrix.diagonal (fun j => (‖gramSchmidt 𝕜 f j‖ : 𝕜) ^ 2) * L.transpose := by
    ext i k
    rw [Matrix.gram_apply, hentry, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
  have hL : L.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp only [L, Matrix.of_apply, not_lt.2 (le_of_lt hij'), (ne_of_lt hij'), ↓reduceIte]
  have hLs : (L.map star).IsLowerTriangular := by
    intro i j hij
    rw [Matrix.map_apply, hL hij, star_zero]
  have hdiag : ∀ i, L i i = 1 := fun i => by simp [L]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_of_isLowerTriangular _ hL, Matrix.det_of_isLowerTriangular _ hLs]
  simp only [Matrix.map_apply, hdiag, star_one, Finset.prod_const_one, one_mul, mul_one]

/-- Adding to `f i` a vector in the span of the earlier vectors leaves all Gram–Schmidt vectors
unchanged. -/
theorem gramSchmidt_update_add [DecidableEq ι] (f : ι → E) {i : ι} {v : E}
    (hv : v ∈ span 𝕜 (f '' Set.Iio i)) :
    gramSchmidt 𝕜 (Function.update f i (f i + v)) = gramSchmidt 𝕜 f := by
  refine gramSchmidt_eq_of_sub_mem_span fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self, add_sub_cancel_left]
    exact hv
  · rw [Function.update_of_ne hj, sub_self]
    exact zero_mem _

end InnerProductSpace
