/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, LinearAlgebra/Matrix/Rank)

public import CslibFrontier.Init
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Block ranks and cut ranks

The *block rank* `M.blockRank S T` of a matrix `M` over a field is the rank of its block with rows
in the set `S` and columns in the set `T`: the dimension of the span of the rows of
`M.submatrix (↑) (↑)`. It agrees with `Matrix.rank` of that submatrix (`Matrix.blockRank_eq_rank`)
but needs no `Fintype` instance on the sets.

The *cut rank* `M.cutRank X` of a square matrix is the block rank of the rows in `X` and the
columns outside `X`. For the adjacency matrix of a graph over `𝔽₂` this is the cut rank of `X` in
the graph [Oum][Oum2005]; here it measures how far a quadratic form is from splitting
across the cut. A quadratic form `v ⬝ᵥ Q *ᵥ v` on a vector glued from a part `u` on `X` and a part
`w` off `X` is a form in `u`, plus a form in `w`, plus the pairing `u ⬝ᵥ C *ᵥ w` of the block `C`
of the polar matrix `Q + Qᵀ` with rows `X` and columns off `X`
(`Matrix.dotProduct_mulVec_self_eq_add`). A matrix that carries a block `R` on rows `f` and
columns `g` and vanishes elsewhere (`Matrix.extendBlock`) has the bilinear form of `R` as its
quadratic form (`Matrix.dotProduct_mulVec_self_eq_of_submatrix`).

Block ranks grow with the block, drop by at most one per deleted row, are invariant under
transposition and injective relabelling, and add over blocks whose rows live on disjoint sets of
columns. Cut ranks of a symmetric matrix are symmetric under complementation.

## Main definitions

* `Matrix.blockRank`: the block rank `M.blockRank S T`, the rank of the block of `M` with rows `S`
  and columns `T`.
* `Matrix.cutRank`: the cut rank `M.cutRank X`, the rank of the block of `M` with rows `X` and
  columns `Xᶜ`.
* `Matrix.extendBlock`: the square matrix `extendBlock f g R` carrying `R` on the rows `f` and the
  columns `g`.

## Main results

* `Matrix.blockRank_eq_rank`: block ranks are ranks of submatrices.
* `Matrix.blockRank_mono`, `Matrix.blockRank_le_add_ncard_sdiff`, `Matrix.blockRank_transpose`,
  `Matrix.blockRank_submatrix`, `Matrix.add_blockRank_le_of_disjoint`: the algebra of block ranks.
* `Matrix.cutRank_le_add_ncard_sdiff`, `Matrix.IsSymm.cutRank_compl`: the algebra of cut ranks.
* `Matrix.dotProduct_mulVec_self_eq_add`: a quadratic form across a cut.
* `Matrix.dotProduct_mulVec_self_eq_of_submatrix`: a bilinear form as a quadratic form.

## References

* [S. Oum, *Rank-width and vertex-minors*][Oum2005]
-/

@[expose] public section

namespace Matrix

open Module Set Submodule

variable {m n m' n' ι κ κ' K : Type*} [Field K]

/-- The rank of the block of `M` with rows in `S` and columns in `T`: the dimension of the span of
the rows of the block. It equals `Matrix.rank` of the submatrix (`Matrix.blockRank_eq_rank`) but
needs no `Fintype` instance on `T`. -/
noncomputable def blockRank (M : Matrix m n K) (S : Set m) (T : Set n) : ℕ :=
  finrank K (span K (range (M.submatrix ((↑) : S → m) ((↑) : T → n)).row))

/-- The *cut rank* of a square matrix `M` at a set `X` of indices: the rank of the block of `M` with
rows in `X` and columns outside `X`. -/
noncomputable def cutRank (M : Matrix ι ι K) (X : Set ι) : ℕ :=
  M.blockRank X Xᶜ

section BlockRank

variable (M : Matrix m n K)

/-- Block ranks are ranks of submatrices. -/
theorem blockRank_eq_rank [Finite m] (S : Set m) (T : Set n) [Fintype T] :
    M.blockRank S T = (M.submatrix ((↑) : S → m) ((↑) : T → n)).rank :=
  (rank_eq_finrank_span_row _).symm

/-- Restricting the columns of a block maps its row space onto the row space of the smaller
block. -/
theorem span_range_row_submatrix_eq_map (S : Set m) {T T' : Set n} (h : T' ⊆ T) :
    span K (range (M.submatrix ((↑) : S → m) ((↑) : T' → n)).row) =
      (span K (range (M.submatrix ((↑) : S → m) ((↑) : T → n)).row)).map
        (LinearMap.funLeft K K (inclusion h)) := by
  rw [Submodule.map_span, ← range_comp]
  rfl

/-- Deleting columns does not increase the rank of a block. -/
theorem blockRank_mono_right [Finite n] (S : Set m) {T T' : Set n} (h : T' ⊆ T) :
    M.blockRank S T' ≤ M.blockRank S T := by
  rw [blockRank, blockRank, M.span_range_row_submatrix_eq_map S h]
  exact Submodule.finrank_map_le _ _

/-- Deleting rows does not increase the rank of a block. -/
theorem blockRank_mono_left [Finite n] {S S' : Set m} (T : Set n) (h : S' ⊆ S) :
    M.blockRank S' T ≤ M.blockRank S T := by
  refine Submodule.finrank_mono (span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, h i.2⟩, rfl⟩

/-- A sub-block has at most the rank of the block. -/
theorem blockRank_mono [Finite n] {S S' : Set m} {T T' : Set n} (hS : S' ⊆ S) (hT : T' ⊆ T) :
    M.blockRank S' T' ≤ M.blockRank S T :=
  (M.blockRank_mono_right S' hT).trans (M.blockRank_mono_left T hS)

/-- The rank of a block is at most the number of its rows. -/
theorem blockRank_le_ncard [Finite m] (S : Set m) (T : Set n) : M.blockRank S T ≤ S.ncard := by
  have := Fintype.ofFinite S
  calc M.blockRank S T ≤ Fintype.card S := finrank_range_le_card _
    _ = S.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- Deleting the rows outside `S'` lowers the rank of a block by at most their number. -/
theorem blockRank_le_add_ncard_sdiff [Finite m] [Finite n] {S S' : Set m} (T : Set n)
    (h : S' ⊆ S) : M.blockRank S T ≤ M.blockRank S' T + (S \ S').ncard := by
  have hrange : range (M.submatrix ((↑) : S → m) ((↑) : T → n)).row =
      range (M.submatrix ((↑) : S' → m) ((↑) : T → n)).row ∪
        range (M.submatrix ((↑) : ↥(S \ S') → m) ((↑) : T → n)).row := by
    ext v
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      by_cases hi' : i ∈ S'
      · exact Or.inl ⟨⟨i, hi'⟩, rfl⟩
      · exact Or.inr ⟨⟨i, hi, hi'⟩, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨⟨i, h i.2⟩, rfl⟩
      · exact ⟨⟨i, i.2.1⟩, rfl⟩
  have h₁ := Submodule.finrank_add_le_finrank_add_finrank
    (span K (range (M.submatrix ((↑) : S' → m) ((↑) : T → n)).row))
    (span K (range (M.submatrix ((↑) : ↥(S \ S') → m) ((↑) : T → n)).row))
  have h₂ := M.blockRank_le_ncard (S \ S') T
  rw [blockRank] at h₂ ⊢
  rw [blockRank, hrange, span_union]
  omega

/-- Blocks that agree entrywise have the same rank. -/
theorem blockRank_congr {M M' : Matrix m n K} {S : Set m} {T : Set n}
    (h : ∀ i ∈ S, ∀ j ∈ T, M i j = M' i j) : M.blockRank S T = M'.blockRank S T := by
  have : M.submatrix ((↑) : S → m) ((↑) : T → n) = M'.submatrix (↑) (↑) :=
    Matrix.ext fun i j => h i i.2 j j.2
  rw [blockRank, blockRank, this]

/-- Row rank equals column rank: transposing a matrix transposes its blocks. -/
theorem blockRank_transpose [Finite m] [Finite n] (S : Set m) (T : Set n) :
    Mᵀ.blockRank T S = M.blockRank S T := by
  have := Fintype.ofFinite S
  have := Fintype.ofFinite T
  rw [blockRank_eq_rank, blockRank_eq_rank, ← transpose_submatrix, rank_transpose]

/-- Relabelling the rows and columns injectively does not change the rank of a block. -/
theorem blockRank_submatrix {f : m' → m} {g : n' → n} (hf : Function.Injective f)
    (hg : Function.Injective g) (S : Set m') (T : Set n') :
    (M.submatrix f g).blockRank S T = M.blockRank (f '' S) (g '' T) := by
  let eS := Equiv.Set.image f S hf
  let eT := Equiv.Set.image g T hg
  let L := LinearEquiv.funCongrLeft K K eT
  have hrange : range ((M.submatrix f g).submatrix ((↑) : S → m') ((↑) : T → n')).row =
      (L : (↥(g '' T) → K) →ₗ[K] (T → K)) ''
        range (M.submatrix ((↑) : ↥(f '' S) → m) ((↑) : ↥(g '' T) → n)).row := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨eS i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i', rfl⟩, rfl⟩
      refine ⟨eS.symm i', funext fun j => ?_⟩
      change M (f (eS.symm i')) (g j) = M i' (eT j)
      rw [show f (eS.symm i') = i' from congrArg Subtype.val (eS.apply_symm_apply i')]
      rfl
  rw [blockRank, blockRank, hrange, span_image]
  exact L.finrank_map_eq _

/-- **Blocks on disjoint columns.** If, among the columns `T`, the rows of `S₁` vanish outside
`T₁` and the rows of `S₂` vanish outside `T₂`, where `T₁` and `T₂` are disjoint, then the ranks of
the blocks `S₁ × T` and `S₂ × T` add up to at most the rank of the block `S × T`. -/
theorem add_blockRank_le_of_disjoint [Finite n] {S S₁ S₂ : Set m} {T T₁ T₂ : Set n}
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (hT : Disjoint T₁ T₂)
    (hM₁ : ∀ i ∈ S₁, ∀ j ∈ T, j ∉ T₁ → M i j = 0)
    (hM₂ : ∀ i ∈ S₂, ∀ j ∈ T, j ∉ T₂ → M i j = 0) :
    M.blockRank S₁ T + M.blockRank S₂ T ≤ M.blockRank S T := by
  set V₁ := span K (range (M.submatrix ((↑) : S₁ → m) ((↑) : T → n)).row)
  set V₂ := span K (range (M.submatrix ((↑) : S₂ → m) ((↑) : T → n)).row)
  -- The rows of a block vanishing off `B` span vectors vanishing off `B`.
  have hsupp (A : Set m) (B : Set n) (hM : ∀ i ∈ A, ∀ j ∈ T, j ∉ B → M i j = 0) :
      ∀ v ∈ span K (range (M.submatrix ((↑) : A → m) ((↑) : T → n)).row), ∀ j : T,
        (j : n) ∉ B → v j = 0 := by
    intro v hv j hj
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hM i i.2 j j.2 hj
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hinf : V₁ ⊓ V₂ = ⊥ := by
    refine eq_bot_iff.mpr fun v ⟨hv₁, hv₂⟩ => (Submodule.mem_bot K).mpr (funext fun j => ?_)
    by_cases hj : (j : n) ∈ T₁
    · exact hsupp S₂ T₂ hM₂ v hv₂ j fun hj' => hT.ne_of_mem hj hj' rfl
    · exact hsupp S₁ T₁ hM₁ v hv₁ j hj
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hinf, finrank_bot, add_zero] at hsum
  rw [blockRank, blockRank, ← hsum]
  refine Submodule.finrank_mono (sup_le (span_mono ?_) (span_mono ?_))
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, h₁ i.2⟩, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, h₂ i.2⟩, rfl⟩

end BlockRank

section CutRank

variable (M : Matrix ι ι K)

/-- Cut ranks are ranks of submatrices. -/
theorem cutRank_eq_rank [Finite ι] (X : Set ι) [Fintype ↥Xᶜ] :
    M.cutRank X = (M.submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι)).rank :=
  M.blockRank_eq_rank X Xᶜ

/-- Passing from `X` to a subset `D` lowers the cut rank by at most `|X \ D|`. -/
theorem cutRank_le_add_ncard_sdiff [Finite ι] {D X : Set ι} (h : D ⊆ X) :
    M.cutRank X ≤ M.cutRank D + (X \ D).ncard :=
  (M.blockRank_le_add_ncard_sdiff _ h).trans
    (Nat.add_le_add_right (M.blockRank_mono_right D (compl_subset_compl.mpr h)) _)

/-- Passing from `X` to a subset `D` lowers the cut rank by at most `|X| - |D|`:
`|D| + ρ(X) ≤ ρ(D) + |X|`. -/
theorem ncard_add_cutRank_le_of_subset [Finite ι] {D X : Set ι} (h : D ⊆ X) :
    D.ncard + M.cutRank X ≤ M.cutRank D + X.ncard := by
  have h₁ := M.cutRank_le_add_ncard_sdiff h
  have h₂ := ncard_sdiff_add_ncard_of_subset h
  omega

/-- The cut rank of the transpose at the complement is the cut rank. -/
theorem cutRank_transpose_compl [Finite ι] (X : Set ι) : Mᵀ.cutRank Xᶜ = M.cutRank X := by
  rw [cutRank, cutRank, compl_compl, blockRank_transpose]

/-- The cut rank of a symmetric matrix is symmetric under complementation. -/
theorem IsSymm.cutRank_compl [Finite ι] {M : Matrix ι ι K} (hM : M.IsSymm) (X : Set ι) :
    M.cutRank Xᶜ = M.cutRank X := by
  conv_lhs => rw [← hM.eq]
  exact M.cutRank_transpose_compl X

/-- The cut rank is at most the size of the set. -/
theorem cutRank_le_ncard [Finite ι] (X : Set ι) : M.cutRank X ≤ X.ncard :=
  M.blockRank_le_ncard X Xᶜ

end CutRank

/-! ### Quadratic forms across a cut -/

/-- **A quadratic form across a cut.** For a set `X` of indices, the quadratic form
`v ⬝ᵥ Q *ᵥ v` is the form of the block `Q` on `X × X` at the part of `v` on `X`, plus the form of
the block on `Xᶜ × Xᶜ` at the part of `v` off `X`, plus the pairing of the two parts through the
block of the polar matrix `Q + Qᵀ` with rows `X` and columns `Xᶜ`. -/
theorem dotProduct_mulVec_self_eq_add {R : Type*} [CommRing R] [Fintype ι] (Q : Matrix ι ι R)
    (X : Set ι) [DecidablePred (· ∈ X)] (v : ι → R) :
    v ⬝ᵥ Q *ᵥ v =
      X.domRestrict v ⬝ᵥ Q.submatrix ((↑) : X → ι) ((↑) : X → ι) *ᵥ X.domRestrict v +
        Xᶜ.domRestrict v ⬝ᵥ Q.submatrix ((↑) : ↥Xᶜ → ι) ((↑) : ↥Xᶜ → ι) *ᵥ Xᶜ.domRestrict v +
          X.domRestrict v ⬝ᵥ (Q + Qᵀ).submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι) *ᵥ
            Xᶜ.domRestrict v := by
  -- Split every sum over `ι` into the indices in `X` and those outside.
  have hsplit (f : ι → R) : ∑ i, f i = ∑ i : X, f i + ∑ i : ↥Xᶜ, f i :=
    (Fintype.sum_subtype_add_sum_subtype (· ∈ X) f).symm
  have hL : v ⬝ᵥ Q *ᵥ v = ∑ i, ∑ j, v i * Q i j * v j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  -- The transposed half of the polar block is the sum from outside `X` into `X`.
  have hswap : ∑ i : X, ∑ j : ↥Xᶜ, v i * Q j i * v j =
      ∑ j : ↥Xᶜ, ∑ i : X, v j * Q j i * v i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hL]
  simp only [hsplit, Finset.sum_add_distrib]
  simp only [dotProduct, mulVec, submatrix_apply, Matrix.add_apply, transpose_apply,
    Set.domRestrict_apply, Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib, ← mul_assoc]
  rw [hswap]
  ring

/-- The square matrix that carries `R` on the rows `f` and the columns `g`, and vanishes
elsewhere. For injective `f` and `g` its quadratic form is the bilinear form of `R`
(`Matrix.dotProduct_mulVec_self_eq_of_submatrix`). -/
noncomputable def extendBlock {α : Type*} [Zero α] (f : κ → ι) (g : κ' → ι)
    (R : Matrix κ κ' α) : Matrix ι ι α :=
  Matrix.of (Function.extend f (fun a => Function.extend g (R a) 0) 0)

section ExtendBlock

variable {α : Type*} [Zero α] {f : κ → ι} {g : κ' → ι}

/-- For injective `f` and `g`, the entry of `extendBlock f g R` at `(f a, g b)` is `R a b`. -/
theorem extendBlock_apply_apply (hf : Function.Injective f) (hg : Function.Injective g)
    (R : Matrix κ κ' α) (a : κ) (b : κ') : extendBlock f g R (f a) (g b) = R a b := by
  simp only [extendBlock, of_apply, hf.extend_apply, hg.extend_apply]

/-- For injective `f` and `g`, the block of `extendBlock f g R` on the rows `f` and the columns
`g` is `R`. -/
theorem submatrix_extendBlock (hf : Function.Injective f) (hg : Function.Injective g)
    (R : Matrix κ κ' α) : (extendBlock f g R).submatrix f g = R :=
  Matrix.ext fun a b => extendBlock_apply_apply hf hg R a b

/-- `extendBlock f g R` vanishes at `(i, j)` when `i` is not in the range of `f` or `j` is not in
the range of `g`. -/
theorem extendBlock_eq_zero (R : Matrix κ κ' α) {i j : ι} (h : i ∉ Set.range f ∨ j ∉ Set.range g) :
    extendBlock f g R i j = 0 := by
  classical
  simp only [extendBlock, of_apply]
  rcases h with h | h
  · rw [Function.extend_apply' _ _ _ h]
    rfl
  · by_cases hi : ∃ a, f a = i
    · rw [Function.extend_def, dite_eq_left hi, Function.extend_apply' _ _ _ h]
      rfl
    · rw [Function.extend_apply' _ _ _ hi]
      rfl

end ExtendBlock

/-- **A bilinear form as a quadratic form.** If `M` carries `R` on the rows `f` and the columns `g`
and vanishes elsewhere, the quadratic form of `M` at `v` is the bilinear form of `R` at the parts
`v ∘ f` and `v ∘ g`. -/
theorem dotProduct_mulVec_self_eq_of_submatrix {S : Type*} [CommSemiring S] [Fintype ι]
    [Fintype κ] [Fintype κ'] {R : Matrix κ κ' S} {M : Matrix ι ι S} {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hMR : M.submatrix f g = R)
    (hM : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range g → M i j = 0) (v : ι → S) :
    v ⬝ᵥ M *ᵥ v = (v ∘ f) ⬝ᵥ R *ᵥ (v ∘ g) := by
  simp only [dotProduct, mulVec, Function.comp_apply]
  symm
  refine Fintype.sum_of_injective f hf _ _ (fun i hi => ?_) fun a => ?_
  · simp [hM i _ (Or.inl hi)]
  · congr 1
    refine Fintype.sum_of_injective g hg _ _ (fun j hj => by simp [hM _ j (Or.inr hj)])
      fun b => ?_
    rw [← hMR, submatrix_apply]

end Matrix
