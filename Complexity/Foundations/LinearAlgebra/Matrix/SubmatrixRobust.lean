/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.CutRank
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Submatrix-robust matrices

A matrix is *submatrix-robust* with deficiency `t` (`Matrix.SubmatrixRobust`) when every square
block of it, with `k` rows and `k` columns, has rank at least `k - t`; then every block has rank
at least its smaller side minus `t` (`Matrix.SubmatrixRobust.min_le`).

**Existence by counting** (`Matrix.exists_submatrixRobust`). A square block of an `m × m` matrix
over `𝔽₂` with `k` rows and rank `r` has `r` columns spanning all of its columns. So the matrix is
determined by those columns, the coefficients expressing each other column of the block in terms
of them, and its entries outside the remaining `k × (k - r)` block. Counting these descriptions, at
most `2 ^ (m² - (k - r)²)` matrices are deficient by `k - r` on given sets of rows and columns with
a given spanning set. A union bound over the fewer than `2 ^ (3 m)` choices shows that some matrix
has every square block of rank at least `k - t` once `(t + 1)² > 3 m`. The deficiency
`t = 2 ⌊√m⌋ + 1` qualifies.

**Cut ranks of bilinear forms** (`Matrix.SubmatrixRobust.le_cutRank_add`). Place a robust `k × k`
matrix `R` on a block of a square matrix `M` whose rows and columns are disjoint sets of indices,
with zeros elsewhere, so that the quadratic form of `M` is a bilinear form `xᵀ R y`. A set `U` of
indices cuts the rows of `R` into `x ∩ U` and `x \ U`, and its columns likewise; the block of the
polar matrix `M + Mᵀ` with rows `U` and columns `Uᶜ` contains, on disjoint sets of columns, the
block of `R` with rows `x ∩ U` and columns `y \ U` and the transpose of the block with rows `x \ U`
and columns `y ∩ U` (`Matrix.add_blockRank_le_cutRank_add_transpose`). If there are at most
`2 k + 1` indices and `|U| = k`, the two blocks have total rank at least `k - 1 - 2 t`.

## Main definitions

* `Matrix.SubmatrixRobust M t`: every square block of `M` with `k` rows has rank at least `k - t`.

## Main results

* `Matrix.SubmatrixRobust.min_le`: every block of a robust matrix has nearly full rank.
* `Matrix.exists_submatrixRobust_of_lt`, `Matrix.exists_submatrixRobust`: robust matrices over
  `𝔽₂` exist, by counting.
* `Matrix.add_blockRank_le_cutRank_add_transpose`: the cut rank of a bilinear form.
* `Matrix.SubmatrixRobust.le_cutRank_add`: bisections of a robust bilinear form have nearly full
  cut rank.
-/

@[expose] public section

namespace Matrix

variable {m n ι κ κ' K : Type*} [Field K]

/-- `M` is *submatrix-robust* with deficiency `t`: every square block of `M`, with `k` rows and `k`
columns, has rank at least `k - t`. -/
def SubmatrixRobust (M : Matrix m n K) (t : ℕ) : Prop :=
  ∀ (S : Set m) (T : Set n), S.ncard = T.ncard → S.ncard ≤ M.blockRank S T + t

/-- A larger deficiency is weaker. -/
theorem SubmatrixRobust.mono {M : Matrix m n K} {t t' : ℕ} (hM : M.SubmatrixRobust t)
    (ht : t ≤ t') : M.SubmatrixRobust t' :=
  fun S T h => (hM S T h).trans (Nat.add_le_add_left ht _)

/-- Every block of a robust matrix has rank at least its smaller side minus the deficiency. -/
theorem SubmatrixRobust.min_le [Finite n] {M : Matrix m n K} {t : ℕ} (hM : M.SubmatrixRobust t)
    (S : Set m) (T : Set n) : min S.ncard T.ncard ≤ M.blockRank S T + t := by
  obtain ⟨S', hS', hS'c⟩ := Set.exists_subset_card_eq (min_le_left S.ncard T.ncard)
  obtain ⟨T', hT', hT'c⟩ := Set.exists_subset_card_eq (min_le_right S.ncard T.ncard)
  have h := hM S' T' (hS'c.trans hT'c.symm)
  rw [hS'c] at h
  exact h.trans (Nat.add_le_add_right (M.blockRank_mono hS' hT') t)

/-! ### Existence by counting -/

section Counting

open Finset

variable {k : ℕ}

/-- The column `j` of `R`, restricted to the rows `S`. -/
private def colVec (R : Matrix (Fin k) (Fin k) (ZMod 2)) (S : Set (Fin k)) (j : Fin k) :
    S → ZMod 2 :=
  fun i => R i j

/-- **Column bases.** The columns of a block contain a spanning set as large as the rank of the
block. -/
private theorem exists_spanning_columns (R : Matrix (Fin k) (Fin k) (ZMod 2))
    (S T : Finset (Fin k)) :
    ∃ T' ⊆ T, #T' = R.blockRank ↑S ↑T ∧
      ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') := by
  classical
  let v : (↑T : Set (Fin k)) → (↑S : Set (Fin k)) → ZMod 2 := fun j => colVec R ↑S j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.image fun x => (a x : Fin k), ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨x, -, rfl⟩ := mem_image.mp hj
    exact (a x).2
  · rw [show (fun x => (a x : Fin k)) = Subtype.val ∘ a from rfl,
      card_image_of_injective _ (Subtype.val_injective.comp ha), card_univ,
      ← finrank_span_eq_card hli, hspan, ← blockRank_transpose]
    rfl
  · have hrange :
        Set.range (v ∘ a) = colVec R ↑S '' ↑(Finset.univ.image fun x => (a x : Fin k)) := by
      ext y
      simp only [Set.mem_range, Function.comp_apply, coe_image, coe_univ, Set.image_univ,
        Set.mem_image, v]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨a x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    intro j hj
    rw [← hrange, hspan]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

open Classical in
/-- The matrices whose columns in `T`, restricted to the rows `S`, lie in the span of their
columns in `T'`. -/
private noncomputable def spannedBy (S T T' : Finset (Fin k)) :
    Finset (Matrix (Fin k) (Fin k) (ZMod 2)) :=
  {R | ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')}

open Classical in
/-- Coefficients expressing a column in terms of the columns in `T'`, chosen once and for all. -/
private noncomputable def spanCoeff (R : Matrix (Fin k) (Fin k) (ZMod 2)) (S T' : Finset (Fin k))
    (j : Fin k) : T' → ZMod 2 :=
  if h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') then
    Classical.choose ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)
  else 0

private theorem spanCoeff_spec {R : Matrix (Fin k) (Fin k) (ZMod 2)} {S T' : Finset (Fin k)}
    {j : Fin k} (h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')) :
    ∑ l, spanCoeff R S T' j l • colVec R ↑S l = colVec R ↑S j := by
  unfold spanCoeff
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)

/-- The complement of `S ×ˢ D` in `Fin k × Fin k` has `k * k - #S * #D` elements. -/
private theorem card_compl_product_add (S D : Finset (Fin k)) :
    #((S ×ˢ D)ᶜ : Finset (Fin k × Fin k)) + #S * #D = k * k := by
  rw [card_compl, card_product, Fintype.card_prod, Fintype.card_fin]
  have : #S * #D ≤ k * k :=
    Nat.mul_le_mul (card_le_univ S |>.trans (by simp)) (card_le_univ D |>.trans (by simp))
  omega

/-- **Counting spanned matrices.** A matrix in `spannedBy S T T'` is determined by the
coefficients of its columns in `T \ T'` and by its entries outside `S × (T \ T')`. -/
private theorem card_spannedBy_mul_le (S T T' : Finset (Fin k)) :
    #(spannedBy S T T') * 2 ^ (#S * #(T \ T')) ≤ 2 ^ (#(T \ T') * #T') * 2 ^ (k * k) := by
  classical
  set D := T \ T'
  set Z : Finset (Fin k × Fin k) := (S ×ˢ D)ᶜ
  let Φ : Matrix (Fin k) (Fin k) (ZMod 2) → (D → T' → ZMod 2) × (Z → ZMod 2) :=
    fun R => (fun j => spanCoeff R S T' j, fun p => R p.1.1 p.1.2)
  have hinj : Set.InjOn Φ (spannedBy S T T') := by
    intro R hR R' hR' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨hc, hz⟩ := h
    have hR := (mem_filter.mp hR).2
    have hR' := (mem_filter.mp hR').2
    funext i j
    by_cases hij : (i, j) ∈ Z
    · exact congrFun hz ⟨(i, j), hij⟩
    · have hij' : i ∈ S ∧ j ∈ D := by simpa [Z] using hij
      have hjT : j ∈ T := (mem_sdiff.mp hij'.2).1
      have e1 := congrFun (spanCoeff_spec (hR j hjT)) ⟨i, hij'.1⟩
      have e2 := congrFun (spanCoeff_spec (hR' j hjT)) ⟨i, hij'.1⟩
      have hcj : spanCoeff R S T' j = spanCoeff R' S T' j := congrFun hc ⟨j, hij'.2⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colVec] at e1 e2
      rw [← e1, ← e2, hcj]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      have hlZ : (i, (l : Fin k)) ∈ Z := by
        simp only [Z, Finset.mem_compl, mem_product, not_and]
        intro _ hl
        exact (mem_sdiff.mp hl).2 l.2
      exact congrFun hz ⟨(i, l), hlZ⟩
  have hcard := card_le_card_of_injOn Φ (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at hcard
  calc #(spannedBy S T T') * 2 ^ (#S * #D)
      ≤ (2 ^ #T') ^ #D * 2 ^ #Z * 2 ^ (#S * #D) := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (#D * #T') * 2 ^ (k * k) := by
        rw [mul_assoc, ← pow_add, card_compl_product_add S D, ← pow_mul, mul_comm #T']

open Classical in
/-- The matrices with a deficient square block on the rows `S` and the columns `T`. -/
private noncomputable def deficientOn (t : ℕ) (S T : Finset (Fin k)) :
    Finset (Matrix (Fin k) (Fin k) (ZMod 2)) :=
  {R | #S = #T ∧ R.blockRank ↑S ↑T + t < #S}

/-- When `T' ⊆ T`, `#T' + t < #S`, and `#S = #T`, at most a `2 ^ -((t + 1) ^ 2)` fraction of
`k × k` matrices belong to `spannedBy S T T'`. -/
private theorem card_spannedBy_mul_two_pow_sq_le {t : ℕ} {S T T' : Finset (Fin k)}
    (hT'T : T' ⊆ T) (hlt : #T' + t < #S) (hST : #S = #T) :
    #(spannedBy S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (k * k) := by
  have hsplit := card_sdiff_add_card_eq_card hT'T
  set d := #(T \ T')
  have hd : t + 1 ≤ d := by omega
  have H := card_spannedBy_mul_le S T T'
  rw [hST, ← hsplit] at H
  have hpow : 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (d * d) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have key : #(spannedBy S T T') * 2 ^ (d * d) * 2 ^ (d * #T') ≤
      2 ^ (k * k) * 2 ^ (d * #T') := by
    calc #(spannedBy S T T') * 2 ^ (d * d) * 2 ^ (d * #T')
        = #(spannedBy S T T') * 2 ^ ((d + #T') * d) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
      _ ≤ 2 ^ (d * #T') * 2 ^ (k * k) := H
      _ = _ := mul_comm _ _
  calc #(spannedBy S T T') * 2 ^ ((t + 1) ^ 2)
      ≤ #(spannedBy S T T') * 2 ^ (d * d) := Nat.mul_le_mul_left _ hpow
    _ ≤ _ := Nat.le_of_mul_le_mul_right key (by positivity)

/-- Each block is deficient for at most a `2 ^ (k - (t + 1)²)` fraction of all matrices. -/
private theorem card_deficientOn_mul_le (t : ℕ) (S T : Finset (Fin k)) :
    #(deficientOn t S T) * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ k * 2 ^ (k * k) := by
  classical
  let 𝒯 := T.powerset.filter fun T' => #T' + t < #S ∧ #S = #T
  have hsub : deficientOn t S T ⊆ 𝒯.biUnion fun T' => spannedBy S T T' := by
    intro R hR
    obtain ⟨hST, hdef⟩ := (mem_filter.mp hR).2
    obtain ⟨T', hT', hcard, hspan⟩ := exists_spanning_columns R S T
    refine mem_biUnion.mpr ⟨T', mem_filter.mpr ⟨mem_powerset.mpr hT', by omega, hST⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, hspan⟩
  have hone : ∀ T' ∈ 𝒯, #(spannedBy S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (k * k) := fun T' hT' => by
    obtain ⟨hT'T, hlt, hST⟩ := mem_filter.mp hT'
    exact card_spannedBy_mul_two_pow_sq_le (mem_powerset.mp hT'T) hlt hST
  have h𝒯 : #𝒯 ≤ 2 ^ k := by
    calc #𝒯 ≤ #T.powerset := card_filter_le _ _
      _ = 2 ^ #T := card_powerset T
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (card_le_univ T |>.trans (by simp))
  calc #(deficientOn t S T) * 2 ^ ((t + 1) ^ 2)
      ≤ (∑ T' ∈ 𝒯, #(spannedBy S T T')) * 2 ^ ((t + 1) ^ 2) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ T' ∈ 𝒯, #(spannedBy S T T') * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
    _ ≤ ∑ _T' ∈ 𝒯, 2 ^ (k * k) := Finset.sum_le_sum hone
    _ = #𝒯 * 2 ^ (k * k) := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ k * 2 ^ (k * k) := Nat.mul_le_mul_right _ h𝒯

/-- **Robust matrices exist, by counting.** If `3 k < (t + 1)²`, some `k × k` matrix over `𝔽₂` is
submatrix-robust with deficiency `t`. -/
theorem exists_submatrixRobust_of_lt {t : ℕ} (ht : 3 * k < (t + 1) ^ 2) :
    ∃ R : Matrix (Fin k) (Fin k) (ZMod 2), R.SubmatrixRobust t := by
  classical
  let bad := (univ ×ˢ univ : Finset (Finset (Fin k) × Finset (Fin k))).biUnion
    fun p => deficientOn t p.1 p.2
  have hbad : #bad * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ (k * k)) := by
    calc #bad * 2 ^ ((t + 1) ^ 2)
        ≤ (∑ p ∈ (univ ×ˢ univ : Finset (Finset (Fin k) × Finset (Fin k))),
            #(deficientOn t p.1 p.2)) * 2 ^ ((t + 1) ^ 2) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p ∈ (univ ×ˢ univ : Finset (Finset (Fin k) × Finset (Fin k))),
            #(deficientOn t p.1 p.2) * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
      _ ≤ ∑ _p ∈ (univ ×ˢ univ : Finset (Finset (Fin k) × Finset (Fin k))),
            2 ^ k * 2 ^ (k * k) :=
          Finset.sum_le_sum fun p _ => card_deficientOn_mul_le t p.1 p.2
      _ = 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ (k * k)) := by
          rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_finset,
            Fintype.card_fin]
  have hlt : #bad < Fintype.card (Matrix (Fin k) (Fin k) (ZMod 2)) := by
    rw [Fintype.card_congr Matrix.of.symm, Fintype.card_fun, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, ← pow_mul]
    by_contra hge
    push Not at hge
    have h1 : 2 ^ (k * k) * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ (k * k)) :=
      (Nat.mul_le_mul_right _ hge).trans hbad
    have h2 : 2 ^ k * 2 ^ k * (2 ^ k * 2 ^ (k * k)) < 2 ^ (k * k) * 2 ^ ((t + 1) ^ 2) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨R, -, hR⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨R, fun S T hST => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hR
  refine mem_biUnion.mpr ⟨(S.toFinset, T.toFinset), mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
  refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
    exact hST
  · simp only [Set.coe_toFinset]
    rw [← Set.ncard_eq_toFinset_card']
    exact hcon

/-- **Robust matrices exist.** For every `k`, some `k × k` matrix over `𝔽₂` has every square block
with `j` rows of rank at least `j - (2 ⌊√k⌋ + 1)`. -/
theorem exists_submatrixRobust (k : ℕ) :
    ∃ R : Matrix (Fin k) (Fin k) (ZMod 2), R.SubmatrixRobust (2 * Nat.sqrt k + 1) := by
  refine exists_submatrixRobust_of_lt ?_
  have h := Nat.lt_succ_sqrt' k
  have : (2 * Nat.sqrt k + 1 + 1) ^ 2 = 4 * (Nat.sqrt k + 1) ^ 2 := by ring
  rw [this]
  rw [Nat.succ_eq_add_one] at h
  omega

end Counting

/-! ### Cut ranks of bilinear forms -/

section Bilinear

open Set

/-- **The cut rank of a bilinear form.** Let `f` and `g` place the rows and the columns of `R`
injectively among the indices of a square matrix `M`, with disjoint ranges, and let `M` carry `R`
on that block and vanish elsewhere. Then at every set `U` of indices, the cut rank of the polar
matrix `M + Mᵀ` is at least the rank of the block of `R` with rows `f⁻¹ U` and columns `g⁻¹ Uᶜ`
plus the rank of the block with rows `f⁻¹ Uᶜ` and columns `g⁻¹ U`. -/
theorem add_blockRank_le_cutRank_add_transpose [Finite ι]
    {R : Matrix κ κ' K} {M : Matrix ι ι K} {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : Disjoint (range f) (range g))
    (hMR : M.submatrix f g = R) (hM : ∀ i j, i ∉ range f ∨ j ∉ range g → M i j = 0)
    (U : Set ι) :
    R.blockRank (f ⁻¹' U) (g ⁻¹' Uᶜ) + R.blockRank (f ⁻¹' Uᶜ) (g ⁻¹' U) ≤
      (M + Mᵀ).cutRank U := by
  set X := range f
  set Y := range g
  have hMX (i j : ι) (h : i ∉ X) : M i j = 0 := hM i j (Or.inl h)
  have hMY (i j : ι) (h : j ∉ Y) : M i j = 0 := hM i j (Or.inr h)
  have hnotY : ∀ i ∈ X, i ∉ Y := fun i hi hi' => hfg.ne_of_mem hi hi' rfl
  have hnotX : ∀ i ∈ Y, i ∉ X := fun i hi hi' => hfg.ne_of_mem hi' hi rfl
  -- The two blocks of the polar matrix live on the disjoint columns `Y \ U` and `X \ U`.
  have hsum := (M + Mᵀ).add_blockRank_le_of_disjoint (S := U) (T := Uᶜ) (S₁ := U ∩ X)
    (S₂ := U ∩ Y) (T₁ := Uᶜ ∩ Y) (T₂ := Uᶜ ∩ X) inter_subset_left inter_subset_left
    (hfg.symm.mono inter_subset_right inter_subset_right)
    (fun i hi j hj hj' => by
      have hjY : j ∉ Y := fun h => hj' ⟨hj, h⟩
      simp only [Matrix.add_apply, transpose_apply, hMY i j hjY, hMY j i (hnotY i hi.2), add_zero])
    (fun i hi j hj hj' => by
      have hjX : j ∉ X := fun h => hj' ⟨hj, h⟩
      simp only [Matrix.add_apply, transpose_apply, hMX i j (hnotX i hi.2), hMX j i hjX, add_zero])
  have hb₁ : R.blockRank (f ⁻¹' U) (g ⁻¹' Uᶜ) ≤ (M + Mᵀ).blockRank (U ∩ X) Uᶜ := by
    calc R.blockRank (f ⁻¹' U) (g ⁻¹' Uᶜ)
        = M.blockRank (U ∩ X) (Uᶜ ∩ Y) := by
          rw [← hMR, M.blockRank_submatrix hf hg, image_preimage_eq_inter_range,
            image_preimage_eq_inter_range]
      _ = (M + Mᵀ).blockRank (U ∩ X) (Uᶜ ∩ Y) := blockRank_congr fun i hi j _ => by
            simp only [Matrix.add_apply, transpose_apply, hMY j i (hnotY i hi.2), add_zero]
      _ ≤ (M + Mᵀ).blockRank (U ∩ X) Uᶜ := blockRank_mono_right _ _ inter_subset_left
  have hb₂ : R.blockRank (f ⁻¹' Uᶜ) (g ⁻¹' U) ≤ (M + Mᵀ).blockRank (U ∩ Y) Uᶜ := by
    calc R.blockRank (f ⁻¹' Uᶜ) (g ⁻¹' U)
        = M.blockRank (Uᶜ ∩ X) (U ∩ Y) := by
          rw [← hMR, M.blockRank_submatrix hf hg, image_preimage_eq_inter_range,
            image_preimage_eq_inter_range]
      _ = Mᵀ.blockRank (U ∩ Y) (Uᶜ ∩ X) := (M.blockRank_transpose _ _).symm
      _ = (M + Mᵀ).blockRank (U ∩ Y) (Uᶜ ∩ X) := blockRank_congr fun i hi j _ => by
            simp only [Matrix.add_apply, transpose_apply, hMX i j (hnotX i hi.2), zero_add]
      _ ≤ (M + Mᵀ).blockRank (U ∩ Y) Uᶜ := blockRank_mono_right _ _ inter_subset_left
  unfold cutRank
  omega

/-- Two injective maps with disjoint ranges pull back at most `|V|` elements of `V`. -/
theorem ncard_preimage_add_ncard_preimage_le [Finite ι] {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : Disjoint (range f) (range g))
    (V : Set ι) : (f ⁻¹' V).ncard + (g ⁻¹' V).ncard ≤ V.ncard := by
  rw [← ncard_image_of_injective _ hf, ← ncard_image_of_injective _ hg,
    ← ncard_union_eq (hfg.mono (image_subset_range _ _) (image_subset_range _ _))]
  exact ncard_le_ncard (union_subset (image_preimage_subset _ _) (image_preimage_subset _ _))

/-- **Bisections of a robust bilinear form.** Let `M` carry a `k × k` matrix `R` that is
submatrix-robust with deficiency `t` on a block whose rows and columns are disjoint sets of
indices, and vanish elsewhere, with at most `2 k + 1` indices in all. Then every set `U` of `k`
indices has cut rank at least `k - (2 t + 1)` in the polar matrix `M + Mᵀ`. -/
theorem SubmatrixRobust.le_cutRank_add [Finite ι] {k t : ℕ}
    {R : Matrix (Fin k) (Fin k) K} (hR : R.SubmatrixRobust t) {M : Matrix ι ι K}
    {f g : Fin k → ι} (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : Disjoint (range f) (range g)) (hMR : M.submatrix f g = R)
    (hM : ∀ i j, i ∉ range f ∨ j ∉ range g → M i j = 0) (hι : Nat.card ι ≤ 2 * k + 1)
    {U : Set ι} (hU : U.ncard = k) : k ≤ (M + Mᵀ).cutRank U + (2 * t + 1) := by
  have hsum := add_blockRank_le_cutRank_add_transpose hf hg hfg hMR hM U
  have hr₁ := hR.min_le (f ⁻¹' U) (g ⁻¹' Uᶜ)
  have hr₂ := hR.min_le (f ⁻¹' Uᶜ) (g ⁻¹' U)
  have hcardFin (V : Set (Fin k)) : V.ncard + Vᶜ.ncard = k := by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have ha := hcardFin (f ⁻¹' U)
  have hb := hcardFin (g ⁻¹' U)
  rw [← preimage_compl] at ha hb
  have hU' := ncard_add_ncard_compl U
  have hab := ncard_preimage_add_ncard_preimage_le hf hg hfg U
  have hab' := ncard_preimage_add_ncard_preimage_le hf hg hfg Uᶜ
  omega

end Bilinear

end Matrix
