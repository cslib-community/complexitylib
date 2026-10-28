/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.MvPolynomial.SetMultilinear
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
import Complexity.Foundations.LinearAlgebra.Matrix.Kronecker
import Complexity.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Relative rank

The variables `σ` of a polynomial are split into `d` blocks by a map `blk : σ → Fin d`, and
set-multilinear polynomials and their monomials are described by choices of one variable per block
(`MvPolynomial.BlockChoice`, `MvPolynomial.IsSetMultilinear`).

For sets `A` and `B` of blocks, the *relative-rank matrix* `relMatrix blk A B f` has rows indexed by
choices on `A` and columns by choices on `B`; its entry is the coefficient in `f` of the product of
the two monomials. The *relative rank* `relRank blk A B f` is its rank divided by the geometric
mean `√(rows * columns)` of its dimensions. With `A` the positive and `B` the negative blocks of a
word `w`, and block `i` of size `2 ^ |w i|`, this is the measure `relrk_w` of Limaye, Srinivasan
and Tavenas [LimayeSrinivasanTavenas2021, §2.1, p. 6]; general `A` and `B` also express the
restricted measures `relrk_{w|S}` used in the multiplicativity property.

The sets `A` and `B` are meant to be disjoint, as the positive and negative blocks of a word are.
The definitions do not require it: on a block of `A ∩ B` the product of a row and a column monomial
can have exponent `2`, and the entries are then coefficients of monomials that are not
set-multilinear. The results below hold for arbitrary `A` and `B`.

This file proves the bound `relrk_w ≤ 1` of the display defining `relrk_w` (`relRank_le_one`) and
the three properties of Claim 7 (ECCC TR21-081, Revision 1, §2.1, pp. 6–7):
* imbalance: `relRank_le_sqrt_rows_div_cols` and `relRank_le_sqrt_cols_div_rows` bound the relative
  rank by the square root of the ratio of the two dimensions, in both orders; together they bound
  it by the square root of the smaller dimension over the larger, which is Claim 7(1);
* subadditivity: `relRank_add_le`, Claim 7(2);
* multiplicativity: `relRank_mul_le` for two factors and `relRank_prod_le` for a finite product,
  for set-multilinear factors on pairwise disjoint sets of blocks, Claim 7(3). LST state equality;
  only the inequality is proved here, which is the direction their lower bound uses.

The rank-level statements `rank_relMatrix_sq_le`, `rank_relMatrix_add_le` and
`rank_relMatrix_mul_le` are natural-number forms of `relrk_w ≤ 1`, subadditivity and
multiplicativity. The dimensions are counted by `MvPolynomial.card_blockChoice`.

## Main definitions

* `Cslib.Circuits.Arithmetic.relMatrix`: the relative-rank coefficient matrix.
* `Cslib.Circuits.Arithmetic.relRank`: the normalized relative rank, a real number.
* `Cslib.Circuits.Arithmetic.blockChoiceCongr`: a renaming of the variables along their blocks,
  acting on choices of one variable per block.

## Main results

* `Cslib.Circuits.Arithmetic.relRank_le_one`: the relative rank is at most `1`.
* `Cslib.Circuits.Arithmetic.relRank_le_sqrt_rows_div_cols`,
  `Cslib.Circuits.Arithmetic.relRank_le_sqrt_cols_div_rows`: imbalance.
* `Cslib.Circuits.Arithmetic.relRank_add_le`: subadditivity.
* `Cslib.Circuits.Arithmetic.relRank_smul_le`, `relRank_smul`: scalar multiples.
* `Cslib.Circuits.Arithmetic.relRank_mul_le`, `Cslib.Circuits.Arithmetic.relRank_prod_le`:
  multiplicativity, as an inequality.
* `Cslib.Circuits.Arithmetic.relMatrix_rename`, `Cslib.Circuits.Arithmetic.relRank_rename`:
  renaming the variables along their blocks permutes the rows and columns, and keeps the relative
  rank.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], §2.1, pp. 6–7, Claim 7. Parametrizing the measure by a
  block map and two arbitrary sets of blocks, instead of by a word, and its invariance under
  renaming, are original to this formalization.
-/

@[expose] public section

open scoped Kronecker

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {σ K : Type*} {d : ℕ}

section Matrix

variable [CommSemiring K]

/-- The **relative-rank matrix** of `f` for the row blocks `A` and column blocks `B`: rows are
indexed by choices of one variable in each block of `A`, columns by choices on `B`, and the entry
is the coefficient in `f` of the product of the two monomials. With `A` and `B` the positive and
negative blocks of a word, this is the matrix `M_w(f)` of [LimayeSrinivasanTavenas2021, §2.1,
p. 6]; indexing it by two arbitrary sets of blocks, so that it also covers LST's sub-words `w|S`,
is original. `A` and `B` are meant to be disjoint: on a shared block the product monomial can
have exponent `2`, and the entries are then coefficients of non-set-multilinear monomials. -/
noncomputable def relMatrix (blk : σ → Fin d) (A B : Finset (Fin d)) (f : MvPolynomial σ K) :
    Matrix (BlockChoice blk A) (BlockChoice blk B) K :=
  Matrix.of fun r c => f.coeff (blockMonomial blk A r + blockMonomial blk B c)

variable (blk : σ → Fin d) (A B : Finset (Fin d))

/-- The entry of the relative-rank matrix at the row choice `r` and the column choice `c` is the
coefficient of the product of their monomials. -/
@[simp]
theorem relMatrix_apply (f : MvPolynomial σ K) (r : BlockChoice blk A) (c : BlockChoice blk B) :
    relMatrix blk A B f r c = f.coeff (blockMonomial blk A r + blockMonomial blk B c) :=
  rfl

/-- The relative-rank matrix of `0` is `0`. -/
@[simp]
theorem relMatrix_zero : relMatrix blk A B (0 : MvPolynomial σ K) = 0 := by
  ext
  simp

/-- The relative-rank matrix is additive in the polynomial. -/
theorem relMatrix_add (f g : MvPolynomial σ K) :
    relMatrix blk A B (f + g) = relMatrix blk A B f + relMatrix blk A B g := by
  ext
  simp

/-- The relative-rank matrix commutes with scaling. -/
theorem relMatrix_smul (c : K) (f : MvPolynomial σ K) :
    relMatrix blk A B (c • f) = c • relMatrix blk A B f := by
  ext
  simp

/-- The relative-rank matrix of a product of set-multilinear polynomials on disjoint blocks is a
submatrix of the Kronecker product of the factors' matrices. -/
theorem relMatrix_mul {blk : σ → Fin d} {A B S T : Finset (Fin d)} {f g : MvPolynomial σ K}
    (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk T g) (hST : Disjoint S T)
    (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T) :
    relMatrix blk A B (f * g) =
      (relMatrix blk (A ∩ S) (B ∩ S) f ⊗ₖ relMatrix blk (A ∩ T) (B ∩ T) g).submatrix
        (fun r => (BlockChoice.restrict Finset.inter_subset_left r,
          BlockChoice.restrict Finset.inter_subset_left r))
        (fun c => (BlockChoice.restrict Finset.inter_subset_left c,
          BlockChoice.restrict Finset.inter_subset_left c)) := by
  ext r c
  rw [Matrix.submatrix_apply, Matrix.kronecker_apply, relMatrix_apply, relMatrix_apply,
    relMatrix_apply, MvPolynomial.coeff_mul_blockMonomial hf hg hST hA hB]

end Matrix

/-! ### Renaming the variables along their blocks -/

section Rename

variable {τ : Type*} {blk : σ → Fin d} {blk' : τ → Fin d}

/-- A renaming of the variables that respects the blocks maps choices of one variable per block
to choices of one variable per block. -/
@[simps]
def blockChoiceCongr (e : σ ≃ τ) (he : ∀ x, blk' (e x) = blk x) (S : Finset (Fin d)) :
    BlockChoice blk S ≃ BlockChoice blk' S where
  toFun x i := ⟨e (x i), (he _).trans (x i).2⟩
  invFun y i := ⟨e.symm (y i), by rw [← he, e.apply_symm_apply]; exact (y i).2⟩
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext i
    simp

/-- The monomial of a renamed choice is the renamed monomial. -/
theorem blockMonomial_blockChoiceCongr (e : σ ≃ τ) (he : ∀ x, blk' (e x) = blk x)
    (S : Finset (Fin d)) (x : BlockChoice blk S) :
    blockMonomial blk' S (blockChoiceCongr e he S x) =
      Finsupp.mapDomain e (blockMonomial blk S x) := by
  simp [blockMonomial, Finsupp.mapDomain_finsetSum]

/-- The relative-rank matrix of a renamed polynomial is the relative-rank matrix of the
polynomial, with rows and columns renamed. -/
theorem relMatrix_rename [CommSemiring K] (e : σ ≃ τ) (he : ∀ x, blk' (e x) = blk x)
    (A B : Finset (Fin d)) (f : MvPolynomial σ K) :
    relMatrix blk' A B (rename e f) =
      (relMatrix blk A B f).submatrix (blockChoiceCongr e he A).symm
        (blockChoiceCongr e he B).symm := by
  ext r c
  obtain ⟨r, rfl⟩ := (blockChoiceCongr e he A).surjective r
  obtain ⟨c, rfl⟩ := (blockChoiceCongr e he B).surjective c
  rw [relMatrix_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    relMatrix_apply, blockMonomial_blockChoiceCongr, blockMonomial_blockChoiceCongr,
    ← Finsupp.mapDomain_add, coeff_rename_mapDomain _ e.injective]

end Rename

section Rank

variable [Fintype σ] [Field K] (blk : σ → Fin d) (A B : Finset (Fin d))

/-- **Relative rank** ([LimayeSrinivasanTavenas2021, §2.1, p. 6]): the rank of the relative-rank
matrix divided by the geometric mean of its dimensions. As for `relMatrix`, the row and column
blocks `A` and `B` are meant to be disjoint. -/
noncomputable def relRank (f : MvPolynomial σ K) : ℝ :=
  (relMatrix blk A B f).rank /
    √((Fintype.card (BlockChoice blk A) * Fintype.card (BlockChoice blk B) : ℕ) : ℝ)

/-- The relative rank is nonnegative. -/
theorem relRank_nonneg (f : MvPolynomial σ K) : 0 ≤ relRank blk A B f :=
  div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

/-- The zero polynomial has relative rank `0`. -/
@[simp]
theorem relRank_zero : relRank blk A B (0 : MvPolynomial σ K) = 0 := by
  simp [relRank]

/-- **The relative rank is at most one, square form**: the square of the rank is at most the
product of the dimensions. This is the natural-number form of the bound `relrk_w ≤ 1` in the
display defining `relrk_w` in [LimayeSrinivasanTavenas2021, §2.1, p. 6]. -/
theorem rank_relMatrix_sq_le (f : MvPolynomial σ K) :
    (relMatrix blk A B f).rank ^ 2 ≤
      Fintype.card (BlockChoice blk A) * Fintype.card (BlockChoice blk B) := by
  rw [sq]
  exact Nat.mul_le_mul (Matrix.rank_le_card_height _) (Matrix.rank_le_card_width _)

/-- A nonnegative quantity at most `R` is at most `√(R / C)` after dividing by `√(R * C)`. -/
private theorem div_sqrt_mul_le {x R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (hx : x ≤ R) :
    x / √(R * C) ≤ √(R / C) := by
  calc x / √(R * C) ≤ R / √(R * C) := div_le_div_of_nonneg_right hx (Real.sqrt_nonneg _)
    _ = (√R * √R) / (√R * √C) := by rw [Real.mul_self_sqrt hR, Real.sqrt_mul hR]
    _ = √(R / C) := by
        rw [Real.sqrt_div' _ hC]
        rcases eq_or_ne (√R) 0 with h | h
        · simp [h]
        · exact mul_div_mul_left _ _ h

/-- **Imbalance** ([LimayeSrinivasanTavenas2021, Claim 7(1), p. 6]): the relative rank is at most
the square root of the number of rows divided by the number of columns. Together with
`relRank_le_sqrt_cols_div_rows` it bounds the relative rank by the square root of the smaller
dimension over the larger, `2 ^ (-|w_[d]| / 2)` in the notation of the source, which is
Claim 7(1). -/
theorem relRank_le_sqrt_rows_div_cols (f : MvPolynomial σ K) :
    relRank blk A B f ≤
      √((Fintype.card (BlockChoice blk A) : ℝ) / Fintype.card (BlockChoice blk B)) := by
  rw [relRank, Nat.cast_mul]
  exact div_sqrt_mul_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast Matrix.rank_le_card_height _)

/-- **Imbalance** ([LimayeSrinivasanTavenas2021, Claim 7(1), p. 6]): the relative rank is at most
the square root of the number of columns divided by the number of rows; see
`relRank_le_sqrt_rows_div_cols` for the other order. -/
theorem relRank_le_sqrt_cols_div_rows (f : MvPolynomial σ K) :
    relRank blk A B f ≤
      √((Fintype.card (BlockChoice blk B) : ℝ) / Fintype.card (BlockChoice blk A)) := by
  rw [relRank, Nat.cast_mul, mul_comm]
  exact div_sqrt_mul_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast Matrix.rank_le_card_width _)

/-- The relative rank is at most `1`, as noted in the display defining `relrk_w` in
[LimayeSrinivasanTavenas2021, §2.1, p. 6]. -/
theorem relRank_le_one (f : MvPolynomial σ K) : relRank blk A B f ≤ 1 := by
  refine div_le_one_of_le₀ (Real.le_sqrt_of_sq_le ?_) (Real.sqrt_nonneg _)
  exact_mod_cast rank_relMatrix_sq_le blk A B f

/-- **Subadditivity of rank** for relative-rank matrices. -/
theorem rank_relMatrix_add_le (f g : MvPolynomial σ K) :
    (relMatrix blk A B (f + g)).rank ≤
      (relMatrix blk A B f).rank + (relMatrix blk A B g).rank := by
  rw [relMatrix_add]
  exact Matrix.rank_add_le _ _

/-- **Subadditivity** ([LimayeSrinivasanTavenas2021, Claim 7(2), p. 7]). -/
theorem relRank_add_le (f g : MvPolynomial σ K) :
    relRank blk A B (f + g) ≤ relRank blk A B f + relRank blk A B g := by
  rw [relRank, relRank, relRank, ← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast rank_relMatrix_add_le blk A B f g)
    (Real.sqrt_nonneg _)

/-- Scaling does not increase the relative rank. -/
theorem relRank_smul_le (c : K) (f : MvPolynomial σ K) :
    relRank blk A B (c • f) ≤ relRank blk A B f := by
  rw [relRank, relRank, relMatrix_smul]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Matrix.rank_smul_le c _)
    (Real.sqrt_nonneg _)

/-- Scaling by a nonzero constant does not change the relative rank. -/
theorem relRank_smul {c : K} (hc : c ≠ 0) (f : MvPolynomial σ K) :
    relRank blk A B (c • f) = relRank blk A B f := by
  refine (relRank_smul_le blk A B c f).antisymm ?_
  calc relRank blk A B f = relRank blk A B (c⁻¹ • c • f) := by rw [inv_smul_smul₀ hc]
    _ ≤ relRank blk A B (c • f) := relRank_smul_le blk A B _ _

/-- Negation does not change the relative rank. -/
@[simp]
theorem relRank_neg (f : MvPolynomial σ K) : relRank blk A B (-f) = relRank blk A B f := by
  rw [← neg_one_smul K f, relRank_smul blk A B (neg_ne_zero.mpr one_ne_zero)]

variable {blk A B}

/-- **Rank multiplicativity, as an inequality**: for set-multilinear factors on disjoint blocks, the
rank of the product's matrix is at most the product of the ranks of the factors' matrices. -/
theorem rank_relMatrix_mul_le {S T : Finset (Fin d)} {f g : MvPolynomial σ K}
    (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk T g) (hST : Disjoint S T)
    (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T) :
    (relMatrix blk A B (f * g)).rank ≤
      (relMatrix blk (A ∩ S) (B ∩ S) f).rank * (relMatrix blk (A ∩ T) (B ∩ T) g).rank := by
  rw [relMatrix_mul hf hg hST hA hB]
  exact (Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_kronecker_le _ _)

/-- **Multiplicativity, as an inequality, binary case** ([LimayeSrinivasanTavenas2021, Claim 7(3),
p. 7]): if `f` and `g` are set-multilinear on disjoint sets `S` and `T` of blocks, which cover the
row and column blocks, then the relative rank of `f * g` is at most the product of the relative
ranks of `f` on the blocks of `S` and `g` on the blocks of `T`. LST state equality; their lower
bound uses only this direction. See `relRank_prod_le` for finite products. -/
theorem relRank_mul_le {S T : Finset (Fin d)} {f g : MvPolynomial σ K}
    (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk T g) (hST : Disjoint S T)
    (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T) :
    relRank blk A B (f * g) ≤
      relRank blk (A ∩ S) (B ∩ S) f * relRank blk (A ∩ T) (B ∩ T) g := by
  have hden : ((Fintype.card (BlockChoice blk A) * Fintype.card (BlockChoice blk B) : ℕ) : ℝ) =
      ((Fintype.card (BlockChoice blk (A ∩ S)) * Fintype.card (BlockChoice blk (B ∩ S)) : ℕ) :
        ℝ) *
      ((Fintype.card (BlockChoice blk (A ∩ T)) * Fintype.card (BlockChoice blk (B ∩ T)) : ℕ) :
        ℝ) := by
    rw [card_blockChoice_inter_mul blk hST hA, card_blockChoice_inter_mul blk hST hB]
    push_cast
    ring
  rw [relRank, relRank, relRank, div_mul_div_comm, ← Real.sqrt_mul (Nat.cast_nonneg _), ← hden]
  exact div_le_div_of_nonneg_right (by exact_mod_cast rank_relMatrix_mul_le hf hg hST hA hB)
    (Real.sqrt_nonneg _)

/-- **Multiplicativity, as an inequality** ([LimayeSrinivasanTavenas2021, Claim 7(3), p. 7]): if
the factors `f i` of a finite product are set-multilinear on pairwise disjoint sets `T i` of blocks,
which together cover the row and column blocks, then the relative rank of the product is at most the
product of the relative ranks of each `f i` on the blocks of `T i`. LST state equality for a
partition of all the blocks; their lower bound uses only this direction. -/
theorem relRank_prod_le {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ K}
    {T : ι → Finset (Fin d)} (hT : (s : Set ι).PairwiseDisjoint T)
    (hf : ∀ i ∈ s, IsSetMultilinear blk (T i) (f i)) (hA : A ⊆ s.biUnion T)
    (hB : B ⊆ s.biUnion T) :
    relRank blk A B (∏ i ∈ s, f i) ≤ ∏ i ∈ s, relRank blk (A ∩ T i) (B ∩ T i) (f i) := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty]
    exact relRank_le_one blk A B 1
  | insert a s ha ih =>
    have hT' : (s : Set ι).PairwiseDisjoint T :=
      hT.subset (Finset.coe_subset.2 (Finset.subset_insert a s))
    have hf' : ∀ i ∈ s, IsSetMultilinear blk (T i) (f i) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdisj : Disjoint (T a) (s.biUnion T) := by
      refine (Finset.disjoint_biUnion_right _ _ _).2 fun i hi => hT
        (Finset.mem_coe.2 (Finset.mem_insert_self a s))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) ?_
      rintro rfl
      exact ha hi
    rw [Finset.biUnion_insert] at hA hB
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine (relRank_mul_le (hf a (Finset.mem_insert_self a s)) (IsSetMultilinear.prod s hT' hf')
      hdisj hA hB).trans (mul_le_mul_of_nonneg_left ?_ (relRank_nonneg _ _ _ _))
    refine (ih hT' hf' Finset.inter_subset_right Finset.inter_subset_right).trans_eq
      (Finset.prod_congr rfl fun i hi => ?_)
    have hsub : T i ⊆ s.biUnion T := Finset.subset_biUnion_of_mem T hi
    rw [Finset.inter_assoc, Finset.inter_eq_right.2 hsub, Finset.inter_assoc,
      Finset.inter_eq_right.2 hsub]

/-- **The relative rank is invariant under renaming the variables along their blocks**
(original). -/
theorem relRank_rename {τ : Type*} [Fintype τ] {blk' : τ → Fin d} (e : σ ≃ τ)
    (he : ∀ x, blk' (e x) = blk x) (A B : Finset (Fin d)) (f : MvPolynomial σ K) :
    relRank blk' A B (rename e f) = relRank blk A B f := by
  rw [relRank, relRank, relMatrix_rename e he, Matrix.rank_submatrix,
    Fintype.card_congr (blockChoiceCongr e he A), Fintype.card_congr (blockChoiceCongr e he B)]

end Rank

end Cslib.Circuits.Arithmetic
