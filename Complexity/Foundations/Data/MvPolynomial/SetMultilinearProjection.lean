/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, set-multilinear polynomials)

public import Complexity.Foundations.Data.MvPolynomial.SetMultilinear
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Pi
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The set-multilinear projection

The variables `σ` of a polynomial are split into `d` blocks by a map `blk : σ → Fin d`. A monomial
is set-multilinear on a set `S` of blocks when it is `blockMonomial blk S x` for a choice `x` of one
variable from each block of `S`. The **set-multilinear projection** `MvPolynomial.smProj blk S`
keeps the terms of a polynomial whose monomials are set-multilinear on `S` and drops the others
([Forbes2024, Def. 23], where it is `π_{sm,S}`). It is a linear map whose image consists of the
set-multilinear polynomials on `S` and which fixes them (`MvPolynomial.smProj_eq_self_iff`); on
the empty set of blocks it is the constant coefficient (`MvPolynomial.smProj_empty`).

A monomial is set-multilinear on `S` exactly when its block degrees, the exponent sums over the
blocks, are one on `S` and zero elsewhere (`MvPolynomial.mem_range_blockMonomial_iff`). The block
degrees are the weight of the monomial for the weight `v ↦ single (blk v) 1`, valued in
`Fin d →₀ ℕ`, that sends each variable to the unit vector of its block. So the set-multilinear
polynomials on `S` are the weighted homogeneous polynomials of weighted degree the indicator of `S`
(`MvPolynomial.isSetMultilinear_iff_isWeightedHomogeneous`), and `smProj blk S` is defined as
Mathlib's `MvPolynomial.weightedHomogeneousComponent` for this weight and degree; idempotence and
orthogonality come from Mathlib. From the characterization, the projection of a product is the
sum, over the ways of splitting `S` into disjoint parts, one for each factor, of the products of
the projections of the factors on their parts (`MvPolynomial.smProj_mul`,
`MvPolynomial.smProj_prod`): a set-multilinear monomial of the product comes from set-multilinear
monomials of the factors on disjoint blocks. The projection commutes
with renaming variables along their blocks (`MvPolynomial.rename_smProj`).

## Main definitions

* `MvPolynomial.smProj`: the projection onto the set-multilinear monomials on a set of blocks, a
  weighted homogeneous component.
* `MvPolynomial.blockSplits`: the families of pairwise disjoint sets of blocks, indexed by a
  finite type, with a given union.

## Main results

* `MvPolynomial.mem_range_blockMonomial_iff`: a monomial is set-multilinear on `S` if and only if
  its block degrees are the indicator of `S`.
* `MvPolynomial.isSetMultilinear_iff_isWeightedHomogeneous`: set-multilinear polynomials on `S`
  are the weighted homogeneous polynomials, for the block weight, of degree the indicator of `S`.
* `MvPolynomial.sum_mem_range_blockMonomial_iff`, `MvPolynomial.add_mem_range_blockMonomial_iff`:
  a product of monomials is set-multilinear on `S` exactly when the factors are set-multilinear on
  the parts of an ordered split of `S`.
* `MvPolynomial.isSetMultilinear_smProj`, `MvPolynomial.smProj_eq_self_iff`: the projection is
  set-multilinear and fixes exactly the set-multilinear polynomials.
* `MvPolynomial.IsSetMultilinear.smProj_eq_zero`, `MvPolynomial.smProj_smProj`: the projections on
  different sets of blocks are orthogonal.
* `MvPolynomial.smProj_empty`, `MvPolynomial.smProj_C`, `MvPolynomial.smProj_one`,
  `MvPolynomial.smProj_X`: projections of constants and variables.
* `MvPolynomial.smProj_mul`, `MvPolynomial.smProj_prod`: projections of products.
* `MvPolynomial.rename_smProj`: the projection commutes with renaming along the blocks.

## References

* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024],
  Definition 23, p. 31:12 (the projection `π_{sm,S}`), and the remark after it, p. 31:13
  (`π_{sm,∅}(f) = f(0)`). The product formulas `smProj_mul` and `smProj_prod` are the expansion
  used in the proof of [Forbes2024, Lemma 26], pp. 31:13–31:14; their statement as identities of
  polynomials, the block-degree characterization, its weighted homogeneous form and
  `rename_smProj` are original.
-/

@[expose] public section

namespace MvPolynomial

open Finset Function

variable {σ K : Type*} {d : ℕ}

section Monomial

/-- The block degree of a monomial at block `i` is the sum of its exponents on the variables of
block `i`. -/
private theorem mapDomain_apply_eq_sum (blk : σ → Fin d) (m : σ →₀ ℕ) (i : Fin d) :
    m.mapDomain blk i = ∑ v ∈ m.support with blk v = i, m v := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, sum_filter]
  exact sum_congr rfl fun v _ => Finsupp.single_apply

/-- The indicator vector of a set of blocks. -/
private theorem sum_single_one_apply (S : Finset (Fin d)) (i : Fin d) :
    (∑ j ∈ S, Finsupp.single j 1 : Fin d →₀ ℕ) i = if i ∈ S then 1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  exact sum_ite_eq' S i fun _ => 1

/-- A set of blocks is determined by its indicator vector. -/
private theorem sum_single_one_injective {S T : Finset (Fin d)}
    (h : (∑ j ∈ S, Finsupp.single j 1 : Fin d →₀ ℕ) = ∑ j ∈ T, Finsupp.single j 1) : S = T := by
  ext i
  have h' := DFunLike.congr_fun h i
  rw [sum_single_one_apply, sum_single_one_apply] at h'
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

/-- **Block-degree characterization.** A monomial is set-multilinear on `S`, that is, it takes
exactly one variable with exponent one from each block of `S` and no other variable, if and only
if its block degrees are `1` on the blocks of `S` and `0` on the others (original). -/
theorem mem_range_blockMonomial_iff {blk : σ → Fin d} {S : Finset (Fin d)} {m : σ →₀ ℕ} :
    m ∈ Set.range (blockMonomial blk S) ↔
      m.mapDomain blk = ∑ i ∈ S, Finsupp.single i 1 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    rw [blockMonomial, Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single, (x _).2]
    exact sum_coe_sort S fun i => Finsupp.single i 1
  · intro h
    have hm (i : Fin d) : ∑ v ∈ m.support with blk v = i, m v = if i ∈ S then 1 else 0 := by
      rw [← mapDomain_apply_eq_sum, h, sum_single_one_apply]
    -- Each exponent is at most the block degree of its block.
    have hle {v : σ} (hv : v ∈ m.support) : m v ≤ if blk v ∈ S then 1 else 0 :=
      hm (blk v) ▸ single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hv, rfl⟩)
    -- Two variables of `m` in the same block coincide.
    have hinj {v w : σ} (hv : v ∈ m.support) (hw : w ∈ m.support) (hvw : blk v = blk w) :
        v = w := by
      by_contra hne
      have hsub : ({v, w} : Finset σ) ⊆ {u ∈ m.support | blk u = blk v} := by
        intro u hu
        rcases mem_insert.1 hu with rfl | hu
        · exact mem_filter.2 ⟨hv, rfl⟩
        · exact mem_filter.2 ⟨mem_singleton.1 hu ▸ hw, (mem_singleton.1 hu ▸ hvw.symm)⟩
      have h₂ := (sum_le_sum_of_subset hsub).trans_eq (hm (blk v))
      rw [sum_pair hne] at h₂
      have := Finsupp.mem_support_iff.1 hv
      have := Finsupp.mem_support_iff.1 hw
      split_ifs at h₂ <;> omega
    have hex (i : S) : ∃ v ∈ m.support, blk v = i := by
      by_contra hne
      have h₀ := hm i
      rw [filter_false_of_mem fun v hv h => hne ⟨v, hv, h⟩, sum_empty, ite_eq_left i.2] at h₀
      exact zero_ne_one h₀
    choose x hx using hex
    refine ⟨fun i => ⟨x i, (hx i).2⟩, ?_⟩
    ext v
    rw [blockMonomial_apply]
    split_ifs with hS hxv
    · have hv : v ∈ m.support := hxv ▸ (hx _).1
      have := hle hv
      rw [ite_eq_left hS] at this
      have := Finsupp.mem_support_iff.1 hv
      omega
    · by_contra hne
      have hv : v ∈ m.support := Finsupp.mem_support_iff.2 (Ne.symm hne)
      exact hxv (hinj (hx _).1 hv (hx _).2)
    · by_contra hne
      have hv : v ∈ m.support := Finsupp.mem_support_iff.2 (Ne.symm hne)
      have := hle hv
      rw [ite_eq_right hS] at this
      exact hne (by omega)

/-- The weight that sends each variable to the unit vector of its block computes the block
degrees of a monomial. -/
theorem _root_.Finsupp.weight_single_one_eq_mapDomain {τ : Type*} (blk : σ → τ) (m : σ →₀ ℕ) :
    Finsupp.weight (fun v => Finsupp.single (blk v) (1 : ℕ)) m = m.mapDomain blk := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  exact Finsupp.sum_congr fun v _ => by rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A monomial is set-multilinear on `S` exactly when its weight, for the weight
`v ↦ single (blk v) 1` that sends each variable to the unit vector of its block, is the indicator
of `S`. -/
theorem mem_range_blockMonomial_iff_weight {blk : σ → Fin d} {S : Finset (Fin d)}
    {m : σ →₀ ℕ} :
    m ∈ Set.range (blockMonomial blk S) ↔
      Finsupp.weight (fun v => Finsupp.single (blk v) (1 : ℕ)) m =
        ∑ i ∈ S, Finsupp.single i 1 := by
  rw [Finsupp.weight_single_one_eq_mapDomain, mem_range_blockMonomial_iff]

/-- A monomial is set-multilinear on at most one set of blocks. -/
theorem eq_of_mem_range_blockMonomial {blk : σ → Fin d} {S T : Finset (Fin d)} {m : σ →₀ ℕ}
    (hS : m ∈ Set.range (blockMonomial blk S)) (hT : m ∈ Set.range (blockMonomial blk T)) :
    S = T :=
  sum_single_one_injective
    ((mem_range_blockMonomial_iff.1 hS).symm.trans (mem_range_blockMonomial_iff.1 hT))

/-- Renaming the variables along their blocks preserves set-multilinearity of monomials, in both
directions (original). -/
theorem mapDomain_mem_range_blockMonomial_iff {τ : Type*} {blk : σ → Fin d} {blk' : τ → Fin d}
    (e : σ → τ) (he : ∀ v, blk' (e v) = blk v) {S : Finset (Fin d)} {m : σ →₀ ℕ} :
    m.mapDomain e ∈ Set.range (blockMonomial blk' S) ↔ m ∈ Set.range (blockMonomial blk S) := by
  rw [mem_range_blockMonomial_iff, mem_range_blockMonomial_iff, ← Finsupp.mapDomain_comp]
  have : blk' ∘ e = blk := funext he
  rw [this]

end Monomial

section Splits

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The **ordered splits** of a set `S` of blocks into `ι`-indexed parts: the families of pairwise
disjoint, possibly empty sets of blocks whose union is `S`. -/
def blockSplits (S : Finset (Fin d)) : Finset (ι → Finset (Fin d)) :=
  {T ∈ Fintype.piFinset fun _ => S.powerset |
    (∀ j k, j ≠ k → Disjoint (T j) (T k)) ∧ univ.biUnion T = S}

variable {ι}

/-- A family is an ordered split of `S` exactly when its parts are pairwise disjoint with union
`S`. -/
theorem mem_blockSplits {S : Finset (Fin d)} {T : ι → Finset (Fin d)} :
    T ∈ blockSplits ι S ↔ Pairwise (Disjoint on T) ∧ univ.biUnion T = S := by
  rw [blockSplits, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h, hU⟩
    exact ⟨fun j k hjk => h j k hjk, hU⟩
  · rintro ⟨h, rfl⟩
    exact ⟨fun j => mem_powerset.2 (subset_biUnion_of_mem T (mem_univ j)),
      fun j k hjk => h hjk, rfl⟩

/-- A family of block-degree vectors sums to the indicator of `S` exactly when it is the family of
indicators of an ordered split of `S`. -/
private theorem sum_eq_sum_single_one_iff {S : Finset (Fin d)} (u : ι → Fin d →₀ ℕ) :
    ∑ j, u j = ∑ i ∈ S, Finsupp.single i 1 ↔
      ∃ T ∈ blockSplits ι S, ∀ j, u j = ∑ i ∈ T j, Finsupp.single i 1 := by
  classical
  constructor
  · intro h
    have hi (i : Fin d) : ∑ j, u j i = if i ∈ S then 1 else 0 := by
      rw [← sum_single_one_apply, ← h, Finsupp.finsetSum_apply]
    have hle (j : ι) (i : Fin d) : u j i ≤ 1 :=
      (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans
        ((hi i).trans_le (by split_ifs <;> omega))
    refine ⟨fun j => (u j).support, mem_blockSplits.2 ⟨fun j k hjk => ?_, ?_⟩, fun j => ?_⟩
    · refine disjoint_left.2 fun i hj hk => ?_
      have h₂ := (sum_le_sum_of_subset (f := fun j => u j i) (subset_univ {j, k})).trans_eq (hi i)
      rw [sum_pair hjk] at h₂
      have := Finsupp.mem_support_iff.1 hj
      have := Finsupp.mem_support_iff.1 hk
      split_ifs at h₂ <;> omega
    · ext i
      rw [mem_biUnion]
      have hsum := hi i
      constructor
      · rintro ⟨j, -, hj⟩
        by_contra hS
        rw [ite_eq_right hS, sum_eq_zero_iff] at hsum
        exact Finsupp.mem_support_iff.1 hj (hsum j (mem_univ j))
      · intro hS
        rw [ite_eq_left hS] at hsum
        by_contra hne
        rw [sum_eq_zero fun j _ => Finsupp.notMem_support_iff.1 fun hj =>
          hne ⟨j, mem_univ j, hj⟩] at hsum
        exact zero_ne_one hsum
    · ext i
      rw [sum_single_one_apply]
      have := hle j i
      by_cases h0 : u j i = 0
      · rw [ite_eq_right (Finsupp.notMem_support_iff.2 h0), h0]
      · rw [ite_eq_left (Finsupp.mem_support_iff.2 h0)]
        omega
  · rintro ⟨T, hT, hu⟩
    obtain ⟨hdisj, rfl⟩ := mem_blockSplits.1 hT
    rw [sum_biUnion fun j _ k _ hjk => hdisj hjk]
    exact sum_congr rfl fun j _ => hu j

/-- A family of monomials multiplies to a set-multilinear monomial on `S` exactly when its members
are set-multilinear on the parts of an ordered split of `S` (original). -/
theorem sum_mem_range_blockMonomial_iff {blk : σ → Fin d} {S : Finset (Fin d)}
    (y : ι → σ →₀ ℕ) :
    ∑ j, y j ∈ Set.range (blockMonomial blk S) ↔
      ∃ T ∈ blockSplits ι S, ∀ j, y j ∈ Set.range (blockMonomial blk (T j)) := by
  simp only [mem_range_blockMonomial_iff, Finsupp.mapDomain_finsetSum]
  exact sum_eq_sum_single_one_iff fun j => (y j).mapDomain blk

/-- Two monomials multiply to a set-multilinear monomial on `S` exactly when they are
set-multilinear on complementary parts of `S` (original). -/
theorem add_mem_range_blockMonomial_iff {blk : σ → Fin d} {S : Finset (Fin d)} {a b : σ →₀ ℕ} :
    a + b ∈ Set.range (blockMonomial blk S) ↔
      ∃ T ∈ S.powerset, a ∈ Set.range (blockMonomial blk T) ∧
        b ∈ Set.range (blockMonomial blk (S \ T)) := by
  classical
  simp only [mem_range_blockMonomial_iff, Finsupp.mapDomain_add, mem_powerset]
  constructor
  · intro h
    have hi (i : Fin d) : a.mapDomain blk i + b.mapDomain blk i = if i ∈ S then 1 else 0 := by
      rw [← sum_single_one_apply, ← h, Finsupp.add_apply]
    refine ⟨(a.mapDomain blk).support, fun i hi' => ?_, ?_, ?_⟩
    · have h' := hi i
      have ha := Finsupp.mem_support_iff.1 hi'
      by_contra hS
      rw [ite_eq_right hS] at h'
      omega
    · ext i
      have h' := hi i
      rw [sum_single_one_apply]
      by_cases ha : a.mapDomain blk i = 0
      · rw [ite_eq_right (Finsupp.notMem_support_iff.2 ha), ha]
      · rw [ite_eq_left (Finsupp.mem_support_iff.2 ha)]
        split_ifs at h' <;> omega
    · ext i
      have h' := hi i
      rw [sum_single_one_apply]
      by_cases hS : i ∈ S
      · rw [ite_eq_left hS] at h'
        by_cases ha : a.mapDomain blk i = 0
        · rw [ite_eq_left (mem_sdiff.2 ⟨hS, Finsupp.notMem_support_iff.2 ha⟩)]
          omega
        · rw [ite_eq_right fun h => (mem_sdiff.1 h).2 (Finsupp.mem_support_iff.2 ha)]
          omega
      · rw [ite_eq_right hS] at h'
        rw [ite_eq_right fun h => hS (mem_sdiff.1 h).1]
        omega
  · rintro ⟨T, hT, ha, hb⟩
    rw [ha, hb, ← sum_union disjoint_sdiff, union_sdiff_of_subset hT]

end Splits

variable [CommSemiring K]

/-- **Set-multilinear polynomials are weighted homogeneous.** A polynomial is set-multilinear on
`S` exactly when it is weighted homogeneous of weighted degree the indicator of `S`, for the
weight `v ↦ single (blk v) 1` that sends each variable to the unit vector of its block
(original). -/
theorem isSetMultilinear_iff_isWeightedHomogeneous {blk : σ → Fin d} {S : Finset (Fin d)}
    {f : MvPolynomial σ K} :
    IsSetMultilinear blk S f ↔
      IsWeightedHomogeneous (fun v => Finsupp.single (blk v) (1 : ℕ)) f
        (∑ i ∈ S, Finsupp.single i 1) :=
  ⟨fun hf _ hm => mem_range_blockMonomial_iff_weight.1 (hf _ (mem_support_iff.2 hm)),
    fun hf _ hm => mem_range_blockMonomial_iff_weight.2 (hf (mem_support_iff.1 hm))⟩

/-- The **set-multilinear projection** `π_{sm,S}` of [Forbes2024, Def. 23]: the linear map that
keeps the terms whose monomials are set-multilinear on the set `S` of blocks and drops the others.
It is Mathlib's weighted homogeneous component of weighted degree the indicator of `S`, for the
weight `v ↦ single (blk v) 1` that sends each variable to the unit vector of its block
(`MvPolynomial.isSetMultilinear_iff_isWeightedHomogeneous`). -/
noncomputable def smProj (blk : σ → Fin d) (S : Finset (Fin d)) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  weightedHomogeneousComponent (fun v => Finsupp.single (blk v) (1 : ℕ))
    (∑ i ∈ S, Finsupp.single i 1)

/-- The set-multilinear projection on `S` is the weighted homogeneous component, for the block
weight, of weighted degree the indicator of `S`. -/
theorem smProj_eq_weightedHomogeneousComponent (blk : σ → Fin d) (S : Finset (Fin d)) :
    smProj (K := K) blk S = weightedHomogeneousComponent
      (fun v => Finsupp.single (blk v) (1 : ℕ)) (∑ i ∈ S, Finsupp.single i 1) :=
  rfl

variable {blk : σ → Fin d} {S T : Finset (Fin d)} {f g : MvPolynomial σ K}

/-- The projection keeps the coefficients of the set-multilinear monomials on `S`. -/
theorem coeff_smProj_of_mem {m : σ →₀ ℕ} (hm : m ∈ Set.range (blockMonomial blk S)) :
    (smProj blk S f).coeff m = f.coeff m := by
  classical
  rw [smProj, coeff_weightedHomogeneousComponent,
    ite_eq_left (mem_range_blockMonomial_iff_weight.1 hm)]

/-- The projection drops the coefficients of the other monomials. -/
theorem coeff_smProj_of_notMem {m : σ →₀ ℕ} (hm : m ∉ Set.range (blockMonomial blk S)) :
    (smProj blk S f).coeff m = 0 := by
  classical
  rw [smProj, coeff_weightedHomogeneousComponent,
    ite_eq_right fun h => hm (mem_range_blockMonomial_iff_weight.2 h)]

/-- The projection of a monomial keeps it if it is set-multilinear on `S`, and is zero
otherwise. -/
theorem smProj_monomial (m : σ →₀ ℕ) (a : K) [Decidable (m ∈ Set.range (blockMonomial blk S))] :
    smProj blk S (monomial m a) =
      if m ∈ Set.range (blockMonomial blk S) then monomial m a else 0 := by
  classical
  ext n
  by_cases hn : n ∈ Set.range (blockMonomial blk S)
  · rw [coeff_smProj_of_mem hn]
    split_ifs with hm
    · rfl
    · rw [coeff_monomial, ite_eq_right fun (h : m = n) => hm (h ▸ hn),
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · rw [coeff_smProj_of_notMem hn]
    split_ifs with hm
    · rw [coeff_monomial, ite_eq_right fun (h : m = n) => hn (h ▸ hm)]
    · rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The projection of a monomial, with the condition in the coefficient. -/
private theorem smProj_monomial' (m : σ →₀ ℕ) (a : K)
    [Decidable (m ∈ Set.range (blockMonomial blk S))] :
    smProj blk S (monomial m a) =
      monomial m (if m ∈ Set.range (blockMonomial blk S) then a else 0) := by
  rw [smProj_monomial]
  split_ifs
  · rfl
  · rw [monomial_zero]

/-- The projection is set-multilinear on `S`. -/
theorem isSetMultilinear_smProj (blk : σ → Fin d) (S : Finset (Fin d)) (f : MvPolynomial σ K) :
    IsSetMultilinear blk S (smProj blk S f) :=
  isSetMultilinear_iff_isWeightedHomogeneous.2
    (weightedHomogeneousComponent_isWeightedHomogeneous _ f)

/-- The projection on `S` fixes a set-multilinear polynomial on `S`. -/
theorem IsSetMultilinear.smProj_eq_self (hf : IsSetMultilinear blk S f) : smProj blk S f = f :=
  (isSetMultilinear_iff_isWeightedHomogeneous.1 hf).weightedHomogeneousComponent_same

/-- A polynomial is set-multilinear on `S` exactly when the projection on `S` fixes it. -/
theorem smProj_eq_self_iff : smProj blk S f = f ↔ IsSetMultilinear blk S f :=
  ⟨fun h => h ▸ isSetMultilinear_smProj blk S f, IsSetMultilinear.smProj_eq_self⟩

/-- The projection on `T` of a set-multilinear polynomial on a different set `S` is zero. -/
theorem IsSetMultilinear.smProj_eq_zero (hf : IsSetMultilinear blk S f) (hST : T ≠ S) :
    smProj blk T f = 0 :=
  (isSetMultilinear_iff_isWeightedHomogeneous.1 hf).weightedHomogeneousComponent_ne _
    fun h => hST (sum_single_one_injective h)

/-- Projecting twice: the projections on different sets of blocks are orthogonal, and each is
idempotent. -/
theorem smProj_smProj [Decidable (T = S)] :
    smProj blk T (smProj blk S f) = if T = S then smProj blk S f else 0 := by
  split_ifs with h
  · exact h ▸ (isSetMultilinear_smProj blk S f).smProj_eq_self
  · exact (isSetMultilinear_smProj blk S f).smProj_eq_zero h

/-- The projection is additive. -/
theorem smProj_add : smProj blk S (f + g) = smProj blk S f + smProj blk S g :=
  map_add _ f g

/-- The projection commutes with multiplication by a constant. -/
theorem smProj_C_mul (c : K) : smProj blk S (C c * f) = C c * smProj blk S f := by
  rw [smProj, weightedHomogeneousComponent_C_mul]

/-- **The projection on no blocks is the constant coefficient** [Forbes2024, p. 31:13]. -/
theorem smProj_empty (blk : σ → Fin d) (f : MvPolynomial σ K) :
    smProj blk ∅ f = C (constantCoeff f) := by
  classical
  have h0 : Set.range (blockMonomial blk ∅) = {0} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨fun i => absurd i.2 (notMem_empty _), ?_⟩, ?_⟩
    · exact sum_of_isEmpty _
    · rintro m ⟨x, rfl⟩
      exact sum_of_isEmpty _
  ext m
  rw [coeff_C, constantCoeff_eq]
  by_cases hm : m = 0
  · subst hm
    rw [coeff_smProj_of_mem (h0 ▸ rfl), ite_eq_left rfl]
  · rw [coeff_smProj_of_notMem (h0 ▸ hm), ite_eq_right (Ne.symm hm)]

/-- The projection of a constant is the constant on no blocks and zero otherwise. -/
theorem smProj_C (blk : σ → Fin d) (S : Finset (Fin d)) (c : K) :
    smProj blk S (C c : MvPolynomial σ K) = if S = ∅ then C c else 0 := by
  split_ifs with h
  · exact (h ▸ isSetMultilinear_C blk c).smProj_eq_self
  · exact (isSetMultilinear_C blk c).smProj_eq_zero h

/-- The projection of `1` is `1` on no blocks and zero otherwise. -/
theorem smProj_one (blk : σ → Fin d) (S : Finset (Fin d)) :
    smProj blk S (1 : MvPolynomial σ K) = if S = ∅ then 1 else 0 := by
  rw [← C_1, smProj_C]

/-- The projection of a variable is the variable on its own block and zero otherwise. -/
theorem smProj_X (blk : σ → Fin d) (S : Finset (Fin d)) (v : σ) :
    smProj blk S (X v : MvPolynomial σ K) = if S = {blk v} then X v else 0 := by
  split_ifs with h
  · exact (h ▸ isSetMultilinear_X blk v).smProj_eq_self
  · exact (isSetMultilinear_X blk v).smProj_eq_zero h

/-- The projection as a sum over the support, with the condition in the coefficients. -/
private theorem smProj_eq_sum [DecidablePred (· ∈ Set.range (blockMonomial blk S))]
    (f : MvPolynomial σ K) :
    smProj blk S f = ∑ m ∈ f.support,
      monomial m (if m ∈ Set.range (blockMonomial blk S) then f.coeff m else 0) := by
  conv_lhs => rw [f.as_sum, map_sum]
  exact sum_congr rfl fun m _ => smProj_monomial' m _

/-- **The projection of a product** (original as stated; the expansion in the proof of
[Forbes2024, Lemma 26]): the set-multilinear part of `f * g` on `S` is the sum, over the parts
`T ⊆ S`, of the product of the part of `f` on `T` and the part of `g` on `S \ T`. -/
theorem smProj_mul (blk : σ → Fin d) (S : Finset (Fin d)) (f g : MvPolynomial σ K) :
    smProj blk S (f * g) = ∑ T ∈ S.powerset, smProj blk T f * smProj blk (S \ T) g := by
  classical
  have key (a b : σ →₀ ℕ) (x y : K) :
      ∑ T ∈ S.powerset, (if a ∈ Set.range (blockMonomial blk T) then x else 0) *
          (if b ∈ Set.range (blockMonomial blk (S \ T)) then y else 0) =
        if a + b ∈ Set.range (blockMonomial blk S) then x * y else 0 := by
    simp only [ite_zero_mul_ite_zero]
    by_cases h : a + b ∈ Set.range (blockMonomial blk S)
    · obtain ⟨T₀, hT₀, ha, hb⟩ := add_mem_range_blockMonomial_iff.1 h
      rw [ite_eq_left h, sum_eq_single_of_mem T₀ hT₀ fun T _ hT =>
        ite_eq_right fun h' => hT (eq_of_mem_range_blockMonomial h'.1 ha), ite_eq_left ⟨ha, hb⟩]
    · rw [ite_eq_right h]
      exact sum_eq_zero fun T hT =>
        ite_eq_right fun h' => h (add_mem_range_blockMonomial_iff.2 ⟨T, hT, h'⟩)
  have hexp (s t : Finset (σ →₀ ℕ)) (x y : (σ →₀ ℕ) → K) :
      (∑ a ∈ s, monomial a (x a)) * ∑ b ∈ t, monomial b (y b) =
        ∑ a ∈ s, ∑ b ∈ t, monomial (a + b) (x a * y b) := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => monomial_mul_monomial ..
  have hT (T : Finset (Fin d)) : smProj blk T f * smProj blk (S \ T) g =
      ∑ a ∈ f.support, ∑ b ∈ g.support, monomial (a + b)
        ((if a ∈ Set.range (blockMonomial blk T) then f.coeff a else 0) *
          (if b ∈ Set.range (blockMonomial blk (S \ T)) then g.coeff b else 0)) := by
    rw [smProj_eq_sum f, smProj_eq_sum g, hexp]
  rw [sum_congr rfl fun T _ => hT T, sum_comm]
  conv_lhs => rw [f.as_sum, g.as_sum, hexp, map_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [map_sum, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [smProj_monomial', ← map_sum, key]

/-- **The projection of a finite product** (original as stated; the expansion in the proof of
[Forbes2024, Lemma 26]): the set-multilinear part of `∏ j, f j` on `S` is the sum, over the
ordered splits `T` of `S` into pairwise disjoint parts `T j` covering `S`, of the products of the
parts of the factors `f j` on `T j`. -/
theorem smProj_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (blk : σ → Fin d)
    (S : Finset (Fin d)) (f : ι → MvPolynomial σ K) :
    smProj blk S (∏ j, f j) = ∑ T ∈ blockSplits ι S, ∏ j, smProj blk (T j) (f j) := by
  classical
  have key (y : ι → σ →₀ ℕ) (x : ι → K) :
      ∑ T ∈ blockSplits ι S, ∏ j, (if y j ∈ Set.range (blockMonomial blk (T j)) then x j else 0) =
        if ∑ j, y j ∈ Set.range (blockMonomial blk S) then ∏ j, x j else 0 := by
    simp only [Fintype.prod_ite_zero]
    by_cases h : ∑ j, y j ∈ Set.range (blockMonomial blk S)
    · obtain ⟨T₀, hT₀, hy⟩ := (sum_mem_range_blockMonomial_iff y).1 h
      rw [ite_eq_left h, sum_eq_single_of_mem T₀ hT₀ fun T _ hT => ite_eq_right fun h' =>
        hT (funext fun j => eq_of_mem_range_blockMonomial (h' j) (hy j)), ite_eq_left hy]
    · rw [ite_eq_right h]
      exact sum_eq_zero fun T hT =>
        ite_eq_right fun h' => h ((sum_mem_range_blockMonomial_iff y).2 ⟨T, hT, h'⟩)
  have hexp (s : ι → Finset (σ →₀ ℕ)) (x : ι → (σ →₀ ℕ) → K) :
      ∏ j, ∑ m ∈ s j, monomial m (x j m) =
        ∑ y ∈ Fintype.piFinset s, monomial (∑ j, y j) (∏ j, x j (y j)) := by
    rw [prod_univ_sum]
    exact sum_congr rfl fun y _ => (monomial_sum_prod _ _ _).symm
  have hT (T : ι → Finset (Fin d)) : ∏ j, smProj blk (T j) (f j) =
      ∑ y ∈ Fintype.piFinset fun j => (f j).support, monomial (∑ j, y j)
        (∏ j, if y j ∈ Set.range (blockMonomial blk (T j)) then (f j).coeff (y j) else 0) := by
    rw [prod_congr rfl fun j _ => smProj_eq_sum (blk := blk) (S := T j) (f j), hexp]
  rw [sum_congr rfl fun T _ => hT T, sum_comm,
    prod_congr rfl fun j _ => (f j).as_sum, hexp, map_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [smProj_monomial', ← map_sum, key]

/-- **The projection commutes with renaming along the blocks** (original): if the renaming `e`
sends each variable to a variable of the same block, then renaming the part of `f` on `S` gives
the part on `S` of the renamed polynomial. The renaming need not be injective. -/
theorem rename_smProj {τ : Type*} {blk' : τ → Fin d} (e : σ → τ) (he : ∀ v, blk' (e v) = blk v)
    (S : Finset (Fin d)) (f : MvPolynomial σ K) :
    rename e (smProj blk S f) = smProj blk' S (rename e f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [smProj_monomial, rename_monomial, smProj_monomial,
      mapDomain_mem_range_blockMonomial_iff e he]
    split_ifs
    · exact rename_monomial e m a
    · exact map_zero _
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]

end MvPolynomial
