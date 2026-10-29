/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, set-multilinear polynomials)

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finset.Pi

/-!
# Set-multilinear polynomials

The variables `σ` of a polynomial are split into `d` blocks by a map `blk : σ → Fin d`. A choice of
one variable from each block in a set `S` of blocks (`MvPolynomial.BlockChoice`) determines the
monomial `MvPolynomial.blockMonomial` that multiplies the chosen variables. Distinct choices give
distinct monomials (`MvPolynomial.blockMonomial_injective`), so the choices on `S` enumerate the
set-multilinear monomials on `S`, and there are `∏ i ∈ S, |block i|` of them
(`MvPolynomial.card_blockChoice`). A polynomial is *set-multilinear* on `S`
(`MvPolynomial.IsSetMultilinear`) when every monomial in its support has this form: it takes
exactly one variable, with exponent one, from each block in `S`, and no variable from any other
block.

Set-multilinear polynomials are closed under sums and scaling on a fixed set of blocks, and under
products over disjoint sets of blocks. A coefficient of such a product on a monomial that splits
along the blocks is the product of the coefficients of the two parts
(`MvPolynomial.coeff_mul_blockMonomial`); this is what makes the coefficient matrix of a product a
Kronecker product.

## Main definitions

* `MvPolynomial.BlockChoice`, `MvPolynomial.blockMonomial`: choices of one variable per block and
  their monomials.
* `MvPolynomial.IsSetMultilinear`: set-multilinear polynomials on a set of blocks.

## Main results

* `MvPolynomial.blockMonomial_injective`, `MvPolynomial.card_blockChoice`: the choices on `S`
  are in bijection with the set-multilinear monomials on `S`, which they count.
* `MvPolynomial.IsSetMultilinear.add`, `.smul`, `.mul`, `.sum`, `.prod`, `.one`,
  `MvPolynomial.isSetMultilinear_C`, `MvPolynomial.isSetMultilinear_X`: closure properties.
* `MvPolynomial.coeff_mul_blockMonomial`: coefficients of a product of set-multilinear polynomials
  on disjoint blocks.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], §1, p. 2 (set-multilinear polynomials) and §2.1, p. 6
  (the sets `M^P_w`, `M^N_w` of set-multilinear monomials). The encoding by block maps and choices
  is original.
-/

@[expose] public section

namespace MvPolynomial

variable {σ K : Type*} {d : ℕ}

/-- A choice of one variable from each block in `S`. -/
abbrev BlockChoice (blk : σ → Fin d) (S : Finset (Fin d)) : Type _ :=
  (i : S) → {x : σ // blk x = i}

/-- Restrict a choice on `S` to a subset `T` of its blocks. -/
def BlockChoice.restrict {blk : σ → Fin d} {S T : Finset (Fin d)} (hTS : T ⊆ S)
    (x : BlockChoice blk S) : BlockChoice blk T :=
  Finset.restrict₂ (π := fun i => {x : σ // blk x = i}) hTS x

/-- The exponent vector of the product of the variables chosen by `x`. -/
noncomputable def blockMonomial (blk : σ → Fin d) (S : Finset (Fin d)) (x : BlockChoice blk S) :
    σ →₀ ℕ :=
  ∑ i, Finsupp.single (x i : σ) 1

/-- The monomial of a choice has exponent `1` at the chosen variable of each block in `S`, and `0`
elsewhere. -/
theorem blockMonomial_apply [DecidableEq σ] (blk : σ → Fin d) (S : Finset (Fin d))
    (x : BlockChoice blk S) (v : σ) :
    blockMonomial blk S x v = if h : blk v ∈ S then if (x ⟨blk v, h⟩ : σ) = v then 1 else 0
      else 0 := by
  rw [blockMonomial, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  have key (i : S) (hiv : (x i : σ) = v) : (i : Fin d) = blk v :=
    (x i).2.symm.trans (congrArg blk hiv)
  split_ifs with h hx
  · rw [Finset.sum_eq_single ⟨blk v, h⟩
      (fun i _ hi => ite_eq_right fun hiv => hi (Subtype.ext (key i hiv)))
      (fun h' => absurd (Finset.mem_univ _) h'), ite_eq_left hx]
  · refine Finset.sum_eq_zero fun i _ => ite_eq_right fun hiv => hx ?_
    obtain rfl : i = ⟨blk v, h⟩ := Subtype.ext (key i hiv)
    exact hiv
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right fun hiv => h (key i hiv ▸ i.2)

/-- A variable outside the blocks of `S` does not occur in the monomial of a choice on `S`. -/
theorem blockMonomial_apply_of_notMem (blk : σ → Fin d) {S : Finset (Fin d)}
    (x : BlockChoice blk S) {v : σ} (hv : blk v ∉ S) : blockMonomial blk S x v = 0 := by
  classical
  rw [blockMonomial_apply, dite_eq_right hv]

/-- At a variable of block `i`, the monomial of a choice has exponent `1` if the variable is the
one chosen in block `i`, and `0` otherwise. -/
theorem blockMonomial_apply_of_eq [DecidableEq σ] {blk : σ → Fin d} {S : Finset (Fin d)}
    (x : BlockChoice blk S) {i : S} {v : σ} (hv : blk v = i) :
    blockMonomial blk S x v = if (x i : σ) = v then 1 else 0 := by
  obtain ⟨i, hi⟩ := i
  simp only at hv
  subst hv
  rw [blockMonomial_apply, dite_eq_left hi]

/-- Distinct choices give distinct monomials, so the choices on `S` are in bijection with the
set-multilinear monomials on `S`, the set `M^P_w` or `M^N_w` of [LimayeSrinivasanTavenas2021, §2.1]
for `S` the positive or negative blocks; `card_blockChoice` therefore counts these monomials. -/
theorem blockMonomial_injective (blk : σ → Fin d) (S : Finset (Fin d)) :
    Function.Injective (blockMonomial blk S) := by
  classical
  intro x y hxy
  funext i
  apply Subtype.ext
  have h := DFunLike.congr_fun hxy (x i : σ)
  rw [blockMonomial_apply_of_eq x (x i).2, blockMonomial_apply_of_eq y (x i).2, ite_eq_left rfl]
    at h
  by_contra hne
  rw [ite_eq_right fun h' => hne h'.symm] at h
  exact one_ne_zero h

/-- Restricting a choice to a subset of the blocks restricts its monomial to those blocks. -/
theorem blockMonomial_restrict_apply (blk : σ → Fin d) {S T : Finset (Fin d)} (hTS : T ⊆ S)
    (x : BlockChoice blk S) (v : σ) :
    blockMonomial blk T (BlockChoice.restrict hTS x) v =
      if blk v ∈ T then blockMonomial blk S x v else 0 := by
  classical
  by_cases hT : blk v ∈ T
  · rw [ite_eq_left hT, blockMonomial_apply, blockMonomial_apply, dite_eq_left hT,
      dite_eq_left (hTS hT)]
    rfl
  · rw [ite_eq_right hT, blockMonomial_apply_of_notMem _ _ hT]

/-- Restricting a choice on `A` to the blocks of `A ∩ S` restricts its monomial to the blocks
of `S`. -/
theorem blockMonomial_inter_apply (blk : σ → Fin d) {A : Finset (Fin d)} (S : Finset (Fin d))
    (x : BlockChoice blk A) (v : σ) :
    blockMonomial blk (A ∩ S) (BlockChoice.restrict Finset.inter_subset_left x) v =
      if blk v ∈ S then blockMonomial blk A x v else 0 := by
  rw [blockMonomial_restrict_apply]
  by_cases hA : blk v ∈ A
  · simp only [Finset.mem_inter, hA, true_and]
  · simp only [Finset.mem_inter, hA, false_and, blockMonomial_apply_of_notMem _ _ hA,
      ite_self]

/-- There are `∏ i ∈ S, |block i|` choices of one variable per block of `S`. -/
theorem card_blockChoice [Fintype σ] (blk : σ → Fin d) (S : Finset (Fin d)) :
    Fintype.card (BlockChoice blk S) = ∏ i ∈ S, Fintype.card {x : σ // blk x = i} := by
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort S fun i => Fintype.card {x : σ // blk x = i}

/-- The choices on `A` split into choices on `A ∩ S` and `A ∩ T` when `S` and `T` are disjoint and
cover `A`. -/
theorem card_blockChoice_inter_mul [Fintype σ] (blk : σ → Fin d) {A S T : Finset (Fin d)}
    (hST : Disjoint S T) (hA : A ⊆ S ∪ T) :
    Fintype.card (BlockChoice blk A) =
      Fintype.card (BlockChoice blk (A ∩ S)) * Fintype.card (BlockChoice blk (A ∩ T)) := by
  rw [card_blockChoice, card_blockChoice, card_blockChoice,
    ← Finset.prod_union (hST.mono Finset.inter_subset_right Finset.inter_subset_right),
    ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hA]

variable [CommSemiring K]

/-- A polynomial is **set-multilinear** on the set `S` of blocks if every monomial in its support
is the product of one variable from each block in `S`: it has exactly one variable, with exponent
one, from each block in `S`, and no variable from any other block. -/
def IsSetMultilinear (blk : σ → Fin d) (S : Finset (Fin d)) (f : MvPolynomial σ K) : Prop :=
  ∀ m ∈ f.support, ∃ x : BlockChoice blk S, blockMonomial blk S x = m

namespace IsSetMultilinear

variable {blk : σ → Fin d} {S T : Finset (Fin d)} {f g : MvPolynomial σ K}

/-- A monomial in the support of a set-multilinear polynomial on `S` has no variable outside the
blocks of `S`. -/
theorem apply_eq_zero (hf : IsSetMultilinear blk S f) {m : σ →₀ ℕ} (hm : m ∈ f.support)
    {v : σ} (hv : blk v ∉ S) : m v = 0 := by
  obtain ⟨x, rfl⟩ := hf m hm
  exact blockMonomial_apply_of_notMem blk x hv

/-- The zero polynomial is set-multilinear on every set of blocks. -/
theorem zero : IsSetMultilinear blk S (0 : MvPolynomial σ K) := by
  simp [IsSetMultilinear]

/-- A sum of set-multilinear polynomials on `S` is set-multilinear on `S`. -/
theorem add (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk S g) :
    IsSetMultilinear blk S (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  exacts [hf m hm, hg m hm]

/-- A scalar multiple of a set-multilinear polynomial on `S` is set-multilinear on `S`. -/
theorem smul (c : K) (hf : IsSetMultilinear blk S f) : IsSetMultilinear blk S (c • f) :=
  fun m hm => hf m (support_smul hm)

/-- A product of set-multilinear polynomials on disjoint sets of blocks is set-multilinear on their
union. -/
theorem mul (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk T g)
    (hST : Disjoint S T) : IsSetMultilinear blk (S ∪ T) (f * g) := by
  classical
  intro m hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  obtain ⟨x, rfl⟩ := hf m₁ hm₁
  obtain ⟨y, rfl⟩ := hg m₂ hm₂
  refine ⟨fun i => if h : (i : Fin d) ∈ S then x ⟨i, h⟩ else
    y ⟨i, (Finset.mem_union.mp i.2).resolve_left h⟩, ?_⟩
  ext v
  rw [Finsupp.add_apply, blockMonomial_apply, blockMonomial_apply, blockMonomial_apply]
  by_cases hS : blk v ∈ S
  · have hT : blk v ∉ T := Finset.disjoint_left.mp hST hS
    simp [hS, hT]
  · by_cases hT : blk v ∈ T <;> simp [hS, hT]

end IsSetMultilinear

/-- A constant is set-multilinear on the empty set of blocks. -/
theorem isSetMultilinear_C (blk : σ → Fin d) (c : K) : IsSetMultilinear blk ∅ (C c) := by
  intro m hm
  refine ⟨fun i => absurd i.2 (Finset.notMem_empty _), ?_⟩
  classical
  rw [mem_support_iff, coeff_C] at hm
  obtain rfl : m = 0 := by
    by_contra h
    exact hm (ite_eq_right fun e => h e.symm)
  rw [blockMonomial]
  exact Finset.sum_of_isEmpty _

/-- A variable is set-multilinear on its own block. -/
theorem isSetMultilinear_X (blk : σ → Fin d) (v : σ) :
    IsSetMultilinear blk {blk v} (X v : MvPolynomial σ K) := by
  classical
  intro m hm
  refine ⟨fun i => ⟨v, (Finset.mem_singleton.mp i.2).symm⟩, ?_⟩
  rw [mem_support_iff, coeff_X] at hm
  obtain rfl : Finsupp.single v 1 = m := by
    by_contra h
    exact hm (ite_eq_right h)
  ext u
  rw [blockMonomial_apply, Finsupp.single_apply]
  by_cases huv : v = u
  · subst huv
    simp
  · simp [huv]

/-- The constant `1` is set-multilinear on the empty set of blocks. -/
theorem IsSetMultilinear.one (blk : σ → Fin d) :
    IsSetMultilinear blk ∅ (1 : MvPolynomial σ K) := by
  rw [← C_1]
  exact isSetMultilinear_C blk 1

/-- A finite sum of set-multilinear polynomials on `S` is set-multilinear on `S`. -/
theorem IsSetMultilinear.sum {blk : σ → Fin d} {S : Finset (Fin d)} {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial σ K} (hf : ∀ i ∈ s, IsSetMultilinear blk S (f i)) :
    IsSetMultilinear blk S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact .zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite product of set-multilinear polynomials on pairwise disjoint sets of blocks is
set-multilinear on their union. -/
theorem IsSetMultilinear.prod {blk : σ → Fin d} {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial σ K} {T : ι → Finset (Fin d)} (hT : (s : Set ι).PairwiseDisjoint T)
    (hf : ∀ i ∈ s, IsSetMultilinear blk (T i) (f i)) :
    IsSetMultilinear blk (s.biUnion T) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.biUnion_empty, Finset.prod_empty]
    exact .one blk
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    refine (hf a (Finset.mem_insert_self a s)).mul
      (ih (hT.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))
        fun i hi => hf i (Finset.mem_insert_of_mem hi)) ?_
    refine (Finset.disjoint_biUnion_right _ _ _).2 fun i hi => hT
      (Finset.mem_coe.2 (Finset.mem_insert_self a s))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) ?_
    rintro rfl
    exact ha hi


/-- **The product of set-multilinear polynomials on disjoint blocks**: a coefficient of `f * g`
on a monomial that splits along the blocks is the product of the coefficients of its two parts. -/
theorem coeff_mul_blockMonomial {blk : σ → Fin d} {A B S T : Finset (Fin d)}
    {f g : MvPolynomial σ K} (hf : IsSetMultilinear blk S f) (hg : IsSetMultilinear blk T g)
    (hST : Disjoint S T) (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T) (r : BlockChoice blk A)
    (c : BlockChoice blk B) :
    (f * g).coeff (blockMonomial blk A r + blockMonomial blk B c) =
      f.coeff (blockMonomial blk (A ∩ S) (BlockChoice.restrict Finset.inter_subset_left r) +
          blockMonomial blk (B ∩ S) (BlockChoice.restrict Finset.inter_subset_left c)) *
        g.coeff (blockMonomial blk (A ∩ T) (BlockChoice.restrict Finset.inter_subset_left r) +
          blockMonomial blk (B ∩ T) (BlockChoice.restrict Finset.inter_subset_left c)) := by
  classical
  set m := blockMonomial blk A r + blockMonomial blk B c
  set mS := blockMonomial blk (A ∩ S) (BlockChoice.restrict Finset.inter_subset_left r) +
    blockMonomial blk (B ∩ S) (BlockChoice.restrict Finset.inter_subset_left c)
  set mT := blockMonomial blk (A ∩ T) (BlockChoice.restrict Finset.inter_subset_left r) +
    blockMonomial blk (B ∩ T) (BlockChoice.restrict Finset.inter_subset_left c)
  have hmS (v : σ) : mS v = if blk v ∈ S then m v else 0 := by
    simp only [mS, m, Finsupp.add_apply, blockMonomial_inter_apply]
    split_ifs <;> simp
  have hmT (v : σ) : mT v = if blk v ∈ T then m v else 0 := by
    simp only [mT, m, Finsupp.add_apply, blockMonomial_inter_apply]
    split_ifs <;> simp
  -- `m` lives on the blocks of `S ∪ T`, so it is the sum of its two parts.
  have hm : mS + mT = m := by
    ext v
    rw [Finsupp.add_apply, hmS, hmT]
    by_cases hS : blk v ∈ S
    · rw [ite_eq_left hS, ite_eq_right (Finset.disjoint_left.mp hST hS), add_zero]
    · by_cases hT : blk v ∈ T
      · rw [ite_eq_right hS, ite_eq_left hT, zero_add]
      · have hv : blk v ∉ S ∪ T := by simp [hS, hT]
        rw [ite_eq_right hS, ite_eq_right hT, add_zero]
        simp only [m, Finsupp.add_apply, blockMonomial_apply_of_notMem _ _ (fun h => hv (hA h)),
          blockMonomial_apply_of_notMem _ _ (fun h => hv (hB h))]
  rw [coeff_mul, Finset.sum_eq_single (mS, mT)]
  · rintro ⟨p₁, p₂⟩ hp hne
    rw [Finset.mem_antidiagonal] at hp
    by_contra h
    have h₁ : p₁ ∈ f.support := mem_support_iff.mpr (left_ne_zero_of_mul h)
    have h₂ : p₂ ∈ g.support := mem_support_iff.mpr (right_ne_zero_of_mul h)
    refine hne (Prod.ext ?_ ?_) <;> ext v <;> simp only [hmS, hmT, ← hp, Finsupp.add_apply]
    · by_cases hS : blk v ∈ S
      · rw [ite_eq_left hS, hg.apply_eq_zero h₂ (Finset.disjoint_left.mp hST hS), add_zero]
      · rw [ite_eq_right hS, hf.apply_eq_zero h₁ hS]
    · by_cases hT : blk v ∈ T
      · rw [ite_eq_left hT, hf.apply_eq_zero h₁ (Finset.disjoint_right.mp hST hT), zero_add]
      · rw [ite_eq_right hT, hg.apply_eq_zero h₂ hT]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr hm) h


end MvPolynomial
