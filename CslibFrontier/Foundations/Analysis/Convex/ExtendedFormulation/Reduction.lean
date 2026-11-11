/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/ExtendedFormulation/Reduction.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# Reductions between extended formulations

This module supplies structural preservation lemmas for extended formulations
(`IsExtendedFormulation` and `extensionComplexity`), covering linear and affine images,
intersections with linear equations (and hence exposed faces of polytopes), and face/convex-hull
characterizations used in reductions from the correlation polytope
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 9].

## Main results

* `IsExtendedFormulation.inter_mulVec_eq`, `extensionComplexity_inter_mulVec_eq_le`:
  intersecting a set with linear equations `C *ᵥ x = d` adds no inequalities.
* `extensionComplexity_inter_dotProduct_eq_le`: the single-equation (exposed-face) case.
* `IsExtendedFormulation.affineImage`, `extensionComplexity_image_affine_le`,
  `extensionComplexity_image_mulVec_le`, `extensionComplexity_image_linearMap_le`:
  affine and linear images do not increase extension complexity.
* `extensionComplexity_eq_of_linearMaps`: mutual linear projections preserve extension complexity.
* `convexHull_inter_mulVec_eq`, `convexHull_inter_dotProduct_eq`:
  a valid inequality family `C *ᵥ V j ≤ d` cuts out the convex hull of the tight vertices.
* `image_affine_convexHull`: affine matrix maps commute with `convexHull`.
* `nontrivial_convexHull_range_iff`: a finite convex hull is nontrivial iff two generators differ.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.3 (Lemma 9).
-/

public section

open Matrix

section Inter

variable {K : Type*} [Semiring K] [PartialOrder K]
variable {ι σ κ τ ρ : Type*} [Fintype ι] [Fintype κ] [Finite τ]

omit [Finite τ] in
/-- Intersecting a set `Q` with linear equations `C *ᵥ x = d` preserves the inequality index type
`σ` of any extended formulation. -/
theorem IsExtendedFormulation.inter_mulVec_eq {Q : Set (ι → K)}
    {E : Matrix σ ι K} {F : Matrix σ κ K} {g : σ → K}
    {E' : Matrix τ ι K} {F' : Matrix τ κ K} {g' : τ → K}
    (hEF : IsExtendedFormulation Q E F g E' F' g') (C : Matrix ρ ι K) (d : ρ → K) :
    IsExtendedFormulation (Q ∩ {x | C *ᵥ x = d}) E F g
      (fromRows E' C) (fromRows F' (0 : Matrix ρ κ K)) (Sum.elim g' d) := by
  intro x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hEF x]
  have heq : ∀ y : κ → K,
      fromRows E' C *ᵥ x + fromRows F' (0 : Matrix ρ κ K) *ᵥ y = Sum.elim g' d ↔
        E' *ᵥ x + F' *ᵥ y = g' ∧ C *ᵥ x = d := fun y => by
    have hsum : fromRows E' C *ᵥ x + fromRows F' (0 : Matrix ρ κ K) *ᵥ y =
        Sum.elim (E' *ᵥ x + F' *ᵥ y) (C *ᵥ x) := by
      ext (i | j) <;> simp only [fromRows_mulVec, zero_mulVec, Pi.add_apply, Pi.zero_apply,
        add_zero, Sum.elim_inl, Sum.elim_inr]
    rw [hsum, Sum.elim_eq_iff]
  simp_rw [heq]
  exact ⟨fun ⟨⟨y, hy, hy'⟩, hCx⟩ => ⟨y, hy, hy', hCx⟩,
    fun ⟨y, hy, hy', hCx⟩ => ⟨⟨y, hy, hy'⟩, hCx⟩⟩

/-- Intersecting with linear equations `C *ᵥ x = d` does not increase extension complexity. -/
theorem extensionComplexity_inter_mulVec_eq_le [Finite ρ] (Q : Set (ι → K))
    (C : Matrix ρ ι K) (d : ρ → K) :
    extensionComplexity (Q ∩ {x | C *ᵥ x = d}) ≤ extensionComplexity Q :=
  le_extensionComplexity_iff.2 fun r ⟨_, _, _, _, _, _, _, _, hEF⟩ => by
    simpa only [Fintype.card_fin] using (hEF.inter_mulVec_eq C d).extensionComplexity_le

/-- Intersecting with a single hyperplane `c ⬝ᵥ x = δ` does not increase extension complexity;
for valid inequalities `c ⬝ᵥ x ≤ δ` this is [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 9 (ii)]. -/
theorem extensionComplexity_inter_dotProduct_eq_le (Q : Set (ι → K)) (c : ι → K) (δ : K) :
    extensionComplexity (Q ∩ {x | c ⬝ᵥ x = δ}) ≤ extensionComplexity Q := by
  have hset : {x : ι → K | c ⬝ᵥ x = δ} = {x | Matrix.of (fun _ : Unit => c) *ᵥ x = fun _ => δ} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩
  rw [hset]
  exact extensionComplexity_inter_mulVec_eq_le Q _ _

end Inter

section AffineImage

variable {K : Type*} [Ring K] [PartialOrder K]
variable {ι ν σ κ τ : Type*} [Fintype ι] [Fintype ν] [Fintype κ] [Finite τ]

omit [Finite τ] in
/-- An extended formulation of `Q` lifts to an extended formulation of any affine image
`(fun z => T *ᵥ z + t) '' Q` with the exact same inequality index type `σ`. -/
theorem IsExtendedFormulation.affineImage [DecidableEq ι] {Q : Set (ν → K)}
    {E : Matrix σ ν K} {F : Matrix σ κ K} {g : σ → K}
    {E' : Matrix τ ν K} {F' : Matrix τ κ K} {g' : τ → K}
    (hEF : IsExtendedFormulation Q E F g E' F' g') (T : Matrix ι ν K) (t : ι → K) :
    IsExtendedFormulation ((fun z => T *ᵥ z + t) '' Q) (0 : Matrix σ ι K) (fromCols E F) g
      (fromRows (-1 : Matrix ι ι K) (0 : Matrix τ ι K))
      (fromBlocks T (0 : Matrix ι κ K) E' F') (Sum.elim (-t) g') := by
  intro x
  rw [Set.mem_image]
  have hblk : ∀ (z : ν → K) (y : κ → K),
      (0 : Matrix σ ι K) *ᵥ x + fromCols E F *ᵥ Sum.elim z y = E *ᵥ z + F *ᵥ y := by
    intro z y
    rw [zero_mulVec, zero_add, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have heq_blk : ∀ (z : ν → K) (y : κ → K),
      fromRows (-1 : Matrix ι ι K) (0 : Matrix τ ι K) *ᵥ x +
        fromBlocks T (0 : Matrix ι κ K) E' F' *ᵥ Sum.elim z y =
          Sum.elim (-x + T *ᵥ z) (E' *ᵥ z + F' *ᵥ y) := by
    intro z y
    ext (i | j) <;> simp only [fromRows_mulVec, neg_mulVec, one_mulVec, zero_mulVec,
      fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, Pi.zero_apply, add_zero, zero_add]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hy'⟩ := (hEF z).1 hz
    refine ⟨Sum.elim z y, ?_, ?_⟩
    · rwa [hblk]
    · rw [heq_blk, hy', Sum.elim_eq_iff]
      refine ⟨?_, rfl⟩
      ext i
      simp only [Pi.add_apply, Pi.neg_apply]
      abel
  · rintro ⟨w, hw, hw'⟩
    rw [← Sum.elim_comp_inl_inr w, hblk] at hw
    rw [← Sum.elim_comp_inl_inr w, heq_blk, Sum.elim_eq_iff] at hw'
    refine ⟨w ∘ Sum.inl, (hEF _).2 ⟨w ∘ Sum.inr, hw, hw'.2⟩, ?_⟩
    ext i
    have hi := congrFun hw'.1 i
    simp only [Pi.add_apply, Pi.neg_apply] at hi ⊢
    calc
      (T *ᵥ (w ∘ Sum.inl)) i + t i = x i + (-x i + (T *ᵥ (w ∘ Sum.inl)) i) + t i := by abel
      _ = x i + (-t i) + t i := by rw [hi]
      _ = x i := by abel

/-- An affine image does not increase extension complexity
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 9 (i)]. -/
theorem extensionComplexity_image_affine_le (Q : Set (ν → K)) (T : Matrix ι ν K) (t : ι → K) :
    extensionComplexity ((fun z => T *ᵥ z + t) '' Q) ≤ extensionComplexity Q := by
  classical
  exact le_extensionComplexity_iff.2 fun r ⟨_, _, _, _, _, _, _, _, hEF⟩ => by
    simpa only [Fintype.card_fin] using (hEF.affineImage T t).extensionComplexity_le

/-- A linear matrix image does not increase extension complexity. -/
theorem extensionComplexity_image_mulVec_le (Q : Set (ν → K)) (T : Matrix ι ν K) :
    extensionComplexity ((fun z => T *ᵥ z) '' Q) ≤ extensionComplexity Q := by
  simpa only [add_zero] using extensionComplexity_image_affine_le Q T 0

end AffineImage

section LinearMap

variable {K : Type*} [CommRing K] [PartialOrder K]
variable {ι ν : Type*} [Fintype ι] [Fintype ν]

/-- A linear map image does not increase extension complexity
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 9 (i)]. -/
theorem extensionComplexity_image_linearMap_le (Q : Set (ν → K)) (f : (ν → K) →ₗ[K] (ι → K)) :
    extensionComplexity (f '' Q) ≤ extensionComplexity Q := by
  classical
  have him : f '' Q = (fun z => LinearMap.toMatrix' f *ᵥ z) '' Q :=
    Set.image_congr fun z _ => (LinearMap.toMatrix'_mulVec f z).symm
  rw [him]
  exact extensionComplexity_image_mulVec_le Q (LinearMap.toMatrix' f)

/-- If two sets are mutual linear images of each other, they have the same extension
complexity. -/
theorem extensionComplexity_eq_of_linearMaps {P : Set (ι → K)} {Q : Set (ν → K)}
    (f : (ν → K) →ₗ[K] (ι → K)) (g : (ι → K) →ₗ[K] (ν → K))
    (hf : f '' Q = P) (hg : g '' P = Q) :
    extensionComplexity P = extensionComplexity Q :=
  le_antisymm (hf ▸ extensionComplexity_image_linearMap_le Q f)
    (hg ▸ extensionComplexity_image_linearMap_le P g)

end LinearMap

section ConvexHull

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι ν ρ : Type*}

omit [IsStrictOrderedRing K] in
/-- An affine matrix map commutes with `convexHull`. -/
theorem image_affine_convexHull (T : Matrix ι ν K) [Fintype ν] (t : ι → K) (S : Set (ν → K)) :
    (fun z => T *ᵥ z + t) '' convexHull K S =
      convexHull K ((fun z => T *ᵥ z + t) '' S) := by
  let φ : (ν → K) →ᵃ[K] (ι → K) :=
    { toFun := fun z => T *ᵥ z + t
      linear := T.mulVecLin
      map_vadd' := fun p v => by
        simp only [vadd_eq_add, mulVecLin_apply, mulVec_add]
        abel }
  exact φ.image_convexHull S

omit [IsStrictOrderedRing K] in
/-- A finite convex hull `conv (range V)` is nontrivial iff `V` takes two distinct values. -/
theorem nontrivial_convexHull_range_iff {V : ν → ι → K} :
    (convexHull K (Set.range V)).Nontrivial ↔ ∃ j₁ j₂, V j₁ ≠ V j₂ := by
  constructor
  · intro hP
    by_contra! h
    refine hP.not_subsingleton ?_
    have hsub : (Set.range V).Subsingleton := by
      rintro _ ⟨j₁, rfl⟩ _ ⟨j₂, rfl⟩
      exact h j₁ j₂
    simpa only [hsub.convex.convexHull_eq] using hsub
  · rintro ⟨j₁, j₂, hj⟩
    exact ⟨V j₁, subset_convexHull K _ ⟨j₁, rfl⟩, V j₂, subset_convexHull K _ ⟨j₂, rfl⟩, hj⟩

/-- If `C *ᵥ V j ≤ d` holds on all generators `V j`, then intersecting `conv (range V)` with
the equality subspace `C *ᵥ x = d` cuts out the convex hull of the tight generators. -/
theorem convexHull_inter_mulVec_eq [Fintype ι] {V : ν → ι → K} {C : Matrix ρ ι K} {d : ρ → K}
    (hV : ∀ j, C *ᵥ V j ≤ d) :
    convexHull K (Set.range V) ∩ {x | C *ᵥ x = d} = convexHull K (V '' {j | C *ᵥ V j = d}) := by
  classical
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx, hCx⟩
    rw [mem_convexHull_iff_exists_fintype] at hx
    obtain ⟨γ, _, w, z, hw0, hw1, hz, rfl⟩ := hx
    have hzV : ∀ k, ∃ j, V j = z k := fun k => hz k
    choose idx hidx using hzV
    have hslack : ∀ i : ρ, ∑ k : γ, w k * (d i - C i ⬝ᵥ V (idx k)) = 0 := fun i => by
      have hCxi := congrFun hCx i
      simp only [mulVec, dotProduct_sum, dotProduct_smul, smul_eq_mul] at hCxi
      calc
        ∑ k : γ, w k * (d i - C i ⬝ᵥ V (idx k))
            = (∑ k : γ, w k) * d i - ∑ k : γ, w k * (C i ⬝ᵥ z k) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, hidx]
        _ = d i - d i := by rw [hw1, one_mul, hCxi]
        _ = 0 := sub_self _
    have htight : ∀ k, w k ≠ 0 → C *ᵥ V (idx k) = d := fun k hwk => by
      ext i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun k' _ =>
        mul_nonneg (hw0 k') (sub_nonneg.2 (hV (idx k') i))).1 (hslack i) k (Finset.mem_univ k)
      rcases mul_eq_zero.1 hterm with hwz | hsub
      · exact absurd hwz hwk
      · exact (sub_eq_zero.1 hsub).symm
    let S : Finset γ := Finset.univ.filter fun k => w k ≠ 0
    have hSw1 : ∑ k ∈ S, w k = 1 := by
      rw [← hw1]
      exact Finset.sum_filter_ne_zero Finset.univ
    have hSx : S.centerMass w z = ∑ k : γ, w k • z k := by
      rw [Finset.centerMass_eq_of_sum_1 _ _ hSw1]
      exact Finset.sum_filter_of_ne fun k _ hnz hwk => hnz (by rw [hwk, zero_smul])
    rw [← hSx]
    exact S.centerMass_mem_convexHull (fun k _ => hw0 k) (hSw1 ▸ zero_lt_one)
      fun k hk => ⟨idx k, htight k (Finset.mem_filter.1 hk).2, hidx k⟩
  · refine convexHull_min ?_ ((convex_convexHull K _).inter ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨subset_convexHull K _ ⟨j, rfl⟩, hj⟩
    · intro x hx y hy a b _ _ hab
      simp only [Set.mem_ofPred_eq, mulVec_add, mulVec_smul] at hx hy ⊢
      rw [hx, hy, ← add_smul, hab, one_smul]

/-- Single-hyperplane specialization of `convexHull_inter_mulVec_eq`. -/
theorem convexHull_inter_dotProduct_eq [Fintype ι] {V : ν → ι → K} {c : ι → K} {δ : K}
    (hV : ∀ j, c ⬝ᵥ V j ≤ δ) :
    convexHull K (Set.range V) ∩ {x | c ⬝ᵥ x = δ} = convexHull K (V '' {j | c ⬝ᵥ V j = δ}) := by
  have hV' : ∀ j, Matrix.of (fun _ : Unit => c) *ᵥ V j ≤ fun _ => δ := fun j _ => hV j
  have h1 : {x : ι → K | c ⬝ᵥ x = δ} = {x | Matrix.of (fun _ : Unit => c) *ᵥ x = fun _ => δ} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩
  have h2 : {j : ν | c ⬝ᵥ V j = δ} = {j | Matrix.of (fun _ : Unit => c) *ᵥ V j = fun _ => δ} := by
    ext j
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩
  rw [h1, h2]
  exact convexHull_inter_mulVec_eq hV'

end ConvexHull

section ExponentialHelpers

/-- Converting `(3 ^ m : ℕ∞) ≤ 2 ^ m * extensionComplexity P` into an explicit ceiling lower
bound `⌈(3 / 2) ^ m⌉ ≤ extensionComplexity P`. -/
theorem ceil_three_div_two_pow_le_of_mul_le_extensionComplexity
    {K : Type*} [Semiring K] [PartialOrder K] {ι : Type*} [Fintype ι] {P : Set (ι → K)} {m : ℕ}
    (hm : ((3 ^ m : ℕ) : ℕ∞) ≤ (2 ^ m : ℕ∞) * extensionComplexity P) :
    (((3 ^ m + 2 ^ m - 1) / 2 ^ m : ℕ) : ℕ∞) ≤ extensionComplexity P := by
  refine le_extensionComplexity_iff.2 fun r hr => ?_
  have hr' : extensionComplexity P ≤ r := by
    obtain ⟨_, _, _, _, _, _, _, _, hEF⟩ := hr
    simpa only [Fintype.card_fin] using hEF.extensionComplexity_le
  have hnat : 3 ^ m ≤ 2 ^ m * r := by exact_mod_cast hm.trans (mul_le_mul_right hr' _)
  have hpos : 0 < 2 ^ m := by positivity
  exact_mod_cast Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hpos).2 (by
    rw [Nat.add_one_mul, mul_comm r]
    omega))

/-- Field-valued exponential lower bound derived from `3 ^ m ≤ 2 ^ m * extensionComplexity P`:
any extended formulation of `P` with `r` inequalities satisfies `(3 / 2 : F) ^ m ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_mul_le
    {K F : Type*} [Semiring K] [PartialOrder K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {ι : Type*} [Fintype ι] {P : Set (ι → K)} {m r : ℕ}
    (hm : ((3 ^ m : ℕ) : ℕ∞) ≤ (2 ^ m : ℕ∞) * extensionComplexity P)
    (hr : HasExtendedFormulation P r) :
    (3 / 2 : F) ^ m ≤ r := by
  have hr' : extensionComplexity P ≤ r := by
    obtain ⟨_, _, _, _, _, _, _, _, hEF⟩ := hr
    simpa only [Fintype.card_fin] using hEF.extensionComplexity_le
  have hnat : 3 ^ m ≤ r * 2 ^ m := by
    simpa only [mul_comm] using
      (by exact_mod_cast hm.trans (mul_le_mul_right hr' _) : 3 ^ m ≤ 2 ^ m * r)
  have hcast : ((3 : F) ^ m) ≤ (r : F) * (2 : F) ^ m := by exact_mod_cast hnat
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact hcast

end ExponentialHelpers
