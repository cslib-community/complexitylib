/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Polytope.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import CslibFrontier.Foundations.LinearAlgebra.Matrix.FourierMotzkin
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact convex polytopes in finite-dimensional normed spaces

This module develops compact convex polytopes in finite-dimensional real normed spaces,
establishing the equivalence between vertex-hull representations (`IsVPolytope`) and bounded
finite half-space intersections (`IsHPolytope`), along with faces (`IsPolytopeFace`), vertex
centroids (`vertexCentroid`), and closure under intersections, products, affine images, and affine
preimages.

## Main definitions

* `Cslib.Polyhedra.IsVPolytope`: a set equal to the convex hull of finitely many points.
* `Cslib.Polyhedra.IsHPolytope`: a bounded intersection of finitely many closed half-spaces.
* `Cslib.Polyhedra.IsPolytope`: compact convex polytopes (`IsVPolytope`).
* `Cslib.Polyhedra.IsPolytopeFace`: convex extreme subsets of a set.
* `Cslib.Polyhedra.vertexCentroid`: the centroid of the extreme points of a polytope.

## Main results

* `Cslib.Polyhedra.isHPolytope_iff_isVPolytope`: **Weyl–Minkowski theorem** for bounded polytopes,
  proved via Fourier–Motzkin elimination (`Matrix.FourierMotzkin.exists_projection`) and
  Krein–Milman (`closure_convexHull_extremePoints`).
* `Cslib.Polyhedra.IsPolytope.inter`, `Cslib.Polyhedra.IsPolytope.prod`,
  `Cslib.Polyhedra.IsPolytope.image`, `Cslib.Polyhedra.IsPolytope.preimage_inter`,
  `Cslib.Polyhedra.IsPolytope.pi`: closure of compact convex polytopes.
* `Cslib.Polyhedra.IsPolytopeFace.isExposed`, `Cslib.Polyhedra.IsPolytopeFace.isPolytope`: faces of
  polytopes are exposed and are themselves polytopes.
* `Cslib.Polyhedra.exists_isPolytopeFace_inter_eq`,
  `Cslib.Polyhedra.exists_isPolytopeFace_prod_eq`,
  `Cslib.Polyhedra.exists_isPolytopeFace_preimage_inter_eq`: characterization of faces of
  intersections, products, and affine preimage intersections.
* `Cslib.Polyhedra.vertexCentroid_notMem_of_ssubset`,
  `Cslib.Polyhedra.vertexCentroid_notMem_affineSpan_of_ssubset`: the vertex centroid of a polytope
  lies outside every proper face and its affine span.
* `Cslib.Polyhedra.exists_isPolytopeFace_ssubset_of_ne_vertexCentroid`: ray projection from the
  vertex centroid onto a proper face.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
-/

public section

namespace Cslib.Polyhedra

open Set Finset
open scoped Matrix

section BasicDefs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A set in `E` is a **V-polytope** if it is the convex hull of a finite set of points. -/
@[expose] def IsVPolytope (P : Set E) : Prop :=
  ∃ S : Set E, S.Finite ∧ P = convexHull ℝ S

/-- A set in `E` is a bounded **H-polytope** if it is bounded and cut out by finitely many affine
inequalities `ℓ x ≤ 0`. -/
@[expose] def IsHPolytope (P : Set E) : Prop :=
  Bornology.IsBounded P ∧ ∃ L : Set (E →ᵃ[ℝ] ℝ), L.Finite ∧ P = {x | ∀ ℓ ∈ L, ℓ x ≤ 0}

/-- A **compact convex polytope** in `E` (`IsVPolytope`, equivalent to `IsHPolytope` in finite
dimensions). -/
@[expose] def IsPolytope (P : Set E) : Prop :=
  IsVPolytope P

/-- A **face** of a convex set `P` is a convex extreme subset of `P`. For polytopes, this coincides
with exposed faces (`IsPolytopeFace.isExposed`). -/
@[expose] def IsPolytopeFace (P F : Set E) : Prop :=
  IsExtreme ℝ P F ∧ Convex ℝ F

/-- The **vertex centroid** of a polytope `P`, defined as the centroid of its finite set of extreme
points (or `0` when `P.extremePoints ℝ` is infinite). -/
noncomputable def vertexCentroid (P : Set E) : E :=
  open Classical in
  if h : (P.extremePoints ℝ).Finite then h.toFinset.centroid ℝ id else 0

/-! ### Basic properties of V-polytopes and H-polytopes -/

theorem isVPolytope_empty : IsVPolytope (∅ : Set E) :=
  ⟨∅, finite_empty, convexHull_empty.symm⟩

theorem isVPolytope_singleton (x : E) : IsVPolytope ({x} : Set E) :=
  ⟨{x}, finite_singleton x, (convexHull_singleton x).symm⟩

theorem isVPolytope_convexHull {S : Set E} (hS : S.Finite) : IsVPolytope (convexHull ℝ S) :=
  ⟨S, hS, rfl⟩

theorem IsVPolytope.convex {P : Set E} (hP : IsVPolytope P) : Convex ℝ P := by
  rcases hP with ⟨S, _, rfl⟩
  exact convex_convexHull ℝ S

theorem IsVPolytope.isCompact {P : Set E} (hP : IsVPolytope P) : IsCompact P := by
  rcases hP with ⟨S, hS, rfl⟩
  exact hS.isCompact_convexHull ℝ

theorem IsVPolytope.isClosed {P : Set E} (hP : IsVPolytope P) : IsClosed P :=
  hP.isCompact.isClosed

theorem IsVPolytope.isBounded {P : Set E} (hP : IsVPolytope P) : Bornology.IsBounded P :=
  hP.isCompact.isBounded

theorem IsVPolytope.image {P : Set E} (hP : IsVPolytope P) (f : E →ᵃ[ℝ] F) :
    IsVPolytope (f '' P) := by
  rcases hP with ⟨S, hS, rfl⟩
  exact ⟨f '' S, hS.image f, f.image_convexHull S⟩

theorem IsVPolytope.prod {P : Set E} {Q : Set F} (hP : IsVPolytope P) (hQ : IsVPolytope Q) :
    IsVPolytope (P ×ˢ Q) := by
  rcases hP with ⟨S, hS, rfl⟩
  rcases hQ with ⟨T, hT, rfl⟩
  exact ⟨S ×ˢ T, hS.prod hT, (convexHull_prod S T).symm⟩

theorem isPolytope_empty : IsPolytope (∅ : Set E) := isVPolytope_empty

theorem isPolytope_singleton (x : E) : IsPolytope ({x} : Set E) := isVPolytope_singleton x

theorem isPolytope_convexHull {S : Set E} (hS : S.Finite) : IsPolytope (convexHull ℝ S) :=
  isVPolytope_convexHull hS

theorem IsPolytope.convex {P : Set E} (hP : IsPolytope P) : Convex ℝ P :=
  IsVPolytope.convex hP

theorem IsPolytope.isCompact {P : Set E} (hP : IsPolytope P) : IsCompact P :=
  IsVPolytope.isCompact hP

theorem IsPolytope.isClosed {P : Set E} (hP : IsPolytope P) : IsClosed P :=
  IsVPolytope.isClosed hP

theorem IsPolytope.isBounded {P : Set E} (hP : IsPolytope P) : Bornology.IsBounded P :=
  IsVPolytope.isBounded hP

theorem IsPolytope.prod {P : Set E} {Q : Set F} (hP : IsPolytope P) (hQ : IsPolytope Q) :
    IsPolytope (P ×ˢ Q) :=
  IsVPolytope.prod hP hQ

theorem IsPolytope.image {P : Set E} (hP : IsPolytope P) (f : E →ᵃ[ℝ] F) :
    IsPolytope (f '' P) :=
  IsVPolytope.image hP f

theorem IsPolytope.pi {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    {P : ∀ i, Set (G i)} (hP : ∀ i, IsPolytope (P i)) :
    IsPolytope (Set.univ.pi P) := by
  classical
  choose S hS hPeq using hP
  refine ⟨Set.univ.pi S, Set.Finite.pi hS, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact mem_convexHull_pi fun i _ => hPeq i ▸ hx i trivial
  · refine convexHull_min (Set.pi_mono fun i _ => hPeq i ▸ subset_convexHull ℝ _) ?_
    exact convex_pi fun i _ => hPeq i ▸ convex_convexHull ℝ (S i)

theorem isHPolytope_empty : IsHPolytope (∅ : Set E) := by
  refine ⟨Bornology.isBounded_empty, {AffineMap.const ℝ E (1 : ℝ)}, finite_singleton _, ?_⟩
  ext x
  simp only [mem_empty_iff_false, mem_ofPred_eq, mem_singleton_iff, forall_eq,
    AffineMap.const_apply, false_iff, not_le]
  exact zero_lt_one

private lemma affineMap_eval_sum_smul (ℓ : E →ᵃ[ℝ] ℝ) {S : Finset E} {w : E → ℝ}
    (hw : ∑ v ∈ S, w v = 1) :
    ℓ (∑ v ∈ S, w v • v) = ∑ v ∈ S, w v * ℓ v := by
  have h : ℓ (S.affineCombination ℝ id w) = S.affineCombination ℝ (ℓ ∘ id) w :=
    Finset.map_affineCombination S id w hw ℓ
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw, Function.comp_apply,
    id_eq, smul_eq_mul] using h

/-- Any finite or infinite intersection of closed affine half-spaces is convex. -/
theorem convex_setOf_forall_le (L : Set (E →ᵃ[ℝ] ℝ)) :
    Convex ℝ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} := by
  have heq : {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} = ⋂ ℓ ∈ L, ℓ ⁻¹' Set.Iic (0 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [heq]
  exact convex_iInter fun ℓ => convex_iInter fun _ => (convex_Iic (0 : ℝ)).affine_preimage ℓ

theorem IsHPolytope.convex {P : Set E} (hP : IsHPolytope P) : Convex ℝ P := by
  rcases hP with ⟨_, L, _, rfl⟩
  exact convex_setOf_forall_le L

theorem IsHPolytope.inter {P Q : Set E} (hP : IsHPolytope P) (hQ : IsHPolytope Q) :
    IsHPolytope (P ∩ Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨_, LQ, hLQ, rfl⟩
  refine ⟨hbP.subset inter_subset_left, LP ∪ LQ, hLP.union hLQ, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union]
  exact ⟨fun ⟨h1, h2⟩ ℓ h => h.elim (h1 ℓ) (h2 ℓ),
    fun h => ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun ℓ hℓ => h ℓ (.inr hℓ)⟩⟩

theorem IsHPolytope.preimage_inter {P : Set E} {Q : Set F} (hP : IsHPolytope P)
    (hQ : IsHPolytope Q) (f : E →ᵃ[ℝ] F) : IsHPolytope (P ∩ f ⁻¹' Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨_, LQ, hLQ, rfl⟩
  refine ⟨hbP.subset inter_subset_left, LP ∪ (fun m : F →ᵃ[ℝ] ℝ => m.comp f) '' LQ,
    hLP.union (hLQ.image _), ?_⟩
  ext x
  simp only [mem_inter_iff, Set.mem_preimage, mem_ofPred_eq, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hxP, hxQ⟩ ℓ (hℓ | ⟨m, hm, rfl⟩)
    · exact hxP ℓ hℓ
    · exact hxQ m hm
  · intro h
    refine ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun m hm => h (m.comp f) (.inr ⟨m, hm, rfl⟩)⟩

theorem IsHPolytope.prod {P : Set E} {Q : Set F} (hP : IsHPolytope P) (hQ : IsHPolytope Q) :
    IsHPolytope (P ×ˢ Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨hbQ, LQ, hLQ, rfl⟩
  refine ⟨hbP.prod hbQ,
    (fun ℓ : E →ᵃ[ℝ] ℝ => ℓ.comp AffineMap.fst) '' LP ∪
      (fun m : F →ᵃ[ℝ] ℝ => m.comp AffineMap.snd) '' LQ,
    (hLP.image _).union (hLQ.image _), ?_⟩
  ext ⟨x, y⟩
  simp only [mem_prod, mem_ofPred_eq, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hx, hy⟩ ℓ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact hx a ha
    · exact hy b hb
  · intro h
    refine ⟨fun a ha => h (a.comp AffineMap.fst) (.inl ⟨a, ha, rfl⟩),
      fun b hb => h (b.comp AffineMap.snd) (.inr ⟨b, hb, rfl⟩)⟩

/-! ### Basic properties of faces -/

theorem IsPolytopeFace.subset {P F : Set E} (h : IsPolytopeFace P F) : F ⊆ P :=
  h.1.subset

theorem IsPolytopeFace.convex {P F : Set E} (h : IsPolytopeFace P F) : Convex ℝ F :=
  h.2

theorem IsPolytopeFace.isExtreme {P F : Set E} (h : IsPolytopeFace P F) : IsExtreme ℝ P F :=
  h.1

@[refl]
theorem IsPolytopeFace.refl {P : Set E} (hP : Convex ℝ P) : IsPolytopeFace P P :=
  ⟨IsExtreme.refl ℝ P, hP⟩

@[trans]
theorem IsPolytopeFace.trans {P Q R : Set E} (hPQ : IsPolytopeFace P Q) (hQR : IsPolytopeFace Q R) :
    IsPolytopeFace P R :=
  ⟨hPQ.1.trans hQR.1, hQR.2⟩

theorem IsPolytopeFace.inter {P F₁ F₂ : Set E} (h₁ : IsPolytopeFace P F₁)
    (h₂ : IsPolytopeFace P F₂) : IsPolytopeFace P (F₁ ∩ F₂) :=
  ⟨h₁.1.inter h₂.1, h₁.2.inter h₂.2⟩

theorem IsPolytopeFace.empty {P : Set E} : IsPolytopeFace P ∅ :=
  ⟨⟨empty_subset P, fun _ _ _ _ _ hz => False.elim hz⟩, convex_empty⟩

theorem IsPolytopeFace.mono {P Q R : Set E} (hPR : IsPolytopeFace P R) (hQP : Q ⊆ P)
    (hRQ : R ⊆ Q) : IsPolytopeFace Q R :=
  ⟨hPR.1.mono hQP hRQ, hPR.2⟩

theorem IsPolytopeFace.inter_inter {P₁ P₂ F₁ F₂ : Set E} (h₁ : IsPolytopeFace P₁ F₁)
    (h₂ : IsPolytopeFace P₂ F₂) : IsPolytopeFace (P₁ ∩ P₂) (F₁ ∩ F₂) := by
  refine ⟨⟨inter_subset_inter h₁.1.subset h₂.1.subset, fun x hx y hy z hz hzx => ?_⟩,
    h₁.2.inter h₂.2⟩
  exact ⟨h₁.1.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hzx,
    h₂.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 hzx⟩

theorem IsPolytopeFace.prod {P₁ : Set E} {P₂ : Set F} {F₁ : Set E} {F₂ : Set F}
    (h₁ : IsPolytopeFace P₁ F₁) (h₂ : IsPolytopeFace P₂ F₂) :
    IsPolytopeFace (P₁ ×ˢ P₂) (F₁ ×ˢ F₂) := by
  refine ⟨⟨prod_mono h₁.1.subset h₂.1.subset, fun x hx y hy z hz hzx => ?_⟩, h₁.2.prod h₂.2⟩
  rcases hzx with ⟨a, b, ha, hb, hab, rfl⟩
  exact ⟨h₁.1.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 ⟨a, b, ha, hb, hab, rfl⟩,
    h₂.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 ⟨a, b, ha, hb, hab, rfl⟩⟩

theorem IsPolytopeFace.preimage {P : Set E} {Q G : Set F} (hP : Convex ℝ P) (f : E →ᵃ[ℝ] F)
    (h : IsPolytopeFace Q G) : IsPolytopeFace (P ∩ f ⁻¹' Q) (P ∩ f ⁻¹' G) := by
  refine ⟨⟨inter_subset_inter_right P (preimage_mono h.1.subset),
    fun x hx y hy z hz hzx => ?_⟩, hP.inter (h.2.affine_preimage f)⟩
  refine ⟨hx.1, h.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 ?_⟩
  have hmem : f z ∈ f '' openSegment ℝ x y := mem_image_of_mem f hzx
  rwa [image_openSegment _ f] at hmem

theorem IsPolytopeFace.left_mem_of_smul_add_mem {P F : Set E} (hPF : IsPolytopeFace P F)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {a y : E} (ha : a ∈ P) (hy : y ∈ P)
    (hmem : c • a + (1 - c) • y ∈ F) : a ∈ F := by
  rcases eq_or_lt_of_le hc1 with rfl | hlt
  · simpa only [one_smul, sub_self, zero_smul, add_zero] using hmem
  · exact hPF.isExtreme.left_mem_of_mem_openSegment ha hy hmem
      ⟨c, 1 - c, hc0, sub_pos.2 hlt, add_sub_cancel c 1, rfl⟩

end BasicDefs

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
private lemma affineMap_lineMap (ℓ : E →ᵃ[ℝ] ℝ) (x y : E) (t : ℝ) :
    ℓ (AffineMap.lineMap x y t) = ℓ x + t * (ℓ y - ℓ x) := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  ring

theorem IsHPolytope.isClosed {P : Set E} (hP : IsHPolytope P) : IsClosed P := by
  rcases hP with ⟨_, L, _, rfl⟩
  have hsub : {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} = ⋂ ℓ ∈ L, {x : E | ℓ x ≤ 0} := by
    ext x; simp
  rw [hsub]
  refine isClosed_biInter fun ℓ _ => ?_
  exact isClosed_le ℓ.continuous_of_finiteDimensional continuous_const

theorem IsHPolytope.isCompact {P : Set E} (hP : IsHPolytope P) : IsCompact P :=
  Metric.isCompact_of_isClosed_isBounded hP.isClosed hP.1

omit [FiniteDimensional ℝ E] in
private lemma finite_extremePoints_of_isHPolytope {P : Set E} (hP : IsHPolytope P) :
    (P.extremePoints ℝ).Finite := by
  classical
  rcases hP with ⟨_, L, hL, rfl⟩
  set Lf : Finset (E →ᵃ[ℝ] ℝ) := hL.toFinset
  let active : E → Finset (E →ᵃ[ℝ] ℝ) := fun x => Lf.filter (fun ℓ => ℓ x = 0)
  have hsub : ∀ x ∈ Set.extremePoints ℝ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0},
      active x ∈ Lf.powerset := fun x _ =>
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hinj : InjOn active (Set.extremePoints ℝ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0}) := by
    intro x hx y hy hxy
    by_contra hne
    set strict : Finset (E →ᵃ[ℝ] ℝ) := Lf.filter (fun ℓ => ℓ x < 0)
    let ε : ℝ :=
      if hs : strict.Nonempty then
        min (1 / 2) (strict.inf' hs fun ℓ => (-ℓ x) / (|ℓ y - ℓ x| + 1))
      else 1 / 2
    have hε_pos : 0 < ε := by
      by_cases hs : strict.Nonempty
      · simp only [ε, dite_eq_left hs, lt_min_iff]
        refine ⟨by norm_num, (Finset.lt_inf'_iff hs).2 fun ℓ hℓ => ?_⟩
        have hlt : ℓ x < 0 := (Finset.mem_filter.1 hℓ).2
        exact div_pos (neg_pos.2 hlt) (by positivity)
      · simp only [ε, dite_eq_right hs]; norm_num
    let x₁ : E := AffineMap.lineMap x y (-ε)
    let x₂ : E := AffineMap.lineMap x y ε
    have hmem : ∀ (t : ℝ), |t| ≤ ε → ∀ ℓ ∈ L, ℓ (AffineMap.lineMap x y t) ≤ 0 := by
      intro t ht ℓ hℓ
      have hℓLf : ℓ ∈ Lf := hL.mem_toFinset.2 hℓ
      have hxℓ : ℓ x ≤ 0 := hx.1 ℓ hℓ
      rw [affineMap_lineMap]
      rcases hxℓ.lt_or_eq with hlt | heq
      · have hstrict : ℓ ∈ strict := Finset.mem_filter.2 ⟨hℓLf, hlt⟩
        have hs : strict.Nonempty := ⟨ℓ, hstrict⟩
        have hε_le : ε ≤ (-ℓ x) / (|ℓ y - ℓ x| + 1) := by
          dsimp only [ε]
          rw [dite_eq_left hs]
          exact (min_le_right (1 / 2) _).trans (Finset.inf'_le _ hstrict)
        have hbound : |t| * |ℓ y - ℓ x| ≤ -ℓ x := by
          have h1 : |t| * (|ℓ y - ℓ x| + 1) ≤ (-ℓ x) := by
            calc |t| * (|ℓ y - ℓ x| + 1) ≤ ε * (|ℓ y - ℓ x| + 1) :=
                  mul_le_mul_of_nonneg_right ht (by positivity)
              _ ≤ ((-ℓ x) / (|ℓ y - ℓ x| + 1)) * (|ℓ y - ℓ x| + 1) :=
                  mul_le_mul_of_nonneg_right hε_le (by positivity)
              _ = -ℓ x := div_mul_cancel₀ _ (by positivity)
          linarith [abs_nonneg t]
        have hle_abs : t * (ℓ y - ℓ x) ≤ |t| * |ℓ y - ℓ x| := by
          rw [← abs_mul]
          exact le_abs_self _
        linarith
      · have hactx : ℓ ∈ active x := Finset.mem_filter.2 ⟨hℓLf, heq⟩
        have hacty : ℓ ∈ active y := hxy ▸ hactx
        have hyℓ : ℓ y = 0 := (Finset.mem_filter.1 hacty).2
        rw [heq, hyℓ, sub_zero, mul_zero, add_zero]
    have hx₁ : x₁ ∈ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} := hmem (-ε) (by rw [abs_neg, abs_of_pos hε_pos])
    have hx₂ : x₂ ∈ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} := hmem ε (by rw [abs_of_pos hε_pos])
    have hmid : x ∈ openSegment ℝ x₁ x₂ := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [x₁, x₂, AffineMap.lineMap_apply_module]
      module
    have heq₁ : x₁ = x := ((mem_extremePoints.1 hx).2 x₁ hx₁ x₂ hx₂ hmid).1
    have hdiff : (-ε) • (y -ᵥ x) = 0 := by
      have : x₁ -ᵥ x = (-ε) • (y -ᵥ x) := by
        simp only [x₁, AffineMap.lineMap_apply_module, vsub_eq_sub]
        module
      rw [heq₁, vsub_self] at this
      exact this.symm
    rcases smul_eq_zero.1 hdiff with hε0 | hyx
    · linarith
    · exact hne (sub_eq_zero.1 hyx).symm
  exact (Finset.finite_toSet Lf.powerset).of_injOn hsub hinj

/-- Every bounded H-polytope is the convex hull of its finite set of extreme points, hence a
V-polytope. -/
theorem IsHPolytope.eq_convexHull_extremePoints {P : Set E} (hP : IsHPolytope P) :
    P = convexHull ℝ (P.extremePoints ℝ) := by
  have hfin : (P.extremePoints ℝ).Finite := finite_extremePoints_of_isHPolytope hP
  have hclosed : IsClosed (convexHull ℝ (P.extremePoints ℝ)) := hfin.isClosed_convexHull ℝ
  have hkm := closure_convexHull_extremePoints hP.isCompact hP.convex
  rw [hclosed.closure_eq] at hkm
  exact hkm.symm

theorem IsHPolytope.isVPolytope {P : Set E} (hP : IsHPolytope P) : IsVPolytope P :=
  ⟨P.extremePoints ℝ, finite_extremePoints_of_isHPolytope hP, hP.eq_convexHull_extremePoints⟩

theorem IsVPolytope.isHPolytope {P : Set E} (hP : IsVPolytope P) : IsHPolytope P := by
  classical
  rcases hP with ⟨S, hS, rfl⟩
  by_cases hSne : S.Nonempty
  · refine ⟨(hS.isCompact_convexHull ℝ).isBounded, ?_⟩
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := Module.finBasis ℝ E
    let eE : E ≃ₗ[ℝ] (Fin d → ℝ) := b.equivFun
    let Sf : Finset E := hS.toFinset
    let m : ℕ := Fintype.card Sf
    let eS : Fin m ≃ Sf := (Fintype.equivFin Sf).symm
    let V : Fin m → Fin d → ℝ := fun j => eE (eS j).1
    have hmem_iff : ∀ x : E, x ∈ convexHull ℝ S ↔
        ∃ w : Fin m → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
          ∀ k : Fin d, ∑ j, w j * V j k = eE x k := by
      intro x
      rw [← hS.coe_toFinset]
      change x ∈ convexHull ℝ (Sf : Set E) ↔ _
      rw [Sf.convexHull_eq]
      constructor
      · rintro ⟨w', hw'₀, hw'₁, rfl⟩
        refine ⟨fun j => w' (eS j).1, fun j => hw'₀ _ (eS j).2, ?_, fun k => ?_⟩
        · rw [Fintype.sum_equiv eS _ (fun u : Sf => w' u.1) (fun _ => rfl)]
          exact (Finset.sum_coe_sort Sf w').trans hw'₁
        · rw [Finset.centerMass_eq_of_sum_1 _ id hw'₁, map_sum]
          simp only [Finset.sum_apply, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, V, id_eq]
          rw [Fintype.sum_equiv eS _ (fun u : Sf => w' u.1 * eE u.1 k) (fun _ => rfl)]
          exact Finset.sum_coe_sort Sf (fun u => w' u * eE u k)
      · rintro ⟨w, hw₀, hw₁, hVk⟩
        let w' : E → ℝ := fun u => if hu : u ∈ Sf then w (eS.symm ⟨u, hu⟩) else 0
        have hw'sum : ∑ u ∈ Sf, w' u = 1 := by
          rw [← Finset.sum_coe_sort Sf w']
          have := Fintype.sum_equiv eS.symm (fun u : Sf => w' u.1) w fun u => by
            simp only [w', dite_eq_left u.2]
          exact this.trans hw₁
        refine ⟨w', fun u hu => by simp only [w', dite_eq_left hu]; exact hw₀ _, hw'sum, ?_⟩
        rw [Finset.centerMass_eq_of_sum_1 _ id hw'sum]
        apply eE.injective
        ext k
        rw [map_sum]
        simp only [Finset.sum_apply, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, id_eq]
        rw [← hVk k, ← Finset.sum_coe_sort Sf (fun u => w' u * eE u k)]
        exact Fintype.sum_equiv eS.symm (fun u : Sf => w' u.1 * eE u.1 k)
          (fun j => w j * V j k) fun u => by
            simp only [w', dite_eq_left u.2, V, Equiv.apply_symm_apply]
    let ι := (Fin d ⊕ Fin d) ⊕ (Unit ⊕ Unit) ⊕ Fin m
    let A : Matrix ι (Fin m) ℝ := Matrix.of fun r j => match r with
      | .inl (.inl k) => -V j k
      | .inl (.inr k) => V j k
      | .inr (.inl (.inl ())) => 1
      | .inr (.inl (.inr ())) => -1
      | .inr (.inr j₀) => if j = j₀ then -1 else 0
    let B : Matrix ι (Fin d) ℝ := Matrix.of fun r k => match r with
      | .inl (.inl k₀) => if k = k₀ then 1 else 0
      | .inl (.inr k₀) => if k = k₀ then -1 else 0
      | .inr (.inl _) => 0
      | .inr (.inr _) => 0
    let rhs : ι → ℝ := fun r => match r with
      | .inl _ => 0
      | .inr (.inl (.inl ())) => 1
      | .inr (.inl (.inr ())) => -1
      | .inr (.inr _) => 0
    have hsys : ∀ (x : E) (w : Fin m → ℝ),
        (A *ᵥ w + B *ᵥ eE x ≤ rhs) ↔
          ((∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∀ k, ∑ j, w j * V j k = eE x k) := by
      intro x w
      constructor
      · intro h
        refine ⟨fun j => ?_, le_antisymm ?_ ?_, fun k => le_antisymm ?_ ?_⟩
        · have := h (.inr (.inr j))
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            Finset.sum_const_zero, add_zero, neg_nonpos] at this
          exact this
        · have := h (.inr (.inl (.inl ())))
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero] at this
          exact this
        · have := h (.inr (.inl (.inr ())))
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            neg_mul, one_mul, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib,
            neg_le_neg_iff] at this
          exact this
        · have := h (.inl (.inr k))
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte] at this
          have h' : ∑ j, w j * V j k = ∑ j, V j k * w j :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
          linarith
        · have := h (.inl (.inl k))
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
            ↓reduceIte] at this
          have hneg : ∑ j, -(V j k * w j) = -∑ j, w j * V j k := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
          linarith
      · rintro ⟨hw₀, hw₁, hVk⟩ r
        rcases r with (k | k) | ((⟨⟩ | ⟨⟩) | j₀)
        · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, neg_mul]
          have hneg : ∑ j, -(V j k * w j) = -∑ j, w j * V j k := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
          linarith [hVk k]
        · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          have h' : ∑ j, V j k * w j = ∑ j, w j * V j k :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
          linarith [hVk k]
        · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero]
          exact hw₁.le
        · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            neg_mul, one_mul, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib,
            neg_le_neg_iff]
          exact hw₁.ge
        · simp only [Pi.add_apply, Matrix.mulVec, dotProduct, A, B, rhs, Matrix.of_apply,
            ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            Finset.sum_const_zero, add_zero, neg_nonpos]
          exact hw₀ j₀
    obtain ⟨ρ, _, T, _, _, hproj⟩ := Matrix.FourierMotzkin.exists_projection A B rhs
    let ℓlin : ρ → E →ₗ[ℝ] ℝ := fun r =>
      { toFun := fun x => ((T * B) *ᵥ eE x) r
        map_add' := fun x y => by rw [map_add, Matrix.mulVec_add, Pi.add_apply]
        map_smul' := fun c x => by
          rw [map_smul, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] }
    let ℓ : ρ → E →ᵃ[ℝ] ℝ := fun r =>
      { toFun := fun x => ((T * B) *ᵥ eE x) r - (T *ᵥ rhs) r
        linear := ℓlin r
        map_vadd' := fun x v => by
          rw [vadd_eq_add, map_add, Matrix.mulVec_add, Pi.add_apply]
          change ((T * B) *ᵥ eE v) r + ((T * B) *ᵥ eE x) r - (T *ᵥ rhs) r =
            ((T * B) *ᵥ eE v) r +ᵥ (((T * B) *ᵥ eE x) r - (T *ᵥ rhs) r)
          rw [vadd_eq_add]
          ring }
    refine ⟨Set.range ℓ, Set.finite_range ℓ, ?_⟩
    ext x
    rw [hmem_iff]
    constructor
    · rintro ⟨w, hw₀, hw₁, hVk⟩
      have hle : (T * B) *ᵥ eE x ≤ T *ᵥ rhs := (hproj (eE x)).1 ⟨w, (hsys x w).2 ⟨hw₀, hw₁, hVk⟩⟩
      rintro _ ⟨r, rfl⟩
      exact sub_nonpos.2 (hle r)
    · intro hx
      have hle : (T * B) *ᵥ eE x ≤ T *ᵥ rhs := fun r =>
        sub_nonpos.1 (hx (ℓ r) ⟨r, rfl⟩)
      obtain ⟨w, hw⟩ := (hproj (eE x)).2 hle
      exact ⟨w, (hsys x w).1 hw⟩
  · rw [not_nonempty_iff_eq_empty.1 hSne, convexHull_empty]
    exact isHPolytope_empty

/-- **Weyl–Minkowski theorem** for compact convex polytopes: a set is the convex hull of finitely
many points if and only if it is a bounded intersection of finitely many closed half-spaces. -/
theorem isHPolytope_iff_isVPolytope {P : Set E} : IsHPolytope P ↔ IsVPolytope P :=
  ⟨IsHPolytope.isVPolytope, IsVPolytope.isHPolytope⟩

theorem isPolytope_iff_isHPolytope {P : Set E} : IsPolytope P ↔ IsHPolytope P :=
  isHPolytope_iff_isVPolytope.symm

theorem IsPolytope.finite_extremePoints {P : Set E} (hP : IsPolytope P) :
    (P.extremePoints ℝ).Finite :=
  finite_extremePoints_of_isHPolytope (isPolytope_iff_isHPolytope.1 hP)

theorem IsPolytope.eq_convexHull_extremePoints {P : Set E} (hP : IsPolytope P) :
    P = convexHull ℝ (P.extremePoints ℝ) :=
  (isPolytope_iff_isHPolytope.1 hP).eq_convexHull_extremePoints

theorem IsPolytope.inter {P Q : Set E} (hP : IsPolytope P) (hQ : IsPolytope Q) :
    IsPolytope (P ∩ Q) :=
  ((isPolytope_iff_isHPolytope.1 hP).inter (isPolytope_iff_isHPolytope.1 hQ)).isVPolytope

theorem IsPolytope.preimage_inter {P : Set E} {Q : Set F} (hP : IsPolytope P)
    (hQ : IsPolytope Q) (f : E →ᵃ[ℝ] F) : IsPolytope (P ∩ f ⁻¹' Q) :=
  ((isPolytope_iff_isHPolytope.1 hP).preimage_inter
    (isPolytope_iff_isHPolytope.1 hQ) f).isVPolytope

theorem IsPolytope.inter_setOf_le {P : Set E} (hP : IsPolytope P) {L : Set (E →ᵃ[ℝ] ℝ)}
    (hL : L.Finite) : IsPolytope (P ∩ {x | ∀ ℓ ∈ L, ℓ x ≤ 0}) := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  refine IsHPolytope.isVPolytope
    ⟨hP.isBounded.subset inter_subset_left, LP ∪ L, hLP.union hL, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union]
  rw [hPeq]
  exact ⟨fun ⟨h1, h2⟩ ℓ h => h.elim (h1 ℓ) (h2 ℓ),
    fun h => ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun ℓ hℓ => h ℓ (.inr hℓ)⟩⟩

/-! ### Faces and vertex centroids of polytopes -/

omit [FiniteDimensional ℝ E] in
theorem isExtreme_mem_of_sum_pos {P F : Set E} (hPF : IsExtreme ℝ P F) (hP : Convex ℝ P)
    {S : Finset E} (hSne : S.Nonempty) (hSP : (S : Set E) ⊆ P) (w : E → ℝ)
    (hwpos : ∀ v ∈ S, 0 < w v) (hwsum : ∑ v ∈ S, w v = 1) (hxF : (∑ v ∈ S, w v • v) ∈ F) :
    ∀ v ∈ S, v ∈ F := by
  classical
  induction S using Finset.induction generalizing w with
  | empty => exact absurd hSne Finset.not_nonempty_empty
  | @insert a S' ha ih =>
    rcases S'.eq_empty_or_nonempty with rfl | hS'ne
    · intro v hv
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hv
      subst hv
      rw [Finset.sum_insert (Finset.notMem_empty _), Finset.sum_empty, add_zero] at hwsum hxF
      rwa [hwsum, one_smul] at hxF
    · have ha_mem : a ∈ insert a S' := Finset.mem_insert_self a S'
      have ha_pos : 0 < w a := hwpos a ha_mem
      have hS'_pos : 0 < ∑ v ∈ S', w v :=
        Finset.sum_pos (fun v hv => hwpos v (Finset.mem_insert_of_mem hv)) hS'ne
      have hw_split : w a + ∑ v ∈ S', w v = 1 := by rwa [← Finset.sum_insert ha]
      have ha_lt : w a < 1 := by linarith
      set r := 1 - w a
      have hr_pos : 0 < r := sub_pos.2 ha_lt
      have hr_eq : ∑ v ∈ S', w v = r := by linarith
      let y : E := ∑ v ∈ S', (w v / r) • v
      have hy_sum : ∑ v ∈ S', w v / r = 1 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, hr_eq, mul_inv_cancel₀ hr_pos.ne']
      have hy_mem_hull : y ∈ convexHull ℝ (S' : Set E) := by
        rw [Finset.convexHull_eq]
        refine ⟨fun v => w v / r, fun v hv =>
          div_nonneg (hwpos v (Finset.mem_insert_of_mem hv)).le hr_pos.le, hy_sum, ?_⟩
        rw [Finset.centerMass_eq_of_sum_1 _ id hy_sum]
        rfl
      have hyP : y ∈ P :=
        convexHull_min (Subset.trans (Finset.coe_subset.2 (Finset.subset_insert a S')) hSP) hP
          hy_mem_hull
      have haP : a ∈ P := hSP ha_mem
      have hxy : ∑ v ∈ insert a S', w v • v = w a • a + r • y := by
        rw [Finset.sum_insert ha, add_right_inj]
        simp only [y, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [mul_div_cancel₀ _ hr_pos.ne']
      have hopen : (∑ v ∈ insert a S', w v • v) ∈ openSegment ℝ a y :=
        ⟨w a, r, ha_pos, hr_pos, by linarith, hxy.symm⟩
      have haF : a ∈ F := hPF.left_mem_of_mem_openSegment haP hyP hxF hopen
      have hyF : y ∈ F := hPF.right_mem_of_mem_openSegment haP hyP hxF hopen
      have hS'F := ih hS'ne (Subset.trans (Finset.coe_subset.2 (Finset.subset_insert a S')) hSP)
        (fun v => w v / r) (fun v hv => div_pos (hwpos v (Finset.mem_insert_of_mem hv)) hr_pos)
        hy_sum hyF
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv'
      · exact haF
      · exact hS'F v hv'

omit [FiniteDimensional ℝ E] in
/-- Any point in `convexHull ℝ (s : Set E) ∩ R`, where `(s : Set E) ⊆ Q` and `R` is extreme in
convex `Q`, lies in the convex hull of a nonempty subset `t ⊆ s` contained in `R`. -/
theorem exists_finset_subset_convexHull_of_isExtreme {s : Finset E} {Q R : Set E}
    (hQ : Convex ℝ Q) (hsQ : (s : Set E) ⊆ Q) (hQR : IsExtreme ℝ Q R)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E) ∩ R) :
    ∃ t ⊆ s, t.Nonempty ∧ (t : Set E) ⊆ R ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx.1
  let t := s.filter (fun v => 0 < w v)
  have hwt0 : ∀ v ∈ s, v ∉ t → w v = 0 := fun v hv hn => by
    simp only [t, Finset.mem_filter, not_and, not_lt] at hn
    exact le_antisymm (hn hv) (hw0 v hv)
  have hw_pos : ∀ v ∈ t, 0 < w v := fun v hv => (Finset.mem_filter.1 hv).2
  have hw_sum : ∑ v ∈ t, w v = 1 :=
    (Finset.sum_subset (Finset.filter_subset _ s) hwt0).trans hw1
  have htne : t.Nonempty := by
    by_contra hmt
    rw [Finset.not_nonempty_iff_eq_empty] at hmt
    rw [hmt, Finset.sum_empty] at hw_sum
    exact one_ne_zero hw_sum.symm
  have hx_comb : ∑ v ∈ t, w v • v = x := by
    rw [← hwx]
    exact Finset.sum_subset (Finset.filter_subset _ s) fun v hv hn => by
      rw [hwt0 v hv hn, zero_smul]
  have htR := isExtreme_mem_of_sum_pos hQR hQ htne
    (Subset.trans (Finset.coe_subset.2 (Finset.filter_subset _ s)) hsQ)
    w hw_pos hw_sum (hx_comb.symm ▸ hx.2)
  exact ⟨t, Finset.filter_subset _ s, htne, fun v hv => htR v hv,
    Finset.mem_convexHull'.2 ⟨w, fun v hv => (hw_pos v hv).le, hw_sum, hx_comb⟩⟩

theorem IsPolytopeFace.eq_convexHull_extremePoints_inter {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) : F = convexHull ℝ (P.extremePoints ℝ ∩ F) := by
  classical
  refine Subset.antisymm (fun x hx => ?_) (convexHull_min inter_subset_right hPF.convex)
  have hVfin := hP.finite_extremePoints
  set V : Finset E := hVfin.toFinset
  have hxV : x ∈ convexHull ℝ (V : Set E) := by
    rw [hVfin.coe_toFinset, ← hP.eq_convexHull_extremePoints]
    exact hPF.subset hx
  have hVP : (V : Set E) ⊆ P := fun _ hv => (hVfin.mem_toFinset.1 hv).1
  obtain ⟨S, hSV, _, hSF, hxS⟩ :=
    exists_finset_subset_convexHull_of_isExtreme hP.convex hVP hPF.isExtreme ⟨hxV, hx⟩
  refine convexHull_mono ?_ hxS
  exact fun v hv => ⟨hVfin.mem_toFinset.1 (hSV hv), hSF hv⟩

theorem IsPolytopeFace.isPolytope {P F : Set E} (hP : IsPolytope P) (hPF : IsPolytopeFace P F) :
    IsPolytope F :=
  ⟨P.extremePoints ℝ ∩ F, hP.finite_extremePoints.subset inter_subset_left,
    hPF.eq_convexHull_extremePoints_inter hP⟩

omit [FiniteDimensional ℝ E] in
theorem IsPolytopeFace.extremePoints_eq {P F : Set E} (hPF : IsPolytopeFace P F) :
    F.extremePoints ℝ = P.extremePoints ℝ ∩ F := by
  rw [hPF.isExtreme.extremePoints_eq, inter_comm]

theorem IsPolytope.extremePoints_nonempty {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty) :
    (P.extremePoints ℝ).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hPeq := hP.eq_convexHull_extremePoints
  rw [h, convexHull_empty] at hPeq
  obtain ⟨x, hx⟩ := hne
  rw [hPeq] at hx
  exact hx

theorem vertexCentroid_eq_centroid {P : Set E} (hP : IsPolytope P) :
    vertexCentroid P = hP.finite_extremePoints.toFinset.centroid ℝ id := by
  unfold vertexCentroid
  rw [dite_eq_left hP.finite_extremePoints]

theorem vertexCentroid_mem {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty) :
    vertexCentroid P ∈ P := by
  rw [vertexCentroid_eq_centroid hP]
  have hsub : P = convexHull ℝ (hP.finite_extremePoints.toFinset : Set E) := by
    rw [hP.finite_extremePoints.coe_toFinset]
    exact hP.eq_convexHull_extremePoints
  have hmem : hP.finite_extremePoints.toFinset.centroid ℝ id ∈
      convexHull ℝ (hP.finite_extremePoints.toFinset : Set E) :=
    Finset.centroid_mem_convexHull (R := ℝ) _ (hP.finite_extremePoints.toFinset_nonempty.2
      (hP.extremePoints_nonempty hne))
  rwa [← hsub] at hmem

theorem vertexCentroid_notMem_of_ssubset {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hss : F ⊂ P) : vertexCentroid P ∉ F := by
  intro hbF
  have hne : P.Nonempty := ⟨vertexCentroid P, hPF.subset hbF⟩
  have hVne : hP.finite_extremePoints.toFinset.Nonempty :=
    hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne)
  rw [vertexCentroid_eq_centroid hP, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)] at hbF
  set V := hP.finite_extremePoints.toFinset
  have hwpos : ∀ v ∈ V, (0 : ℝ) < V.centroidWeights ℝ v := fun v _ => by
    simp only [Finset.centroidWeights_apply, inv_pos, Nat.cast_pos]
    exact Finset.card_pos.2 hVne
  have hVF : (V : Set E) ⊆ F :=
    isExtreme_mem_of_sum_pos hPF.isExtreme hP.convex hVne
      (fun v hv => (hP.finite_extremePoints.mem_toFinset.1 hv).1)
      (V.centroidWeights ℝ) hwpos (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne) hbF
  have hPF' : P ⊆ F := by
    rw [hP.eq_convexHull_extremePoints, ← hP.finite_extremePoints.coe_toFinset]
    exact convexHull_min hVF hPF.convex
  exact hss.not_subset hPF'

theorem IsPolytopeFace.inter_affineSpan_eq {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hne : F.Nonempty) : P ∩ (affineSpan ℝ F : Set E) = F := by
  classical
  refine Subset.antisymm ?_ (subset_inter hPF.subset (subset_affineSpan ℝ F))
  intro x ⟨hxP, hxaff⟩
  have hFp := hPF.isPolytope hP
  have hVfin := hFp.finite_extremePoints
  set V : Finset E := hVfin.toFinset
  have hVne : V.Nonempty := hVfin.toFinset_nonempty.2 (hFp.extremePoints_nonempty hne)
  have hVeq : F = convexHull ℝ (V : Set E) := by
    rw [hVfin.coe_toFinset]
    exact hFp.eq_convexHull_extremePoints
  have hxaffV : x ∈ affineSpan ℝ (Set.range ((↑) : V → E)) := by
    rw [Subtype.range_coe_subtype]
    change x ∈ affineSpan ℝ (V : Set E)
    rwa [← affineSpan_convexHull (V : Set E), ← hVeq]
  rw [mem_affineSpan_iff_eq_affineCombination] at hxaffV
  obtain ⟨s', w', hw'1, rfl⟩ := hxaffV
  let w : E → ℝ := fun v => if hv : v ∈ V then if ⟨v, hv⟩ ∈ s' then w' ⟨v, hv⟩ else 0 else 0
  have hw1 : ∑ v ∈ V, w v = 1 := by
    rw [← Finset.sum_coe_sort V w]
    have hsplit : ∑ v : V, w v.1 = ∑ v ∈ s', w' v := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V => v ∈ s')]
      have h1 : Finset.univ.filter (fun v : V => v ∈ s') = s' := by ext; simp
      have h2 : ∑ v ∈ Finset.univ.filter (fun v : V => v ∉ s'), w v.1 = 0 :=
        Finset.sum_eq_zero fun v hv => by
          have hns : v ∉ s' := (Finset.mem_filter.1 hv).2
          simp only [w, v.2, hns, ↓reduceDIte, ↓reduceIte]
      rw [h1, h2, add_zero]
      exact Finset.sum_congr rfl fun v hv => by simp only [w, v.2, hv, ↓reduceDIte, ↓reduceIte]
    exact hsplit.trans hw'1
  have hwx : s'.affineCombination ℝ ((↑) : V → E) w' = ∑ v ∈ V, w v • v := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw'1, ← Finset.sum_coe_sort V,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V => v ∈ s')]
    have h1 : Finset.univ.filter (fun v : V => v ∈ s') = s' := by ext; simp
    have h2 : ∑ v ∈ Finset.univ.filter (fun v : V => v ∉ s'), w v.1 • v.1 = 0 :=
      Finset.sum_eq_zero fun v hv => by
        have hns : v ∉ s' := (Finset.mem_filter.1 hv).2
        simp only [w, v.2, hns, ↓reduceDIte, ↓reduceIte, zero_smul]
    rw [h1, h2, add_zero]
    exact Finset.sum_congr rfl fun v hv => by simp only [w, v.2, hv, ↓reduceDIte, ↓reduceIte]
  let n : ℝ := (V.card : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 (Finset.card_pos.2 hVne)
  let M : ℝ := V.sum (fun v => |w v|)
  have hM : 0 ≤ M := Finset.sum_nonneg fun v _ => abs_nonneg _
  let ε : ℝ := 1 / (2 * n * (M + 1))
  have hden_pos : 0 < 2 * n * (M + 1) := mul_pos (mul_pos two_pos hn) (by linarith)
  have hε_pos : 0 < ε := div_pos one_pos hden_pos
  have hε_lt : ε < 1 := by
    have h1 : 1 ≤ n := Nat.one_le_cast.2 (Nat.succ_le_of_lt (Finset.card_pos.2 hVne))
    have h2 : 1 < 2 * n * (M + 1) := by nlinarith
    exact (div_lt_one hden_pos).2 h2
  let b := vertexCentroid F
  have hbF : b ∈ F := vertexCentroid_mem hFp hne
  have hb_eq : b = ∑ v ∈ V, (1 / n) • v := by
    dsimp only [b]
    rw [vertexCentroid_eq_centroid hFp, Finset.centroid_def]
    change Finset.affineCombination ℝ V id (V.centroidWeights ℝ) = _
    rw [Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)]
    simp only [Finset.centroidWeights_apply, one_div, id_eq, n]
  let y := (1 - ε) • b + ε • (∑ v ∈ V, w v • v)
  have hyF : y ∈ F := by
    rw [hVeq, Finset.convexHull_eq]
    let u : E → ℝ := fun v => (1 - ε) * (1 / n) + ε * w v
    have husum : ∑ v ∈ V, u v = 1 := by
      simp only [u, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hw1]
      have hn0 : n ≠ 0 := hn.ne'
      field_simp
      ring
    refine ⟨u, fun v hv => ?_, husum, ?_⟩
    · have hw_le : -M ≤ w v := by
        have := Finset.single_le_sum (fun z _ => abs_nonneg (w z)) hv
        linarith [neg_abs_le (w v)]
      have h1 : 1 / 2 ≤ 1 - ε := by
        have h1' : 1 ≤ n := Nat.one_le_cast.2 (Nat.succ_le_of_lt (Finset.card_pos.2 hVne))
        have h2' : 2 ≤ 2 * n * (M + 1) := by nlinarith
        have hle : ε ≤ 1 / 2 := (div_le_div_iff₀ hden_pos two_pos).2 (by linarith)
        linarith
      have h2 : -((1 - ε) / n) ≤ ε * (-M) := by
        have hbound : ε * M ≤ 1 / (2 * n) := by
          simp only [ε]
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hden_pos (mul_pos two_pos hn)]
          nlinarith
        have hhalf : 1 / (2 * n) ≤ (1 - ε) / n := by
          rw [div_le_div_iff₀ (mul_pos two_pos hn) hn]
          nlinarith
        linarith
      have hmul : ε * (-M) ≤ ε * w v := mul_le_mul_of_nonneg_left hw_le hε_pos.le
      dsimp only [u]
      nlinarith [show (1 - ε) * (1 / n) = (1 - ε) / n by ring]
    · rw [Finset.centerMass_eq_of_sum_1 _ id husum]
      simp only [y, hb_eq, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib,
        ← add_smul, u, id]
  rw [hwx]
  exact hPF.isExtreme.right_mem_of_mem_openSegment (hPF.subset hbF) (hwx ▸ hxP) hyF
    ⟨1 - ε, ε, sub_pos.2 hε_lt, hε_pos, sub_add_cancel 1 ε, rfl⟩

theorem vertexCentroid_notMem_affineSpan_of_ssubset {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hne : F.Nonempty) (hss : F ⊂ P) :
    vertexCentroid P ∉ affineSpan ℝ F := by
  intro hmem
  have hmem' : vertexCentroid P ∈ P ∩ (affineSpan ℝ F : Set E) :=
    ⟨vertexCentroid_mem hP ⟨hne.some, hPF.subset hne.some_mem⟩, hmem⟩
  rw [hPF.inter_affineSpan_eq hP hne] at hmem'
  exact vertexCentroid_notMem_of_ssubset hP hPF hss hmem'

theorem IsPolytope.apply_vertexCentroid_lt {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty)
    {ℓ : E →ᵃ[ℝ] ℝ} (hℓ_le : ∀ z ∈ P, ℓ z ≤ 0) {y : E} (hyP : y ∈ P) (hylt : ℓ y < 0) :
    ℓ (vertexCentroid P) < 0 := by
  classical
  set V : Finset E := hP.finite_extremePoints.toFinset
  have hVne : V.Nonempty :=
    hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne)
  have hVsub : (V : Set E) ⊆ P := fun v hv => (hP.finite_extremePoints.mem_toFinset.1 hv).1
  have hyhull : y ∈ convexHull ℝ (V : Set E) := by
    rwa [hP.finite_extremePoints.coe_toFinset, ← hP.eq_convexHull_extremePoints]
  rw [Finset.convexHull_eq] at hyhull
  obtain ⟨w, hw0, hw1, rfl⟩ := hyhull
  rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hylt
  simp only [id_eq] at hylt
  rw [affineMap_eval_sum_smul ℓ hw1] at hylt
  have hex : ∃ v₀ ∈ V, ℓ v₀ < 0 := by
    by_contra! hge
    have h0 : 0 ≤ ∑ v ∈ V, w v * ℓ v := Finset.sum_nonneg fun v hv => by
      have : ℓ v = 0 := le_antisymm (hℓ_le v (hVsub hv)) (hge v hv)
      simp [this]
    linarith
  obtain ⟨v₀, hv₀, hv₀lt⟩ := hex
  have hb_sum : ℓ (vertexCentroid P) = ∑ v ∈ V, V.centroidWeights ℝ v * ℓ v := by
    rw [vertexCentroid_eq_centroid hP, Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)]
    simp only [id_eq]
    exact affineMap_eval_sum_smul ℓ (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)
  rw [hb_sum, ← Finset.add_sum_erase _ _ hv₀]
  have hVcard : (0 : ℝ) < V.card := Nat.cast_pos.2 (Finset.card_pos.2 hVne)
  have hhead : V.centroidWeights ℝ v₀ * ℓ v₀ < 0 :=
    mul_neg_of_pos_of_neg (by simp [Finset.centroidWeights_apply, hVcard]) hv₀lt
  have hrest : ∑ v ∈ V.erase v₀, V.centroidWeights ℝ v * ℓ v ≤ 0 :=
    Finset.sum_nonpos fun v hv => mul_nonpos_of_nonneg_of_nonpos
      (by simp [Finset.centroidWeights_apply]) (hℓ_le v (hVsub (Finset.mem_of_mem_erase hv)))
  linarith

private lemma isExposed_of_eq_zero {R : Set E} {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite)
    (hReq : R = {x | ∀ ℓ ∈ LR, ℓ x ≤ 0}) {L₀ : Set (E →ᵃ[ℝ] ℝ)} (hL₀ : L₀ ⊆ LR) :
    IsExposed ℝ R {x ∈ R | ∀ ℓ ∈ L₀, ℓ x = 0} := by
  classical
  set L₀f : Finset (E →ᵃ[ℝ] ℝ) := (hLR.subset hL₀).toFinset
  let gLin : E →ₗ[ℝ] ℝ := ∑ ℓ ∈ L₀f, ℓ.linear
  let g : StrongDual ℝ E := ⟨gLin, gLin.continuous_of_finiteDimensional⟩
  intro hne
  refine ⟨g, Subset.antisymm (fun x hx => ⟨hx.1, fun y hy => ?_⟩) ?_⟩
  · have hx0 : ∀ ℓ ∈ L₀f, ℓ x = 0 := fun ℓ hℓ =>
      hx.2 ℓ ((hLR.subset hL₀).mem_toFinset.1 hℓ)
    have hy_le : ∀ ℓ ∈ L₀f, ℓ y ≤ 0 := fun ℓ hℓ =>
      (hReq ▸ hy) ℓ (hL₀ ((hLR.subset hL₀).mem_toFinset.1 hℓ))
    have hdiff : g y - g x = ∑ ℓ ∈ L₀f, (ℓ y - ℓ x) := by
      simp only [g, gLin, ContinuousLinearMap.coe_mk', LinearMap.coe_sum, Finset.sum_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have hv := ℓ.linear_apply_vsub y x
      simpa [vsub_eq_sub] using hv
    have hnonpos : g y - g x ≤ 0 := by
      rw [hdiff]
      exact Finset.sum_nonpos fun ℓ hℓ => by rw [hx0 ℓ hℓ, sub_zero]; exact hy_le ℓ hℓ
    linarith
  · rintro x ⟨hxR, hxmax⟩
    obtain ⟨y₀, hy₀⟩ := hne
    refine ⟨hxR, fun ℓ hℓ => ?_⟩
    have hxy : g y₀ - g x ≤ 0 := sub_nonpos.2 (hxmax y₀ hy₀.1)
    have hdiff : g y₀ - g x = ∑ m ∈ L₀f, (m y₀ - m x) := by
      simp only [g, gLin, ContinuousLinearMap.coe_mk', LinearMap.coe_sum, Finset.sum_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hv := m.linear_apply_vsub y₀ x
      simpa [vsub_eq_sub] using hv
    have hsum : ∑ m ∈ L₀f, (-m x) ≤ 0 := by
      have : ∑ m ∈ L₀f, (m y₀ - m x) = ∑ m ∈ L₀f, (-m x) :=
        Finset.sum_congr rfl fun m hm => by
          rw [hy₀.2 m ((hLR.subset hL₀).mem_toFinset.1 hm), zero_sub]
      linarith [hdiff]
    have hnonneg : ∀ m ∈ L₀f, 0 ≤ -m x := fun m hm =>
      neg_nonneg.2 ((hReq ▸ hxR) m (hL₀ ((hLR.subset hL₀).mem_toFinset.1 hm)))
    have h0 : -ℓ x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1
        (le_antisymm hsum (Finset.sum_nonneg hnonneg)) ℓ ((hLR.subset hL₀).mem_toFinset.2 hℓ)
    linarith

omit [FiniteDimensional ℝ E] in
theorem IsExposed.isPolytopeFace {P F : Set E} (hP : Convex ℝ P) (hPF : IsExposed ℝ P F) :
    IsPolytopeFace P F := by
  refine ⟨hPF.isExtreme, ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact convex_empty
  · obtain ⟨l, rfl⟩ := hPF hne
    intro x hx y hy a b ha hb hab
    refine ⟨hP hx.1 hy.1 ha hb hab, fun z hz => ?_⟩
    simp only [smul_eq_mul, map_add, map_smul]
    have hax : a * l z ≤ a * l x := mul_le_mul_of_nonneg_left (hx.2 z hz) ha
    have hby : b * l z ≤ b * l y := mul_le_mul_of_nonneg_left (hy.2 z hz) hb
    linarith [show a * l z + b * l z = l z by rw [← add_mul, hab, one_mul]]

theorem isPolytopeFace_of_eq_zero {R : Set E} {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite)
    (hReq : R = {x | ∀ ℓ ∈ LR, ℓ x ≤ 0}) (hRc : Convex ℝ R)
    {L₀ : Set (E →ᵃ[ℝ] ℝ)} (hL₀ : L₀ ⊆ LR) :
    IsPolytopeFace R {x ∈ R | ∀ ℓ ∈ L₀, ℓ x = 0} :=
  IsExposed.isPolytopeFace hRc (isExposed_of_eq_zero hLR hReq hL₀)

theorem IsPolytopeFace.exists_eq_zero_of_isHPolytope {P F : Set E}
    {L : Set (E →ᵃ[ℝ] ℝ)} (hL : L.Finite) (hPL : P = {x | ∀ ℓ ∈ L, ℓ x ≤ 0})
    (hP : IsPolytope P) (hPF : IsPolytopeFace P F) (hne : F.Nonempty) :
    ∃ L₀ ⊆ L, F = {x ∈ P | ∀ ℓ ∈ L₀, ℓ x = 0} := by
  classical
  let L₀ : Set (E →ᵃ[ℝ] ℝ) := {ℓ ∈ L | ∀ y ∈ F, ℓ y = 0}
  refine ⟨L₀, fun _ h => h.1,
    Subset.antisymm (fun x hx => ⟨hPF.subset hx, fun ℓ hℓ => hℓ.2 x hx⟩) ?_⟩
  intro z ⟨hzP, hzL₀⟩
  have hFp := hPF.isPolytope hP
  let b := vertexCentroid F
  have hbF : b ∈ F := vertexCentroid_mem hFp hne
  have hb_strict : ∀ ℓ ∈ L \ L₀, ℓ b < 0 := by
    rintro ℓ ⟨hℓL, hnℓ⟩
    simp only [L₀, mem_ofPred_eq, hℓL, true_and, not_forall] at hnℓ
    obtain ⟨y, hyF, hne0⟩ := hnℓ
    have hy_lt : ℓ y < 0 := ((hPL ▸ hPF.subset hyF) ℓ hℓL).lt_of_ne hne0
    exact hFp.apply_vertexCentroid_lt hne (fun z hz => (hPL ▸ hPF.subset hz) ℓ hℓL) hyF hy_lt
  set Lstrict : Finset (E →ᵃ[ℝ] ℝ) := hL.toFinset.filter (fun ℓ => ℓ ∉ L₀)
  let ε : ℝ :=
    if hs : Lstrict.Nonempty then
      min 1 (Lstrict.inf' hs fun ℓ => (-ℓ b) / (|ℓ b - ℓ z| + 1))
    else 1
  have hε_pos : 0 < ε := by
    by_cases hs : Lstrict.Nonempty
    · dsimp only [ε]
      rw [dite_eq_left hs, lt_min_iff]
      refine ⟨one_pos, (Finset.lt_inf'_iff hs).2 fun ℓ hℓ => ?_⟩
      have hℓ' : ℓ ∈ L \ L₀ := by
        rw [Finset.mem_filter, hL.mem_toFinset] at hℓ
        exact hℓ
      exact div_pos (neg_pos.2 (hb_strict ℓ hℓ')) (by positivity)
    · dsimp only [ε]
      rw [dite_eq_right hs]
      exact one_pos
  let w : E := AffineMap.lineMap b z (-ε)
  have hwP : w ∈ P := by
    rw [hPL]
    intro ℓ hℓ
    rw [affineMap_lineMap]
    by_cases hℓ0 : ℓ ∈ L₀
    · have hb0 : ℓ b = 0 := hℓ0.2 b hbF
      have hz0 : ℓ z = 0 := hzL₀ ℓ hℓ0
      rw [hb0, hz0, sub_zero, mul_zero, add_zero]
    · have hℓs : ℓ ∈ Lstrict := Finset.mem_filter.2 ⟨hL.mem_toFinset.2 hℓ, hℓ0⟩
      have hs : Lstrict.Nonempty := ⟨ℓ, hℓs⟩
      have hε_le : ε ≤ (-ℓ b) / (|ℓ b - ℓ z| + 1) := by
        dsimp only [ε]
        rw [dite_eq_left hs]
        exact (min_le_right 1 _).trans (Finset.inf'_le _ hℓs)
      have hb_lt : ℓ b < 0 := hb_strict ℓ ⟨hℓ, hℓ0⟩
      have hbound : ε * |ℓ z - ℓ b| ≤ -ℓ b := by
        rw [abs_sub_comm]
        have h1 : ε * (|ℓ b - ℓ z| + 1) ≤ -ℓ b := by
          calc ε * (|ℓ b - ℓ z| + 1)
              ≤ ((-ℓ b) / (|ℓ b - ℓ z| + 1)) * (|ℓ b - ℓ z| + 1) :=
                mul_le_mul_of_nonneg_right hε_le (by positivity)
            _ = -ℓ b := div_mul_cancel₀ _ (by positivity)
        linarith
      have hneg_le : -ε * (ℓ z - ℓ b) ≤ ε * |ℓ z - ℓ b| := by
        calc -ε * (ℓ z - ℓ b) = -(ε * (ℓ z - ℓ b)) := neg_mul _ _
          _ ≤ |-(ε * (ℓ z - ℓ b))| := le_abs_self _
          _ = |ε * (ℓ z - ℓ b)| := abs_neg _
          _ = ε * |ℓ z - ℓ b| := by rw [abs_mul, abs_of_pos hε_pos]
      linarith
  have hopen : b ∈ openSegment ℝ w z := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, ?_, ?_⟩
    · field_simp
    · simp only [w, AffineMap.lineMap_apply_module, smul_add, smul_smul]
      have hcb : 1 / (1 + ε) * (1 - -ε) = 1 := by field_simp; ring
      have hcz : 1 / (1 + ε) * -ε + ε / (1 + ε) = 0 := by field_simp; ring
      rw [add_assoc, ← add_smul, hcb, hcz, one_smul, zero_smul, add_zero]
  exact hPF.isExtreme.right_mem_of_mem_openSegment hwP hzP hbF hopen

theorem IsPolytopeFace.isExposed {P F : Set E} (hP : IsPolytope P) (hPF : IsPolytopeFace P F) :
    IsExposed ℝ P F := by
  intro hne
  obtain ⟨_, L, hL, hPL⟩ := isPolytope_iff_isHPolytope.1 hP
  obtain ⟨L₀, hL₀, hFeq⟩ := hPF.exists_eq_zero_of_isHPolytope hL hPL hP hne
  have hexp := isExposed_of_eq_zero hL hPL hL₀
  rw [← hFeq] at hexp
  exact hexp hne

theorem exists_isPolytopeFace_inter_setOf_le_eq_zero {P R F : Set E} (hP : IsPolytope P)
    {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite) (hR : R = {x | ∀ m ∈ LR, m x ≤ 0})
    (hF : IsPolytopeFace (P ∩ R) F) (hne : F.Nonempty) :
    ∃ P' L₀, IsPolytopeFace P P' ∧ L₀ ⊆ LR ∧ F = P' ∩ {x ∈ R | ∀ m ∈ L₀, m x = 0} := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  have hPR_eq : P ∩ R = {x | ∀ ℓ ∈ LP ∪ LR, ℓ x ≤ 0} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union]
    rw [hPeq, hR]
    exact ⟨fun ⟨h1, h2⟩ ℓ h => h.elim (h1 ℓ) (h2 ℓ),
      fun h => ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun ℓ hℓ => h ℓ (.inr hℓ)⟩⟩
  have hPR : IsPolytope (P ∩ R) :=
    IsHPolytope.isVPolytope ⟨hP.isBounded.subset inter_subset_left, LP ∪ LR, hLP.union hLR, hPR_eq⟩
  obtain ⟨K₀, hK₀, hFeq⟩ := hF.exists_eq_zero_of_isHPolytope (hLP.union hLR) hPR_eq hPR hne
  let P' := {x ∈ P | ∀ ℓ ∈ K₀ ∩ LP, ℓ x = 0}
  let L₀ := K₀ ∩ LR
  let R' := {x ∈ R | ∀ ℓ ∈ L₀, ℓ x = 0}
  have hFeq' : F = P' ∩ R' := by
    rw [hFeq]
    ext x
    simp only [P', R', L₀, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hxP, hxR⟩, hxK⟩
      exact ⟨⟨hxP, fun ℓ hℓ => hxK ℓ hℓ.1⟩, ⟨hxR, fun ℓ hℓ => hxK ℓ hℓ.1⟩⟩
    · rintro ⟨⟨hxP, hxKP⟩, ⟨hxR, hxKR⟩⟩
      refine ⟨⟨hxP, hxR⟩, fun ℓ hℓ => ?_⟩
      rcases hK₀ hℓ with hℓP | hℓR
      · exact hxKP ℓ ⟨hℓ, hℓP⟩
      · exact hxKR ℓ ⟨hℓ, hℓR⟩
  exact ⟨P', L₀, isPolytopeFace_of_eq_zero hLP hPeq hP.convex inter_subset_right,
    inter_subset_right, hFeq'⟩

theorem exists_isPolytopeFace_inter_setOf_le {P R F : Set E} (hP : IsPolytope P)
    {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite) (hR : R = {x | ∀ m ∈ LR, m x ≤ 0})
    (hF : IsPolytopeFace (P ∩ R) F) (hne : F.Nonempty) :
    ∃ P' R', IsPolytopeFace P P' ∧ IsPolytopeFace R R' ∧ F = P' ∩ R' := by
  have hRc : Convex ℝ R := hR ▸ convex_setOf_forall_le LR
  obtain ⟨P', L₀, hPP', hL₀, hFeq⟩ :=
    exists_isPolytopeFace_inter_setOf_le_eq_zero hP hLR hR hF hne
  exact ⟨P', {x ∈ R | ∀ m ∈ L₀, m x = 0}, hPP',
    isPolytopeFace_of_eq_zero hLR hR hRc hL₀, hFeq⟩

theorem exists_isPolytopeFace_inter_eq {P Q F : Set E} (hP : IsPolytope P) (hQ : IsPolytope Q)
    (hF : IsPolytopeFace (P ∩ Q) F) (hne : F.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ F = P' ∩ Q' := by
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  exact exists_isPolytopeFace_inter_setOf_le hP hLQ hQeq hF hne

theorem exists_isPolytopeFace_preimage_inter_eq {P : Set E} {Q : Set F} (f : E →ᵃ[ℝ] F)
    (hP : IsPolytope P) (hQ : IsPolytope Q) {G : Set E}
    (hG : IsPolytopeFace (P ∩ f ⁻¹' Q) G) (hne : G.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ G = P' ∩ f ⁻¹' Q' := by
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  let Lf : Set (E →ᵃ[ℝ] ℝ) := (fun m : F →ᵃ[ℝ] ℝ => m.comp f) '' LQ
  have hLf : Lf.Finite := hLQ.image _
  have hpre : f ⁻¹' Q = {x | ∀ k ∈ Lf, k x ≤ 0} := by
    ext x
    simp only [Set.mem_preimage, mem_ofPred_eq, Lf, Set.mem_image]
    rw [hQeq]
    constructor
    · rintro hx _ ⟨m, hm, rfl⟩
      exact hx m hm
    · intro hx m hm
      exact hx (m.comp f) ⟨m, hm, rfl⟩
  have hPR_eq : P ∩ f ⁻¹' Q = {x | ∀ ℓ ∈ LP ∪ Lf, ℓ x ≤ 0} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union]
    rw [hPeq, hpre]
    exact ⟨fun ⟨h1, h2⟩ ℓ h => h.elim (h1 ℓ) (h2 ℓ),
      fun h => ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun ℓ hℓ => h ℓ (.inr hℓ)⟩⟩
  have hPR : IsPolytope (P ∩ f ⁻¹' Q) := hP.preimage_inter hQ f
  obtain ⟨K₀, hK₀, hGeq⟩ := hG.exists_eq_zero_of_isHPolytope (hLP.union hLf) hPR_eq hPR hne
  let P' := {x ∈ P | ∀ ℓ ∈ K₀ ∩ LP, ℓ x = 0}
  let Q' := {y ∈ Q | ∀ m ∈ LQ, m.comp f ∈ K₀ → m y = 0}
  have hGeq' : G = P' ∩ f ⁻¹' Q' := by
    rw [hGeq]
    ext x
    simp only [P', Q', mem_inter_iff, Set.mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hxP, hxQ⟩, hxK⟩
      exact ⟨⟨hxP, fun ℓ hℓ => hxK ℓ hℓ.1⟩, ⟨hxQ, fun m _ hmK => hxK (m.comp f) hmK⟩⟩
    · rintro ⟨⟨hxP, hxKP⟩, ⟨hxQ, hxKQ⟩⟩
      refine ⟨⟨hxP, hxQ⟩, fun ℓ hℓ => ?_⟩
      rcases hK₀ hℓ with hℓP | ⟨m, hmQ, rfl⟩
      · exact hxKP ℓ ⟨hℓ, hℓP⟩
      · exact hxKQ m hmQ hℓ
  have hQ'face : IsPolytopeFace Q Q' := by
    have hQ'eq : Q' = {y ∈ Q | ∀ m ∈ {m ∈ LQ | m.comp f ∈ K₀}, m y = 0} := by
      ext y; simp [Q']
    rw [hQ'eq]
    exact isPolytopeFace_of_eq_zero hLQ hQeq hQ.convex (fun _ hm => hm.1)
  exact ⟨P', Q', isPolytopeFace_of_eq_zero hLP hPeq hP.convex inter_subset_right, hQ'face, hGeq'⟩

/-- Every point `x ∈ P` other than `vertexCentroid P` lies on a closed segment from
`vertexCentroid P` to a point `y` in some proper nonempty face of `P`. -/
theorem exists_isPolytopeFace_ssubset_of_ne_vertexCentroid {P : Set E} (hP : IsPolytope P)
    {x : E} (hx : x ∈ P) (hxne : x ≠ vertexCentroid P) :
    ∃ F, IsPolytopeFace P F ∧ F.Nonempty ∧ F ⊂ P ∧
      ∃ y ∈ F, x ∈ segment ℝ (vertexCentroid P) y := by
  classical
  obtain ⟨hbnd, L, hL, hPL⟩ := isPolytope_iff_isHPolytope.1 hP
  let b := vertexCentroid P
  have hbP : b ∈ P := vertexCentroid_mem hP ⟨x, hx⟩
  let Lstrict : Set (E →ᵃ[ℝ] ℝ) := {ℓ ∈ L | ∃ z ∈ P, ℓ z < 0}
  have hb_strict : ∀ ℓ ∈ Lstrict, ℓ b < 0 := fun ℓ ⟨hℓL, z, hzP, hzlt⟩ =>
    hP.apply_vertexCentroid_lt ⟨x, hx⟩ (fun w hw => (hPL ▸ hw) ℓ hℓL) hzP hzlt
  set Linc : Finset (E →ᵃ[ℝ] ℝ) := hL.toFinset.filter (fun ℓ => ℓ ∈ Lstrict ∧ ℓ b < ℓ x)
  have hLinc_ne : Linc.Nonempty := by
    by_contra hmt
    rw [Finset.not_nonempty_iff_eq_empty] at hmt
    have hray : ∀ t : ℝ, 1 ≤ t → AffineMap.lineMap b x t ∈ P := by
      intro t ht
      rw [hPL]
      intro ℓ hℓ
      rw [affineMap_lineMap]
      by_cases hℓs : ℓ ∈ Lstrict
      · have hn : ℓ ∉ Linc := by simp [hmt]
        simp only [Linc, Finset.mem_filter, hL.mem_toFinset.2 hℓ, hℓs, true_and, not_lt] at hn
        have hb0 : ℓ b < 0 := hb_strict ℓ hℓs
        have hdiff : ℓ x - ℓ b ≤ 0 := sub_nonpos.2 hn
        have hmul : t * (ℓ x - ℓ b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hdiff
        linarith
      · have h0b : ℓ b = 0 := by
          by_contra hne
          exact hℓs ⟨hℓ, b, hbP, ((hPL ▸ hbP) ℓ hℓ).lt_of_ne hne⟩
        have h0x : ℓ x = 0 := by
          by_contra hne
          exact hℓs ⟨hℓ, x, hx, ((hPL ▸ hx) ℓ hℓ).lt_of_ne hne⟩
        rw [h0b, h0x, sub_zero, mul_zero, add_zero]
    obtain ⟨C, hC⟩ := hbnd.subset_closedBall b
    have hxd_pos : 0 < ‖x - b‖ := norm_sub_pos_iff.2 hxne
    set t : ℝ := max 1 ((C + 1) / ‖x - b‖)
    have ht1 : 1 ≤ t := le_max_left _ _
    have hmem := hC (hray t ht1)
    rw [mem_closedBall_iff_norm, AffineMap.lineMap_apply_module] at hmem
    have hnorm : ‖(1 - t) • b + t • x - b‖ = t * ‖x - b‖ := by
      have : (1 - t) • b + t • x - b = t • (x - b) := by module
      rw [this, norm_smul, Real.norm_of_nonneg (by linarith)]
    rw [hnorm] at hmem
    have hC1 : C + 1 ≤ t * ‖x - b‖ := (div_le_iff₀ hxd_pos).1 (le_max_right 1 _)
    linarith
  obtain ⟨ℓ₀, hℓ₀, hmin⟩ := Linc.exists_min_image (fun ℓ => (-ℓ b) / (ℓ x - ℓ b)) hLinc_ne
  set t := (-ℓ₀ b) / (ℓ₀ x - ℓ₀ b)
  have hℓ₀L : ℓ₀ ∈ L := hL.mem_toFinset.1 (Finset.filter_subset _ _ hℓ₀)
  have hℓ₀s : ℓ₀ ∈ Lstrict := (Finset.mem_filter.1 hℓ₀).2.1
  have hℓ₀_inc : ℓ₀ b < ℓ₀ x := (Finset.mem_filter.1 hℓ₀).2.2
  have hℓ₀_le : ℓ₀ x ≤ 0 := (hPL ▸ hx) ℓ₀ hℓ₀L
  have hℓ₀_diff : 0 < ℓ₀ x - ℓ₀ b := sub_pos.2 hℓ₀_inc
  have ht1 : 1 ≤ t := (one_le_div hℓ₀_diff).2 (by linarith)
  have ht_pos : 0 < t := by linarith
  let y := AffineMap.lineMap b x t
  have hyP : y ∈ P := by
    rw [hPL]
    intro ℓ hℓ
    rw [affineMap_lineMap]
    by_cases hℓs : ℓ ∈ Lstrict
    · have hb0 : ℓ b < 0 := hb_strict ℓ hℓs
      by_cases hinc : ℓ b < ℓ x
      · have hmem : ℓ ∈ Linc := Finset.mem_filter.2 ⟨hL.mem_toFinset.2 hℓ, hℓs, hinc⟩
        have hle := hmin ℓ hmem
        have hdiff : 0 < ℓ x - ℓ b := sub_pos.2 hinc
        have hmul : t * (ℓ x - ℓ b) ≤ -ℓ b := (le_div_iff₀ hdiff).1 hle
        linarith
      · have hdiff : ℓ x - ℓ b ≤ 0 := sub_nonpos.2 (not_lt.1 hinc)
        have hmul : t * (ℓ x - ℓ b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht_pos.le hdiff
        linarith
    · have h0b : ℓ b = 0 := by
        by_contra hne
        exact hℓs ⟨hℓ, b, hbP, ((hPL ▸ hbP) ℓ hℓ).lt_of_ne hne⟩
      have h0x : ℓ x = 0 := by
        by_contra hne
        exact hℓs ⟨hℓ, x, hx, ((hPL ▸ hx) ℓ hℓ).lt_of_ne hne⟩
      rw [h0b, h0x, sub_zero, mul_zero, add_zero]
  have hy0 : ℓ₀ y = 0 := by
    simp only [y, affineMap_lineMap, t]
    rw [div_mul_cancel₀ _ hℓ₀_diff.ne']
    ring
  let F : Set E := {z ∈ P | ℓ₀ z = 0}
  have hPF : IsPolytopeFace P F := by
    have hsub : {ℓ₀} ⊆ L := singleton_subset_iff.2 hℓ₀L
    simpa [F] using isPolytopeFace_of_eq_zero hL hPL hP.convex hsub
  have hFne : F.Nonempty := ⟨y, hyP, hy0⟩
  have hFss : F ⊂ P := ⟨fun _ h => h.1, fun hsub => by
    have hbF := hsub hbP
    exact (hb_strict ℓ₀ hℓ₀s).ne hbF.2⟩
  refine ⟨F, hPF, hFne, hFss, y, ⟨hyP, hy0⟩, ?_⟩
  refine ⟨1 - 1 / t, 1 / t, sub_nonneg.2 (div_le_one_of_le₀ ht1 ht_pos.le), by positivity,
    by ring, ?_⟩
  simp only [y, AffineMap.lineMap_apply_module]
  have ht0 : t ≠ 0 := ht_pos.ne'
  have hcb : 1 - 1 / t + (1 / t) * (1 - t) = 0 := by field_simp; ring
  have hcx : (1 / t) * t = 1 := by field_simp
  calc (1 - 1 / t) • b + (1 / t) • ((1 - t) • b + t • x)
      = (1 - 1 / t + (1 / t) * (1 - t)) • b + ((1 / t) * t) • x := by module
    _ = x := by rw [hcb, hcx, zero_smul, one_smul, zero_add]

theorem IsPolytopeFace.simplex_convexHull_iff {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) {F : Set E} :
    IsPolytopeFace (convexHull ℝ (s : Set E)) F ↔ ∃ t ⊆ s, F = convexHull ℝ (t : Set E) := by
  classical
  have hP : IsPolytope (convexHull ℝ (s : Set E)) := isPolytope_convexHull s.finite_toSet
  constructor
  · intro hPF
    let t := s.filter (fun v => v ∈ F)
    refine ⟨t, Finset.filter_subset _ _, Subset.antisymm (fun x hx => ?_) ?_⟩
    · have hFeq := hPF.eq_convexHull_extremePoints_inter hP
      refine convexHull_mono (fun v hv => ?_) (hFeq ▸ hx)
      rcases hv with ⟨hvext, hvF⟩
      have hvs : v ∈ (s : Set E) := extremePoints_convexHull_subset hvext
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hvs, hvF⟩)
    · exact convexHull_min (fun v hv => (Finset.mem_filter.1 hv).2) hPF.convex
  · rintro ⟨t, hts, rfl⟩
    refine ⟨⟨convexHull_mono (Finset.coe_subset.2 hts), fun x hx y hy z hz hzx => ?_⟩,
      convex_convexHull ℝ _⟩
    have hx_hull := hx
    have hy_hull := hy
    rw [Finset.convexHull_eq] at hx_hull hy_hull
    obtain ⟨wx, hwx0, hwx1, rfl⟩ := hx_hull
    obtain ⟨wy, hwy0, hwy1, rfl⟩ := hy_hull
    rcases hzx with ⟨a, b, ha, hb, hab, hzeq⟩
    have hz_hull := hz
    rw [Finset.convexHull_eq] at hz_hull
    obtain ⟨wz, hwz0, hwz1, hwzeq⟩ := hz_hull
    let cx : E → ℝ := fun v => if v ∈ s then wx v else 0
    let cy : E → ℝ := fun v => if v ∈ s then wy v else 0
    let cz : E → ℝ := fun v => if v ∈ t then wz v else 0
    let c' : E → ℝ := fun v => a * cx v + b * cy v
    let c : s → ℝ := fun v => c' v.1
    let d : s → ℝ := fun v => cz v.1
    have hcx_sum : ∑ v : s, cx v.1 = 1 := by
      rw [Finset.sum_coe_sort s cx]
      exact (Finset.sum_congr rfl fun v hv => by simp only [cx, hv, ↓reduceIte]).trans hwx1
    have hcy_sum : ∑ v : s, cy v.1 = 1 := by
      rw [Finset.sum_coe_sort s cy]
      exact (Finset.sum_congr rfl fun v hv => by simp only [cy, hv, ↓reduceIte]).trans hwy1
    have hc_sum : ∑ v : s, c v = 1 := by
      simp only [c, c', Finset.sum_add_distrib, ← Finset.mul_sum, hcx_sum, hcy_sum]
      linarith
    have hd_sum : ∑ v : s, d v = 1 := by
      dsimp only [d]
      rw [Finset.sum_coe_sort s cz]
      have hsub : ∑ v ∈ s, cz v = ∑ v ∈ t, wz v := by
        simp only [cz, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.2 hts]
      exact hsub.trans hwz1
    have hc_comb : Finset.univ.affineCombination ℝ ((↑) : s → E) c =
        a • s.centerMass wx id + b • s.centerMass wy id := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hc_sum,
        s.centerMass_eq_of_sum_1 id hwx1, s.centerMass_eq_of_sum_1 id hwy1,
        Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      dsimp only [c]
      rw [Finset.sum_coe_sort s (fun v => c' v • v)]
      refine Finset.sum_congr rfl fun v hv => ?_
      simp only [c', cx, cy, hv, ↓reduceIte, id_eq, smul_smul, add_smul]
    have hd_comb : Finset.univ.affineCombination ℝ ((↑) : s → E) d = t.centerMass wz id := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hd_sum,
        t.centerMass_eq_of_sum_1 id hwz1]
      dsimp only [d]
      rw [Finset.sum_coe_sort s (fun v => cz v • v)]
      simp only [cz, ite_smul, zero_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hts, id_eq]
    have hcd_eq : Finset.univ.affineCombination ℝ ((↑) : s → E) c =
        Finset.univ.affineCombination ℝ ((↑) : s → E) d := by
      rw [hc_comb, hd_comb, hzeq, hwzeq]
    have hcd := hs.injOn_affineCombination_fintypeAffineCoords
      (mem_fintypeAffineCoords_iff_sum.2 hc_sum) (mem_fintypeAffineCoords_iff_sum.2 hd_sum) hcd_eq
    have hx_supp : ∀ v ∈ s, v ∉ t → wx v = 0 := by
      intro v hvs hvt
      have hcv := congrFun hcd ⟨v, hvs⟩
      have hdv : d ⟨v, hvs⟩ = 0 := by simp only [d, cz, hvt, ↓reduceIte]
      have hcv' : a * wx v + b * wy v = 0 := by
        simpa only [c, c', cx, cy, hvs, ↓reduceIte, hdv] using hcv
      have hax : 0 ≤ a * wx v := mul_nonneg ha.le (hwx0 v hvs)
      have hby : 0 ≤ b * wy v := mul_nonneg hb.le (hwy0 v hvs)
      have hax0 : a * wx v = 0 := by linarith
      exact (mul_eq_zero.1 hax0).resolve_left ha.ne'
    have htsum : ∑ v ∈ t, wx v = 1 := by
      rw [Finset.sum_subset hts fun v hvs hvt => hx_supp v hvs hvt]
      exact hwx1
    rw [Finset.convexHull_eq]
    refine ⟨wx, fun v hv => hwx0 v (hts hv), htsum, ?_⟩
    rw [t.centerMass_eq_of_sum_1 id htsum, s.centerMass_eq_of_sum_1 id hwx1]
    exact Finset.sum_subset hts fun v hvs hvt => by simp [hx_supp v hvs hvt]

theorem exists_isPolytopeFace_prod_eq {P : Set E} {Q : Set F} (hP : IsPolytope P)
    (hQ : IsPolytope Q) {G : Set (E × F)} (hG : IsPolytopeFace (P ×ˢ Q) G) (hne : G.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ G = P' ×ˢ Q' := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  let L₁ : Set (E × F →ᵃ[ℝ] ℝ) := (fun a : E →ᵃ[ℝ] ℝ => a.comp AffineMap.fst) '' LP
  let L₂ : Set (E × F →ᵃ[ℝ] ℝ) := (fun b : F →ᵃ[ℝ] ℝ => b.comp AffineMap.snd) '' LQ
  have hPReq : P ×ˢ Q = {p : E × F | ∀ ℓ ∈ L₁ ∪ L₂, ℓ p ≤ 0} := by
    ext ⟨x, y⟩
    simp only [mem_prod, mem_ofPred_eq, Set.mem_union, Set.mem_image, L₁, L₂]
    rw [hPeq, hQeq]
    constructor
    · rintro ⟨hx, hy⟩ _ (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact hx a ha
      · exact hy b hb
    · intro h
      exact ⟨fun a ha => h (a.comp AffineMap.fst) (.inl ⟨a, ha, rfl⟩),
        fun b hb => h (b.comp AffineMap.snd) (.inr ⟨b, hb, rfl⟩)⟩
  obtain ⟨K₀, hK₀, hGeq⟩ := hG.exists_eq_zero_of_isHPolytope
    ((hLP.image _).union (hLQ.image _)) hPReq (hP.prod hQ) hne
  let P' := {x ∈ P | ∀ a ∈ {a ∈ LP | a.comp AffineMap.fst ∈ K₀}, a x = 0}
  let Q' := {y ∈ Q | ∀ b ∈ {b ∈ LQ | b.comp AffineMap.snd ∈ K₀}, b y = 0}
  refine ⟨P', Q',
    isPolytopeFace_of_eq_zero hLP hPeq hP.convex (fun _ ha => ha.1),
    isPolytopeFace_of_eq_zero hLQ hQeq hQ.convex (fun _ hb => hb.1), ?_⟩
  rw [hGeq]
  ext ⟨x, y⟩
  simp only [P', Q', mem_prod, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hxP, hyQ⟩, hxy⟩
    exact ⟨⟨hxP, fun a ha => hxy _ ha.2⟩, ⟨hyQ, fun b hb => hxy _ hb.2⟩⟩
  · rintro ⟨⟨hxP, hx'⟩, ⟨hyQ, hy'⟩⟩
    refine ⟨⟨hxP, hyQ⟩, fun ℓ hℓ => ?_⟩
    rcases hK₀ hℓ with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
    · exact hx' a ⟨ha, hℓ⟩
    · exact hy' b ⟨hb, hℓ⟩

end FiniteDim

end Cslib.Polyhedra
