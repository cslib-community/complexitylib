/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/PolytopalComplex.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.Polyhedra.Polytope
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polytopal complexes, barycentric subdivision, polyhedra, and common refinements

This module develops finite polytopal complexes (`PolytopalComplex`), hyperplane-arrangement
splitting (`splitComplex`, `ofFinitePolytopes`), barycentric subdivision (`barycentricSubdivision`)
yielding a finite `Geometry.SimplicialComplex ℝ E`, compact polyhedra (`IsPolyhedron`), closure of
polyhedra under unions, intersections, products, affine images, and affine preimages, common
refinements of triangulations, and compatible triangulations of finite families of subpolyhedra.

## Main definitions

* `Cslib.Polyhedra.PolytopalComplex`: finite collection of nonempty compact polytopes closed under
  nonempty faces and intersecting in faces.
* `Cslib.Polyhedra.PolytopalComplex.barycentricSubdivision`: the barycentric subdivision of a
  polytopal complex as a `Geometry.SimplicialComplex ℝ E`.
* `Cslib.Polyhedra.PolytopalComplex.ofFinitePolytopes`: a hyperplane-arrangement polytopal complex
  covering any finite family of polytopes and respecting each member.
* `Cslib.Polyhedra.IsPolyhedron`: compact polyhedra, defined as underlying spaces of finite
  simplicial complexes.

## Main results

* `Cslib.Polyhedra.PolytopalComplex.barycentricSubdivision_space`: barycentric subdivision
  preserves the underlying space.
* `Cslib.Polyhedra.isPolyhedron_iff_finite_union_polytopes`,
  `Cslib.Polyhedra.isPolyhedron_iff_finite_union_simplices`,
  `Cslib.Polyhedra.isPolyhedron_iff_exists_polytopalComplex`: equivalent characterizations of
  compact polyhedra.
* `Cslib.Polyhedra.IsPolyhedron.union`, `Cslib.Polyhedra.IsPolyhedron.inter`,
  `Cslib.Polyhedra.IsPolyhedron.prod`, `Cslib.Polyhedra.IsPolyhedron.image`,
  `Cslib.Polyhedra.IsPolyhedron.preimage_inter`: closure of compact polyhedra.
* `Cslib.Polyhedra.exists_common_triangulation_of_complexes`,
  `Cslib.Polyhedra.exists_common_refinement_of_finite_complexes`,
  `Cslib.Polyhedra.exists_triangulation_compatible_with_subpolyhedra`: common refinements of
  triangulations and compatible triangulations of finite subpolyhedra.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
* Issue #4325 notes (`STOC 1056 Lemma B.1` label; unverified against the primary manuscript).
-/

public section

namespace Cslib.Polyhedra

open Set Finset

/-- A finite **polytopal complex** in `E` is a finite collection of nonempty compact polytopes
that contains all nonempty faces of its cells and intersects any two cells in a common face. -/
structure PolytopalComplex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The cells of the polytopal complex. -/
  cells : Set (Set E)
  /-- Finiteness of the cell family. -/
  finite_cells : cells.Finite
  /-- Every cell is a compact convex polytope. -/
  isPolytope_of_mem : ∀ {P}, P ∈ cells → IsPolytope P
  /-- Every cell is nonempty. -/
  nonempty_of_mem : ∀ {P}, P ∈ cells → P.Nonempty
  /-- Nonempty faces of cells belong to the complex. -/
  face_mem : ∀ {P F}, P ∈ cells → IsPolytopeFace P F → F.Nonempty → F ∈ cells
  /-- The intersection of any two cells is a face of the first. -/
  inter_face : ∀ {P Q}, P ∈ cells → Q ∈ cells → IsPolytopeFace P (P ∩ Q)

section BasicComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The underlying topological space of a polytopal complex. -/
@[expose] def PolytopalComplex.space (C : PolytopalComplex E) : Set E :=
  ⋃ P ∈ C.cells, P

theorem PolytopalComplex.mem_space_iff {C : PolytopalComplex E} {x : E} :
    x ∈ C.space ↔ ∃ P ∈ C.cells, x ∈ P := by
  simp only [PolytopalComplex.space, Set.mem_iUnion, exists_prop]

theorem PolytopalComplex.subset_space {C : PolytopalComplex E} {P : Set E} (hP : P ∈ C.cells) :
    P ⊆ C.space :=
  Set.subset_biUnion_of_mem (u := fun R : Set E => R) hP

theorem PolytopalComplex.isCompact_space (C : PolytopalComplex E) : IsCompact C.space :=
  C.finite_cells.isCompact_biUnion fun _ hP => (C.isPolytope_of_mem hP).isCompact

theorem PolytopalComplex.isClosed_space (C : PolytopalComplex E) : IsClosed C.space :=
  C.isCompact_space.isClosed

theorem PolytopalComplex.isBounded_space (C : PolytopalComplex E) :
    Bornology.IsBounded C.space :=
  C.isCompact_space.isBounded

/-- The empty polytopal complex. -/
def PolytopalComplex.empty : PolytopalComplex E where
  cells := ∅
  finite_cells := finite_empty
  isPolytope_of_mem h := False.elim h
  nonempty_of_mem h := False.elim h
  face_mem h := False.elim h
  inter_face h := False.elim h

@[simp]
theorem PolytopalComplex.space_empty : (PolytopalComplex.empty : PolytopalComplex E).space = ∅ :=
  Set.biUnion_empty _

/-- The polytopal complex consisting of all nonempty faces of a single polytope `P`. -/
def PolytopalComplex.ofPolytope [FiniteDimensional ℝ E] {P : Set E} (hP : IsPolytope P) :
    PolytopalComplex E where
  cells := {F | IsPolytopeFace P F ∧ F.Nonempty}
  finite_cells := by
    classical
    let V : Finset E := hP.finite_extremePoints.toFinset
    let mapFace : Set E → Finset E := fun F => V.filter (· ∈ F)
    have hmaps : MapsTo mapFace {F | IsPolytopeFace P F ∧ F.Nonempty}
        (V.powerset : Set (Finset E)) :=
      fun F _ => Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
    have hinj : InjOn mapFace {F | IsPolytopeFace P F ∧ F.Nonempty} := by
      intro F₁ hF₁ F₂ hF₂ heq
      have hVeq : P.extremePoints ℝ ∩ F₁ = P.extremePoints ℝ ∩ F₂ := by
        ext v
        constructor
        · intro ⟨hvP, hv1⟩
          have hvV : v ∈ V := hP.finite_extremePoints.mem_toFinset.2 hvP
          have hv2 : v ∈ mapFace F₂ := heq ▸ Finset.mem_filter.2 ⟨hvV, hv1⟩
          exact ⟨hvP, (Finset.mem_filter.1 hv2).2⟩
        · intro ⟨hvP, hv2⟩
          have hvV : v ∈ V := hP.finite_extremePoints.mem_toFinset.2 hvP
          have hv1 : v ∈ mapFace F₁ := heq.symm ▸ Finset.mem_filter.2 ⟨hvV, hv2⟩
          exact ⟨hvP, (Finset.mem_filter.1 hv1).2⟩
      rw [hF₁.1.eq_convexHull_extremePoints_inter hP,
        hF₂.1.eq_convexHull_extremePoints_inter hP, hVeq]
    exact (Finset.finite_toSet V.powerset).of_injOn hmaps hinj
  isPolytope_of_mem h := h.1.isPolytope hP
  nonempty_of_mem h := h.2
  face_mem h1 h2 hne := ⟨h1.1.trans h2, hne⟩
  inter_face h1 h2 := (h1.1.inter h2.1).mono h1.1.subset inter_subset_left

@[simp]
theorem PolytopalComplex.space_ofPolytope [FiniteDimensional ℝ E] {P : Set E} (hP : IsPolytope P) :
    (PolytopalComplex.ofPolytope hP).space = P := by
  refine Subset.antisymm (Set.iUnion₂_subset fun _ h => h.1.subset) fun x hx => ?_
  exact Set.mem_biUnion ⟨IsPolytopeFace.refl hP.convex, ⟨x, hx⟩⟩ hx

/-- Convert a finite simplicial complex into a polytopal complex of its simplices. -/
def PolytopalComplex.ofSimplicialComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hfin : K.faces.Finite) : PolytopalComplex E where
  cells := (fun s : Finset E => convexHull ℝ (s : Set E)) '' K.faces
  finite_cells := hfin.image _
  isPolytope_of_mem := by
    rintro _ ⟨s, _, rfl⟩
    exact isPolytope_convexHull s.finite_toSet
  nonempty_of_mem := by
    rintro _ ⟨s, hs, rfl⟩
    exact (convexHull_nonempty_iff.2 ((K.isRelLowerSet_faces hs).1))
  face_mem := by
    rintro _ F ⟨s, hs, rfl⟩ hSF hFne
    obtain ⟨t, hts, rfl⟩ := (IsPolytopeFace.simplex_convexHull_iff (K.indep hs)).1 hSF
    have htne : t.Nonempty := by
      by_contra hmt
      rw [Finset.not_nonempty_iff_eq_empty] at hmt
      rw [hmt, Finset.coe_empty, convexHull_empty] at hFne
      exact hFne.ne_empty rfl
    exact ⟨t, K.down_closed hs hts htne, rfl⟩
  inter_face := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    classical
    dsimp only
    rw [K.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
    exact (IsPolytopeFace.simplex_convexHull_iff (K.indep hs)).2
      ⟨s ∩ t, Finset.inter_subset_left, by rw [Finset.coe_inter]⟩

@[simp]
theorem PolytopalComplex.cells_ofSimplicialComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hfin : K.faces.Finite) :
    (PolytopalComplex.ofSimplicialComplex K hfin).cells =
      (fun s : Finset E => convexHull ℝ (s : Set E)) '' K.faces := by
  rfl

@[simp]
theorem PolytopalComplex.space_ofSimplicialComplex [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hfin : K.faces.Finite) :
    (PolytopalComplex.ofSimplicialComplex K hfin).space = K.space := by
  ext x
  simp only [PolytopalComplex.space, PolytopalComplex.ofSimplicialComplex,
    Geometry.SimplicialComplex.space, Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨convexHull ℝ (s : Set E), ⟨s, hs, rfl⟩, hx⟩

/-- The Cartesian product of two polytopal complexes. -/
def PolytopalComplex.prod [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : PolytopalComplex E) (D : PolytopalComplex F) : PolytopalComplex (E × F) where
  cells := {R | ∃ P ∈ C.cells, ∃ Q ∈ D.cells, R = P ×ˢ Q}
  finite_cells := by
    let pairCells : Set (Set E × Set F) := C.cells ×ˢ D.cells
    have hfin : pairCells.Finite := C.finite_cells.prod D.finite_cells
    have hsub : {R : Set (E × F) | ∃ P ∈ C.cells, ∃ Q ∈ D.cells, R = P ×ˢ Q} =
        (fun p : Set E × Set F => p.1 ×ˢ p.2) '' pairCells := by
      ext R
      simp only [mem_ofPred_eq, Set.mem_image, pairCells, Set.mem_prod, Prod.exists]
      exact ⟨fun ⟨P, hP, Q, hQ, hR⟩ => ⟨P, Q, ⟨hP, hQ⟩, hR.symm⟩,
        fun ⟨P, Q, ⟨hP, hQ⟩, hR⟩ => ⟨P, hP, Q, hQ, hR.symm⟩⟩
    rw [hsub]
    exact hfin.image _
  isPolytope_of_mem := by
    rintro _ ⟨P, hP, Q, hQ, rfl⟩
    exact (C.isPolytope_of_mem hP).prod (D.isPolytope_of_mem hQ)
  nonempty_of_mem := by
    rintro _ ⟨P, hP, Q, hQ, rfl⟩
    exact (C.nonempty_of_mem hP).prod (D.nonempty_of_mem hQ)
  face_mem := by
    rintro _ G ⟨P, hP, Q, hQ, rfl⟩ hG hGne
    obtain ⟨P', Q', hPP', hQQ', rfl⟩ :=
      exists_isPolytopeFace_prod_eq (C.isPolytope_of_mem hP) (D.isPolytope_of_mem hQ) hG hGne
    obtain ⟨⟨x, y⟩, hxy⟩ := hGne
    exact ⟨P', C.face_mem hP hPP' ⟨x, hxy.1⟩, Q', D.face_mem hQ hQQ' ⟨y, hxy.2⟩, rfl⟩
  inter_face := by
    rintro _ _ ⟨P₁, hP₁, Q₁, hQ₁, rfl⟩ ⟨P₂, hP₂, Q₂, hQ₂, rfl⟩
    rw [Set.prod_inter_prod]
    exact (C.inter_face hP₁ hP₂).prod (D.inter_face hQ₁ hQ₂)

@[simp]
theorem PolytopalComplex.space_prod [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : PolytopalComplex E) (D : PolytopalComplex F) :
    (C.prod D).space = C.space ×ˢ D.space := by
  ext ⟨x, y⟩
  simp only [PolytopalComplex.space, PolytopalComplex.prod, Set.mem_iUnion, Set.mem_prod,
    mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨_, ⟨P, hP, Q, hQ, rfl⟩, hx, hy⟩
    exact ⟨⟨P, hP, hx⟩, ⟨Q, hQ, hy⟩⟩
  · rintro ⟨⟨P, hP, hx⟩, ⟨Q, hQ, hy⟩⟩
    exact ⟨P ×ˢ Q, ⟨P, hP, Q, hQ, rfl⟩, hx, hy⟩

end BasicComplex

section HyperplaneSplit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private lemma isPolytopeFace_halfSpace_inter (ℓ : E →ᵃ[ℝ] ℝ) {R₁ R₂ : Set E}
    (h₁ : R₁ = {x | ℓ x ≤ 0} ∨ R₁ = {x | 0 ≤ ℓ x} ∨ R₁ = {x | ℓ x = 0})
    (h₂ : R₂ = {x | ℓ x ≤ 0} ∨ R₂ = {x | 0 ≤ ℓ x} ∨ R₂ = {x | ℓ x = 0}) :
    IsPolytopeFace R₁ (R₁ ∩ R₂) := by
  have hL : {x | ℓ x ≤ 0} = {x | ∀ m ∈ ({ℓ} : Set _), m x ≤ 0} := by
    ext x; simp only [mem_ofPred_eq, mem_singleton_iff, forall_eq]
  have hG : {x | 0 ≤ ℓ x} = {x | ∀ m ∈ ({-ℓ} : Set _), m x ≤ 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_singleton_iff, forall_eq, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonpos]
  have hZ : {x | ℓ x = 0} = {x | ∀ m ∈ ({ℓ, -ℓ} : Set _), m x ≤ 0} := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
      AffineMap.coe_neg, Pi.neg_apply, neg_nonpos, le_antisymm_iff]
  have hface_le : IsPolytopeFace {x | ℓ x ≤ 0} {x | ℓ x = 0} := by
    have h := isPolytopeFace_of_eq_zero (LR := {ℓ}) (finite_singleton ℓ)
      hL (hL ▸ convex_setOf_forall_le {ℓ}) (Subset.refl {ℓ})
    have heq : {x ∈ {x | ℓ x ≤ 0} | ∀ m ∈ ({ℓ} : Set _), m x = 0} = {x | ℓ x = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff, forall_eq, and_iff_right_iff_imp]
      exact fun h0 => le_of_eq h0
    rwa [heq] at h
  have hface_ge : IsPolytopeFace {x | 0 ≤ ℓ x} {x | ℓ x = 0} := by
    have h := isPolytopeFace_of_eq_zero (LR := {-ℓ}) (finite_singleton (-ℓ))
      hG (hG ▸ convex_setOf_forall_le {-ℓ}) (Subset.refl {-ℓ})
    have heq : {x ∈ {x | 0 ≤ ℓ x} | ∀ m ∈ ({-ℓ} : Set _), m x = 0} = {x | ℓ x = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff, forall_eq, AffineMap.coe_neg, Pi.neg_apply,
        neg_eq_zero, and_iff_right_iff_imp]
      exact fun h0 => le_of_eq h0.symm
    rwa [heq] at h
  have hc1 : Convex ℝ R₁ := by
    rcases h₁ with rfl | rfl | rfl
    · exact hL ▸ convex_setOf_forall_le {ℓ}
    · exact hG ▸ convex_setOf_forall_le {-ℓ}
    · exact hZ ▸ convex_setOf_forall_le {ℓ, -ℓ}
  have hLG : {x | ℓ x ≤ 0} ∩ {x | 0 ≤ ℓ x} = {x | ℓ x = 0} := by
    ext x; simp only [mem_inter_iff, mem_ofPred_eq, le_antisymm_iff]
  have hGL : {x | 0 ≤ ℓ x} ∩ {x | ℓ x ≤ 0} = {x | ℓ x = 0} := by
    ext x; simp only [mem_inter_iff, mem_ofPred_eq, le_antisymm_iff, and_comm]
  have hLZ : {x | ℓ x ≤ 0} ∩ {x | ℓ x = 0} = {x | ℓ x = 0} := by
    ext x; exact ⟨fun h => h.2, fun h => ⟨le_of_eq h, h⟩⟩
  have hGZ : {x | 0 ≤ ℓ x} ∩ {x | ℓ x = 0} = {x | ℓ x = 0} := by
    ext x; exact ⟨fun h => h.2, fun h => ⟨le_of_eq h.symm, h⟩⟩
  have hZL : {x | ℓ x = 0} ∩ {x | ℓ x ≤ 0} = {x | ℓ x = 0} := by
    ext x; exact ⟨fun h => h.1, fun h => ⟨h, le_of_eq h⟩⟩
  have hZG : {x | ℓ x = 0} ∩ {x | 0 ≤ ℓ x} = {x | ℓ x = 0} := by
    ext x; exact ⟨fun h => h.1, fun h => ⟨h, le_of_eq h.symm⟩⟩
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl
  · rw [Set.inter_self]; exact IsPolytopeFace.refl hc1
  · rwa [hLG]
  · rwa [hLZ]
  · rwa [hGL]
  · rw [Set.inter_self]; exact IsPolytopeFace.refl hc1
  · rwa [hGZ]
  · rw [hZL]; exact IsPolytopeFace.refl hc1
  · rw [hZG]; exact IsPolytopeFace.refl hc1
  · rw [Set.inter_self]; exact IsPolytopeFace.refl hc1

private def halfSpaceLR (ℓ : E →ᵃ[ℝ] ℝ) (k : Fin 3) : Set (E →ᵃ[ℝ] ℝ) :=
  match k with
  | 0 => {ℓ}
  | 1 => {-ℓ}
  | 2 => {ℓ, -ℓ}

omit [FiniteDimensional ℝ E] in
private lemma halfSpaceLR_finite (ℓ : E →ᵃ[ℝ] ℝ) (k : Fin 3) : (halfSpaceLR ℓ k).Finite := by
  fin_cases k
  · exact finite_singleton _
  · exact finite_singleton _
  · exact (finite_singleton _).insert _

private def halfSpaceSet (ℓ : E →ᵃ[ℝ] ℝ) (k : Fin 3) : Set E :=
  match k with
  | 0 => {x | ℓ x ≤ 0}
  | 1 => {x | 0 ≤ ℓ x}
  | 2 => {x | ℓ x = 0}

omit [FiniteDimensional ℝ E] in
private lemma halfSpaceSet_eq (ℓ : E →ᵃ[ℝ] ℝ) (k : Fin 3) :
    halfSpaceSet ℓ k = {x | ∀ m ∈ halfSpaceLR ℓ k, m x ≤ 0} := by
  fin_cases k <;> ext x <;>
    simp [halfSpaceSet, halfSpaceLR, AffineMap.coe_neg, Pi.neg_apply, le_antisymm_iff]

/-- Cells obtained by slicing every cell of `C` with the hyperplane `{x | ℓ x = 0}` and its
two closed half-spaces. -/
private def splitCells (C : PolytopalComplex E) (ℓ : E →ᵃ[ℝ] ℝ) : Set (Set E) :=
  {Q | ∃ P ∈ C.cells, ∃ k : Fin 3, Q = P ∩ halfSpaceSet ℓ k ∧ Q.Nonempty}

/-- Refine a polytopal complex by slicing every cell along the affine hyperplane `{x | ℓ x = 0}`. -/
def PolytopalComplex.splitComplex (C : PolytopalComplex E) (ℓ : E →ᵃ[ℝ] ℝ) :
    PolytopalComplex E where
  cells := splitCells C ℓ
  finite_cells := by
    let f : Set E × Fin 3 → Set E := fun p => p.1 ∩ halfSpaceSet ℓ p.2
    have hfin : (C.cells ×ˢ (Set.univ : Set (Fin 3))).Finite :=
      C.finite_cells.prod finite_univ
    refine (hfin.image f).subset ?_
    rintro Q ⟨P, hP, k, rfl, _⟩
    exact ⟨(P, k), ⟨hP, Set.mem_univ k⟩, rfl⟩
  isPolytope_of_mem := by
    rintro Q ⟨P, hP, k, rfl, _⟩
    rw [halfSpaceSet_eq]
    exact (C.isPolytope_of_mem hP).inter_setOf_le (halfSpaceLR_finite ℓ k)
  nonempty_of_mem := by
    rintro _ ⟨_, _, _, _, hne⟩
    exact hne
  face_mem := by
    rintro Q F ⟨P, hP, k, rfl, _⟩ hF hFne
    have hR := halfSpaceSet_eq ℓ k
    obtain ⟨P', L₀, hPP', hL₀, hFeq⟩ := exists_isPolytopeFace_inter_setOf_le_eq_zero
      (C.isPolytope_of_mem hP) (halfSpaceLR_finite ℓ k) hR hF hFne
    have hP'mem : P' ∈ C.cells := by
      obtain ⟨x, hx⟩ := hFne
      exact C.face_mem hP hPP' ⟨x, (hFeq ▸ hx).1⟩
    fin_cases k
    · rcases eq_empty_or_nonempty L₀ with rfl | ⟨m, hm⟩
      · refine ⟨P', hP'mem, 0, ?_, hFne⟩
        rw [hFeq]; ext x; simp [halfSpaceSet]
      · have hm' : m = ℓ := hL₀ hm
        subst hm'
        refine ⟨P', hP'mem, 2, ?_, hFne⟩
        rw [hFeq]; ext x
        simp only [halfSpaceSet, mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
        intro _
        exact ⟨fun h => h.2 m hm, fun h => ⟨le_of_eq h, fun _ hn => (hL₀ hn) ▸ h⟩⟩
    · rcases eq_empty_or_nonempty L₀ with rfl | ⟨m, hm⟩
      · refine ⟨P', hP'mem, 1, ?_, hFne⟩
        rw [hFeq]; ext x; simp [halfSpaceSet]
      · have hm' : m = -ℓ := hL₀ hm
        subst hm'
        refine ⟨P', hP'mem, 2, ?_, hFne⟩
        rw [hFeq]; ext x
        simp only [halfSpaceSet, mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
        intro _
        constructor
        · intro h
          have : (-ℓ) x = 0 := h.2 (-ℓ) hm
          simpa [AffineMap.coe_neg] using this
        · intro h
          refine ⟨le_of_eq h.symm, fun n hn => ?_⟩
          have hn' : n = -ℓ := hL₀ hn
          subst hn'
          simp [AffineMap.coe_neg, h]
    · refine ⟨P', hP'mem, 2, ?_, hFne⟩
      rw [hFeq]; ext x
      simp only [halfSpaceSet, mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
      intro _
      refine ⟨fun h => h.1, fun h => ⟨h, fun n hn => ?_⟩⟩
      rcases hL₀ hn with rfl | rfl
      · exact h
      · simp [AffineMap.coe_neg, h]
  inter_face := by
    rintro Q₁ Q₂ ⟨P₁, hP₁, k₁, rfl, _⟩ ⟨P₂, hP₂, k₂, rfl, _⟩
    rw [inter_inter_inter_comm]
    have h₁ : halfSpaceSet ℓ k₁ = {x | ℓ x ≤ 0} ∨
        halfSpaceSet ℓ k₁ = {x | 0 ≤ ℓ x} ∨ halfSpaceSet ℓ k₁ = {x | ℓ x = 0} := by
      fin_cases k₁ <;> simp [halfSpaceSet]
    have h₂ : halfSpaceSet ℓ k₂ = {x | ℓ x ≤ 0} ∨
        halfSpaceSet ℓ k₂ = {x | 0 ≤ ℓ x} ∨ halfSpaceSet ℓ k₂ = {x | ℓ x = 0} := by
      fin_cases k₂ <;> simp [halfSpaceSet]
    exact (C.inter_face hP₁ hP₂).inter_inter (isPolytopeFace_halfSpace_inter ℓ h₁ h₂)

theorem PolytopalComplex.space_splitComplex (C : PolytopalComplex E) (ℓ : E →ᵃ[ℝ] ℝ) :
    (C.splitComplex ℓ).space = C.space := by
  ext x
  simp only [PolytopalComplex.mem_space_iff, PolytopalComplex.splitComplex, splitCells,
    mem_ofPred_eq]
  constructor
  · rintro ⟨Q, ⟨P, hP, _, rfl, _⟩, hx, _⟩
    exact ⟨P, hP, hx⟩
  · rintro ⟨P, hP, hxP⟩
    rcases le_total (ℓ x) 0 with hle | hge
    · exact ⟨P ∩ halfSpaceSet ℓ 0, ⟨P, hP, 0, rfl, ⟨x, hxP, hle⟩⟩, hxP, hle⟩
    · exact ⟨P ∩ halfSpaceSet ℓ 1, ⟨P, hP, 1, rfl, ⟨x, hxP, hge⟩⟩, hxP, hge⟩

theorem PolytopalComplex.splitComplex_subset {C : PolytopalComplex E} {ℓ : E →ᵃ[ℝ] ℝ} {Q : Set E}
    (hQ : Q ∈ (C.splitComplex ℓ).cells) : ∃ P ∈ C.cells, Q ⊆ P := by
  rcases hQ with ⟨P, hP, _, rfl, _⟩
  exact ⟨P, hP, inter_subset_left⟩

theorem PolytopalComplex.splitComplex_signs {C : PolytopalComplex E} {ℓ : E →ᵃ[ℝ] ℝ} {Q : Set E}
    (hQ : Q ∈ (C.splitComplex ℓ).cells) :
    (∀ x ∈ Q, ℓ x ≤ 0) ∨ (∀ x ∈ Q, 0 ≤ ℓ x) := by
  rcases hQ with ⟨P, _, k, rfl, _⟩
  fin_cases k
  · left; intro x hx; exact hx.2
  · right; intro x hx; exact hx.2
  · left; intro x hx; exact le_of_eq hx.2

/-- Fold `splitComplex` over a list of affine functionals. -/
def PolytopalComplex.splitList (C : PolytopalComplex E) (ls : List (E →ᵃ[ℝ] ℝ)) :
    PolytopalComplex E :=
  ls.foldl PolytopalComplex.splitComplex C

theorem PolytopalComplex.space_splitList (C : PolytopalComplex E) (ls : List (E →ᵃ[ℝ] ℝ)) :
    (C.splitList ls).space = C.space := by
  induction ls generalizing C with
  | nil => rfl
  | cons ℓ ls ih =>
    simp only [PolytopalComplex.splitList, List.foldl_cons]
    change ((C.splitComplex ℓ).splitList ls).space = C.space
    rw [ih, C.space_splitComplex]

theorem PolytopalComplex.splitList_subset (C : PolytopalComplex E) (ls : List (E →ᵃ[ℝ] ℝ))
    {Q : Set E} (hQ : Q ∈ (C.splitList ls).cells) : ∃ P ∈ C.cells, Q ⊆ P := by
  induction ls generalizing C Q with
  | nil => exact ⟨Q, hQ, Subset.refl _⟩
  | cons ℓ ls ih =>
    simp only [PolytopalComplex.splitList, List.foldl_cons] at hQ
    obtain ⟨R, hR, hQR⟩ := ih (C.splitComplex ℓ) hQ
    obtain ⟨P, hP, hRP⟩ := C.splitComplex_subset hR
    exact ⟨P, hP, hQR.trans hRP⟩

theorem PolytopalComplex.splitList_signs (C : PolytopalComplex E) (ls : List (E →ᵃ[ℝ] ℝ))
    {ℓ : E →ᵃ[ℝ] ℝ} (hℓ : ℓ ∈ ls) {Q : Set E} (hQ : Q ∈ (C.splitList ls).cells) :
    (∀ x ∈ Q, ℓ x ≤ 0) ∨ (∀ x ∈ Q, 0 ≤ ℓ x) := by
  induction ls generalizing C Q with
  | nil => simp at hℓ
  | cons m ls ih =>
    simp only [PolytopalComplex.splitList, List.foldl_cons] at hQ
    rcases List.mem_cons.1 hℓ with rfl | hmem
    · obtain ⟨R, hR, hQR⟩ := splitList_subset (C.splitComplex ℓ) ls hQ
      rcases C.splitComplex_signs hR with hle | hge
      · left; exact fun x hx => hle x (hQR hx)
      · right; exact fun x hx => hge x (hQR hx)
    · exact ih (C.splitComplex m) hmem hQ

/-- Cells whose H-representation uses only inequalities from `M`. -/
private def IsHRepIn (M : Set (E →ᵃ[ℝ] ℝ)) (P : Set E) : Prop :=
  ∃ L ⊆ M, L.Finite ∧ P = {x | ∀ ℓ ∈ L, ℓ x ≤ 0}

omit [FiniteDimensional ℝ E] in
private lemma isHRepIn_mono {M₁ M₂ : Set (E →ᵃ[ℝ] ℝ)} (hM : M₁ ⊆ M₂) {P : Set E}
    (hP : IsHRepIn M₁ P) : IsHRepIn M₂ P := by
  rcases hP with ⟨L, hLM, hLfin, hPeq⟩
  exact ⟨L, hLM.trans hM, hLfin, hPeq⟩

private lemma isHRepIn_ofPolytope {P : Set E} {LP : Set (E →ᵃ[ℝ] ℝ)} (hLP : LP.Finite)
    (hPeq : P = {x | ∀ ℓ ∈ LP, ℓ x ≤ 0}) (hP : IsPolytope P)
    {F : Set E} (hPF : IsPolytopeFace P F) (hFne : F.Nonempty) :
    IsHRepIn (LP ∪ Neg.neg '' LP) F := by
  obtain ⟨L₀, hL₀, hFeq⟩ := hPF.exists_eq_zero_of_isHPolytope hLP hPeq hP hFne
  refine ⟨LP ∪ Neg.neg '' L₀, ?_, hLP.union ((hLP.subset hL₀).image _), ?_⟩
  · exact union_subset subset_union_left (Subset.trans (image_mono hL₀) subset_union_right)
  · rw [hFeq]
    ext x
    simp only [mem_ofPred_eq, Set.mem_union, Set.mem_image]
    rw [hPeq]
    constructor
    · rintro ⟨hxP, hx0⟩ ℓ (hℓ | ⟨m, hm, rfl⟩)
      · exact hxP ℓ hℓ
      · simp [AffineMap.coe_neg, hx0 m hm]
    · intro h
      refine ⟨fun ℓ hℓ => h ℓ (.inl hℓ), fun m hm => ?_⟩
      have h1 : m x ≤ 0 := h m (.inl (hL₀ hm))
      have h2 : (-m) x ≤ 0 := h (-m) (.inr ⟨m, hm, rfl⟩)
      simp only [AffineMap.coe_neg, Pi.neg_apply, neg_nonpos] at h2
      exact le_antisymm h1 h2

private lemma isHRepIn_splitComplex {C : PolytopalComplex E} {M : Set (E →ᵃ[ℝ] ℝ)}
    (hM : ∀ P ∈ C.cells, IsHRepIn M P) (ℓ : E →ᵃ[ℝ] ℝ) :
    ∀ Q ∈ (C.splitComplex ℓ).cells, IsHRepIn (M ∪ {ℓ, -ℓ}) Q := by
  rintro Q ⟨P, hP, k, rfl, _⟩
  obtain ⟨LP, hLM, hLP, hPeq⟩ := hM P hP
  refine ⟨LP ∪ halfSpaceLR ℓ k, ?_, hLP.union (halfSpaceLR_finite ℓ k), ?_⟩
  · refine union_subset (hLM.trans subset_union_left) ?_
    fin_cases k
    · exact Subset.trans (by simp [halfSpaceLR]) subset_union_right
    · exact Subset.trans (by simp [halfSpaceLR]) subset_union_right
    · exact Subset.trans (by simp [halfSpaceLR]) subset_union_right
  · rw [halfSpaceSet_eq ℓ k]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union]
    rw [hPeq]
    exact ⟨fun ⟨h1, h2⟩ m hm => hm.elim (h1 m) (h2 m),
      fun h => ⟨fun m hm => h m (.inl hm), fun m hm => h m (.inr hm)⟩⟩

private lemma isHRepIn_splitList {C : PolytopalComplex E} {M : Set (E →ᵃ[ℝ] ℝ)}
    (hM : ∀ P ∈ C.cells, IsHRepIn M P) (ls : List (E →ᵃ[ℝ] ℝ)) :
    ∀ Q ∈ (C.splitList ls).cells,
      IsHRepIn (M ∪ {m | ∃ ℓ ∈ ls, m = ℓ ∨ m = -ℓ}) Q := by
  induction ls generalizing C M with
  | nil =>
    intro Q hQ
    exact isHRepIn_mono subset_union_left (hM Q hQ)
  | cons ℓ ls ih =>
    intro Q hQ
    simp only [PolytopalComplex.splitList, List.foldl_cons] at hQ
    have hsplit := ih (isHRepIn_splitComplex hM ℓ) Q hQ
    refine isHRepIn_mono ?_ hsplit
    rintro m (hm | ⟨r, hr, hrm⟩)
    · rcases hm with hm | (h1 | h2)
      · exact .inl hm
      · exact .inr ⟨ℓ, List.mem_cons_self, .inl h1⟩
      · exact .inr ⟨ℓ, List.mem_cons_self, .inr h2⟩
    · exact .inr ⟨r, List.mem_cons_of_mem _ hr, hrm⟩

private lemma inter_face_of_split_hRep {Q₁ Q₂ : Set E} {M : Set (E →ᵃ[ℝ] ℝ)}
    (hQ₁ : IsPolytope Q₁) (hQ₂rep : IsHRepIn M Q₂)
    (hsplit : ∀ m ∈ M, (∀ x ∈ Q₁, m x ≤ 0) ∨ (∀ x ∈ Q₁, 0 ≤ m x)) :
    IsPolytopeFace Q₁ (Q₁ ∩ Q₂) := by
  classical
  obtain ⟨_, L₁, hL₁, hQ₁eq⟩ := isPolytope_iff_isHPolytope.1 hQ₁
  obtain ⟨L₂, hL₂M, hL₂fin, hQ₂eq⟩ := hQ₂rep
  let B : Set (E →ᵃ[ℝ] ℝ) := {m ∈ L₂ | ¬∀ y ∈ Q₁, m y ≤ 0}
  have hBge : ∀ m ∈ B, ∀ y ∈ Q₁, (-m) y ≤ 0 := by
    intro m hm y hy
    rcases hsplit m (hL₂M hm.1) with hle | hge
    · exact False.elim (hm.2 hle)
    · simpa [AffineMap.coe_neg] using hge y hy
  let L₁' := L₁ ∪ Neg.neg '' B
  have hL₁'fin : L₁'.Finite := hL₁.union ((hL₂fin.subset fun _ (h : _ ∈ B) => h.1).image _)
  have hQ₁eq' : Q₁ = {x | ∀ ℓ ∈ L₁', ℓ x ≤ 0} := by
    ext x
    simp only [L₁', Set.mem_union, Set.mem_image, mem_ofPred_eq]
    constructor
    · rintro hx ℓ (hℓ | ⟨m, hm, rfl⟩)
      · exact (hQ₁eq ▸ hx) ℓ hℓ
      · exact hBge m hm x hx
    · intro h
      rw [hQ₁eq]
      exact fun ℓ hℓ => h ℓ (.inl hℓ)
  have hface := isPolytopeFace_of_eq_zero hL₁'fin hQ₁eq' hQ₁.convex subset_union_right
  convert hface using 1
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_image, B]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    rintro _ ⟨m, ⟨hm2, hnle⟩, rfl⟩
    have hle : m x ≤ 0 := (hQ₂eq ▸ hx2) m hm2
    rcases hsplit m (hL₂M hm2) with h_abs | hge
    · exact False.elim (hnle h_abs)
    · simp only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
      exact le_antisymm hle (hge x hx1)
  · rintro ⟨hx1, hx0⟩
    refine ⟨hx1, ?_⟩
    rw [hQ₂eq]
    intro m hm2
    by_cases hle : ∀ y ∈ Q₁, m y ≤ 0
    · exact hle x hx1
    · have h0 := hx0 (-m) ⟨m, ⟨hm2, hle⟩, rfl⟩
      simp only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] at h0
      exact le_of_eq h0

private lemma split_subset_of_vertexCentroid_mem {Q P : Set E} (hQ : IsPolytope Q)
    (hQne : Q.Nonempty)
    {LP : Set (E →ᵃ[ℝ] ℝ)} (hPeq : P = {x | ∀ ℓ ∈ LP, ℓ x ≤ 0})
    (hsplit : ∀ ℓ ∈ LP, (∀ x ∈ Q, ℓ x ≤ 0) ∨ (∀ x ∈ Q, 0 ≤ ℓ x))
    (hbP : vertexCentroid Q ∈ P) : Q ⊆ P := by
  rw [hPeq]
  intro x hxQ ℓ hℓ
  rcases hsplit ℓ hℓ with hle | hge
  · exact hle x hxQ
  · by_contra! hpos
    have hb_le : ℓ (vertexCentroid Q) ≤ 0 := (hPeq ▸ hbP) ℓ hℓ
    have hneg_le : ∀ z ∈ Q, (-ℓ) z ≤ 0 := fun z hz => by
      simpa [AffineMap.coe_neg] using hge z hz
    have hneg_lt : (-ℓ) x < 0 := by simpa [AffineMap.coe_neg] using hpos
    have hblt := hQ.apply_vertexCentroid_lt hQne hneg_le hxQ hneg_lt
    simp only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] at hblt
    linarith

private noncomputable def allHyperplanes {ℱ : Set (Set E)} (hℱ : ℱ.Finite) :
    Finset (E →ᵃ[ℝ] ℝ) :=
  letI := Classical.propDecidable
  hℱ.toFinset.biUnion fun P =>
    if hP : IsHPolytope P then hP.2.choose_spec.1.toFinset else ∅

omit [FiniteDimensional ℝ E] in
private lemma mem_allHyperplanes_of_hPoly {ℱ : Set (Set E)} (hℱ : ℱ.Finite) {P : Set E}
    (hP : P ∈ ℱ) (hHP : IsHPolytope P) {ℓ : E →ᵃ[ℝ] ℝ} (hℓ : ℓ ∈ hHP.2.choose) :
    ℓ ∈ allHyperplanes hℱ := by
  classical
  refine Finset.mem_biUnion.2 ⟨P, hℱ.mem_toFinset.2 hP, ?_⟩
  simp only [dite_eq_left hHP]
  exact hHP.2.choose_spec.1.mem_toFinset.2 hℓ

/-- Given a finite family `ℱ` of compact convex polytopes, construct a single polytopal complex
whose space is `⋃ P ∈ ℱ, P`, refining each member of `ℱ` cleanly along its bounding
half-spaces. -/
noncomputable def PolytopalComplex.ofFinitePolytopes {ℱ : Set (Set E)} (hℱ : ℱ.Finite)
    (hpoly : ∀ P ∈ ℱ, IsPolytope P) : PolytopalComplex E :=
  letI := Classical.propDecidable
  let allL : Finset (E →ᵃ[ℝ] ℝ) := allHyperplanes hℱ
  let ls : List (E →ᵃ[ℝ] ℝ) := allL.toList
  let pieces : Set E → PolytopalComplex E := fun P =>
    if h : P ∈ ℱ then (PolytopalComplex.ofPolytope (hpoly P h)).splitList ls else
      PolytopalComplex.empty
  { cells := ⋃ P ∈ ℱ, (pieces P).cells
    finite_cells := hℱ.biUnion fun P _ => (pieces P).finite_cells
    isPolytope_of_mem := by
      rintro Q hQ
      rw [Set.mem_iUnion₂] at hQ
      rcases hQ with ⟨P, _, hQP⟩
      exact (pieces P).isPolytope_of_mem hQP
    nonempty_of_mem := by
      rintro Q hQ
      rw [Set.mem_iUnion₂] at hQ
      rcases hQ with ⟨P, _, hQP⟩
      exact (pieces P).nonempty_of_mem hQP
    face_mem := by
      rintro Q F hQ hQF hFne
      rw [Set.mem_iUnion₂] at hQ ⊢
      rcases hQ with ⟨P, hP, hQP⟩
      exact ⟨P, hP, (pieces P).face_mem hQP hQF hFne⟩
    inter_face := by
      rintro Q₁ Q₂ hQ₁ hQ₂
      rw [Set.mem_iUnion₂] at hQ₁ hQ₂
      rcases hQ₁ with ⟨P₁, hP₁, hQ₁P⟩
      rcases hQ₂ with ⟨P₂, hP₂, hQ₂P⟩
      let M : Set (E →ᵃ[ℝ] ℝ) :=
        (allL : Set (E →ᵃ[ℝ] ℝ)) ∪ Neg.neg '' (allL : Set (E →ᵃ[ℝ] ℝ))
      have hrep : ∀ {P : Set E} (hP : P ∈ ℱ),
          ∀ R ∈ (PolytopalComplex.ofPolytope (hpoly P hP)).cells, IsHRepIn M R := by
        intro P hP R hR
        have hHP : IsHPolytope P := isPolytope_iff_isHPolytope.1 (hpoly P hP)
        let LP : Set (E →ᵃ[ℝ] ℝ) := hHP.2.choose
        have hLPfin : LP.Finite := hHP.2.choose_spec.1
        have hPeq : P = {x | ∀ ℓ ∈ LP, ℓ x ≤ 0} := hHP.2.choose_spec.2
        have hL_all : LP ⊆ (allL : Set (E →ᵃ[ℝ] ℝ)) := fun ℓ hℓ =>
          Finset.mem_coe.2 (mem_allHyperplanes_of_hPoly hℱ hP hHP hℓ)
        have hsubM : LP ∪ Neg.neg '' LP ⊆ M :=
          union_subset (hL_all.trans subset_union_left)
            ((image_mono hL_all).trans subset_union_right)
        exact isHRepIn_mono hsubM (isHRepIn_ofPolytope hLPfin hPeq (hpoly P hP) hR.1 hR.2)
      have hQ₁p : Q₁ ∈ ((PolytopalComplex.ofPolytope (hpoly P₁ hP₁)).splitList ls).cells := by
        simpa only [pieces, dite_eq_left hP₁] using hQ₁P
      have hQ₂p : Q₂ ∈ ((PolytopalComplex.ofPolytope (hpoly P₂ hP₂)).splitList ls).cells := by
        simpa only [pieces, dite_eq_left hP₂] using hQ₂P
      have hQ₂M : IsHRepIn M Q₂ := by
        have hsplit := isHRepIn_splitList (hrep hP₂) ls Q₂ hQ₂p
        refine isHRepIn_mono ?_ hsplit
        rintro m (hm | ⟨ℓ, hℓ, rfl | rfl⟩)
        · exact hm
        · exact .inl (Finset.mem_coe.2 (Finset.mem_toList.1 hℓ))
        · exact .inr ⟨ℓ, Finset.mem_coe.2 (Finset.mem_toList.1 hℓ), rfl⟩
      have hsplitM : ∀ m ∈ M, (∀ x ∈ Q₁, m x ≤ 0) ∨ (∀ x ∈ Q₁, 0 ≤ m x) := by
        rintro m (hm | ⟨ℓ, hℓ, rfl⟩)
        · exact PolytopalComplex.splitList_signs _ ls
            (Finset.mem_toList.2 (Finset.mem_coe.1 hm)) hQ₁p
        · rcases PolytopalComplex.splitList_signs _ ls
              (Finset.mem_toList.2 (Finset.mem_coe.1 hℓ)) hQ₁p with hle | hge
          · right; intro x hx; simpa [AffineMap.coe_neg] using hle x hx
          · left; intro x hx; simpa [AffineMap.coe_neg] using hge x hx
      exact inter_face_of_split_hRep ((pieces P₁).isPolytope_of_mem hQ₁P) hQ₂M hsplitM }

theorem PolytopalComplex.space_ofFinitePolytopes {ℱ : Set (Set E)} (hℱ : ℱ.Finite)
    (hpoly : ∀ P ∈ ℱ, IsPolytope P) :
    (PolytopalComplex.ofFinitePolytopes hℱ hpoly).space = ⋃ P ∈ ℱ, P := by
  classical
  ext x
  simp only [PolytopalComplex.space, PolytopalComplex.ofFinitePolytopes, Set.mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨Q, ⟨P, hP, hQ⟩, hx⟩
    have hQp : Q ∈ ((PolytopalComplex.ofPolytope (hpoly P hP)).splitList
        (allHyperplanes hℱ).toList).cells := by
      simpa only [dite_eq_left hP] using hQ
    obtain ⟨F, hFP, hQF⟩ := PolytopalComplex.splitList_subset _ _ hQp
    exact ⟨P, hP, hFP.1.subset (hQF hx)⟩
  · rintro ⟨P, hP, hx⟩
    have hsp : x ∈ ((PolytopalComplex.ofPolytope (hpoly P hP)).splitList
        (allHyperplanes hℱ).toList).space := by
      rw [PolytopalComplex.space_splitList, PolytopalComplex.space_ofPolytope]
      exact hx
    rw [PolytopalComplex.mem_space_iff] at hsp
    rcases hsp with ⟨Q, hQ, hxQ⟩
    refine ⟨Q, ⟨P, hP, ?_⟩, hxQ⟩
    simpa only [dite_eq_left hP] using hQ

theorem PolytopalComplex.ofFinitePolytopes_cell_subset {ℱ : Set (Set E)} (hℱ : ℱ.Finite)
    (hpoly : ∀ P ∈ ℱ, IsPolytope P) {Q : Set E}
    (hQ : Q ∈ (PolytopalComplex.ofFinitePolytopes hℱ hpoly).cells) :
    ∃ P ∈ ℱ, Q ⊆ P := by
  classical
  change Q ∈ ⋃ P ∈ ℱ, _ at hQ
  rw [Set.mem_iUnion₂] at hQ
  rcases hQ with ⟨P, hP, hQP⟩
  have hQp : Q ∈ ((PolytopalComplex.ofPolytope (hpoly P hP)).splitList
      (allHyperplanes hℱ).toList).cells := by
    simpa only [dite_eq_left hP] using hQP
  obtain ⟨F, hFP, hQF⟩ := PolytopalComplex.splitList_subset _ _ hQp
  exact ⟨P, hP, hQF.trans hFP.1.subset⟩

theorem PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid {ℱ : Set (Set E)}
    (hℱ : ℱ.Finite) (hpoly : ∀ P ∈ ℱ, IsPolytope P) {Q P : Set E}
    (hQ : Q ∈ (PolytopalComplex.ofFinitePolytopes hℱ hpoly).cells) (hP : P ∈ ℱ) :
    IsPolytopeFace Q (Q ∩ P) ∧ (vertexCentroid Q ∈ P → Q ⊆ P) := by
  classical
  change Q ∈ ⋃ R ∈ ℱ, _ at hQ
  rw [Set.mem_iUnion₂] at hQ
  rcases hQ with ⟨R, hR, hQR⟩
  let hHP : IsHPolytope P := isPolytope_iff_isHPolytope.1 (hpoly P hP)
  let LP : Set (E →ᵃ[ℝ] ℝ) := hHP.2.choose
  have hLPfin : LP.Finite := hHP.2.choose_spec.1
  have hPeq : P = {x | ∀ ℓ ∈ LP, ℓ x ≤ 0} := hHP.2.choose_spec.2
  have hQp : Q ∈ ((PolytopalComplex.ofPolytope (hpoly R hR)).splitList
      (allHyperplanes hℱ).toList).cells := by
    simpa only [dite_eq_left hR] using hQR
  have hsplit : ∀ ℓ ∈ LP, (∀ x ∈ Q, ℓ x ≤ 0) ∨ (∀ x ∈ Q, 0 ≤ ℓ x) := by
    intro ℓ hℓ
    apply PolytopalComplex.splitList_signs _ _ _ hQp
    exact Finset.mem_toList.2 (mem_allHyperplanes_of_hPoly hℱ hP hHP hℓ)
  have hQpoly := (PolytopalComplex.ofFinitePolytopes hℱ hpoly).isPolytope_of_mem
    (Set.mem_biUnion hR hQR)
  have hQne := (PolytopalComplex.ofFinitePolytopes hℱ hpoly).nonempty_of_mem
    (Set.mem_biUnion hR hQR)
  exact ⟨inter_face_of_split_hRep hQpoly ⟨LP, Subset.refl _, hLPfin, hPeq⟩ hsplit,
    split_subset_of_vertexCentroid_mem hQpoly hQne hPeq hsplit⟩

end HyperplaneSplit

section Barycentric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonempty finite chain of cells of `C` totally ordered by inclusion. -/
private def IsCellChain (C : PolytopalComplex E) (𝒞 : Finset (Set E)) : Prop :=
  (𝒞 : Set (Set E)) ⊆ C.cells ∧ 𝒞.Nonempty ∧
    (𝒞 : Set (Set E)).Pairwise (fun A B => A ⊆ B ∨ B ⊆ A)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma finset_chain_exists_top {𝒞 : Finset (Set E)} (hne : 𝒞.Nonempty)
    (hpair : (𝒞 : Set (Set E)).Pairwise (fun A B => A ⊆ B ∨ B ⊆ A)) :
    ∃ P ∈ 𝒞, ∀ Q ∈ 𝒞, Q ⊆ P := by
  induction 𝒞 using Finset.induction with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | @insert A 𝒞' hA ih =>
    rcases 𝒞'.eq_empty_or_nonempty with rfl | h𝒞'ne
    · refine ⟨A, Finset.mem_insert_self A ∅, fun Q hQ => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hQ
      rw [hQ]
    · have hpair' : (𝒞' : Set (Set E)).Pairwise (fun X Y => X ⊆ Y ∨ Y ⊆ X) :=
        hpair.mono (Finset.coe_subset.2 (Finset.subset_insert A 𝒞'))
      obtain ⟨P, hP, hmax⟩ := ih h𝒞'ne hpair'
      have hneAP : A ≠ P := fun h => hA (h ▸ hP)
      rcases hpair (Finset.mem_coe.2 (Finset.mem_insert_self A 𝒞'))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hP)) hneAP with hAP | hPA
      · refine ⟨P, Finset.mem_insert_of_mem hP, fun Q hQ => ?_⟩
        rcases Finset.mem_insert.1 hQ with rfl | hQ'
        · exact hAP
        · exact hmax Q hQ'
      · refine ⟨A, Finset.mem_insert_self A 𝒞', fun Q hQ => ?_⟩
        rcases Finset.mem_insert.1 hQ with rfl | hQ'
        · exact Subset.refl _
        · exact (hmax Q hQ').trans hPA

omit [FiniteDimensional ℝ E] in
private lemma isCellChain_exists_top {C : PolytopalComplex E} {𝒞 : Finset (Set E)}
    (h𝒞 : IsCellChain C 𝒞) : ∃ P ∈ 𝒞, ∀ Q ∈ 𝒞, Q ⊆ P :=
  finset_chain_exists_top h𝒞.2.1 h𝒞.2.2

private lemma vertexCentroid_injOn_cells (C : PolytopalComplex E) :
    InjOn vertexCentroid C.cells := by
  intro P hP Q hQ heq
  have hbP : vertexCentroid P ∈ P :=
    vertexCentroid_mem (C.isPolytope_of_mem hP) (C.nonempty_of_mem hP)
  have hbQ : vertexCentroid Q ∈ Q :=
    vertexCentroid_mem (C.isPolytope_of_mem hQ) (C.nonempty_of_mem hQ)
  have hbPQ : vertexCentroid P ∈ P ∩ Q := ⟨hbP, heq ▸ hbQ⟩
  have hFP : IsPolytopeFace P (P ∩ Q) := C.inter_face hP hQ
  have hFQ : IsPolytopeFace Q (P ∩ Q) := by
    rw [inter_comm]
    exact C.inter_face hQ hP
  have hPQ : P ⊆ Q := by
    by_contra hnot
    have hss : P ∩ Q ⊂ P := ⟨inter_subset_left, fun hsub => hnot (hsub.trans inter_subset_right)⟩
    exact vertexCentroid_notMem_of_ssubset (C.isPolytope_of_mem hP) hFP hss hbPQ
  have hQP : Q ⊆ P := by
    by_contra hnot
    have hss : P ∩ Q ⊂ Q := ⟨inter_subset_right, fun hsub => hnot (hsub.trans inter_subset_left)⟩
    exact vertexCentroid_notMem_of_ssubset (C.isPolytope_of_mem hQ) hFQ hss (heq ▸ hbPQ)
  exact Subset.antisymm hPQ hQP

omit [FiniteDimensional ℝ E] in
private lemma isCellChain_erase {C : PolytopalComplex E} {𝒞 : Finset (Set E)}
    (h𝒞 : IsCellChain C 𝒞) {P : Set E} (hne : (𝒞.erase P).Nonempty) :
    IsCellChain C (𝒞.erase P) :=
  ⟨(Finset.coe_subset.2 (Finset.erase_subset P 𝒞)).trans h𝒞.1, hne,
    h𝒞.2.2.mono (Finset.coe_subset.2 (Finset.erase_subset P 𝒞))⟩

open Classical in
private lemma affineIndependent_vertexCentroid_of_isCellChain (C : PolytopalComplex E) :
    ∀ n : ℕ, ∀ 𝒞 : Finset (Set E), 𝒞.card = n → IsCellChain C 𝒞 →
      AffineIndependent ℝ ((↑) : 𝒞.image vertexCentroid → E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro 𝒞 hn h𝒞
    obtain ⟨P, hP𝒞, hmax⟩ := isCellChain_exists_top h𝒞
    set 𝒞' := 𝒞.erase P
    rcases 𝒞'.eq_empty_or_nonempty with hmt | h𝒞'ne
    · have hsingle : 𝒞 = {P} := by
        ext Q
        constructor
        · intro hQ
          simp only [Finset.mem_singleton]
          by_contra hne
          have hmem : Q ∈ 𝒞' := Finset.mem_erase.2 ⟨hne, hQ⟩
          rw [hmt] at hmem
          exact Finset.notMem_empty _ hmem
        · intro hQ
          simp only [Finset.mem_singleton] at hQ
          exact hQ ▸ hP𝒞
      have himg : 𝒞.image vertexCentroid = {vertexCentroid P} := by simp [hsingle]
      rw [himg]
      exact affineIndependent_of_subsingleton ℝ _
    · have hcard : 𝒞'.card < n := by
        rw [← hn]
        exact Finset.card_erase_lt_of_mem hP𝒞
      have h𝒞' : IsCellChain C 𝒞' := isCellChain_erase h𝒞 h𝒞'ne
      have hindep' : AffineIndependent ℝ ((↑) : 𝒞'.image vertexCentroid → E) :=
        ih 𝒞'.card hcard 𝒞' rfl h𝒞'
      obtain ⟨Q₀, hQ₀𝒞', hmax'⟩ := isCellChain_exists_top h𝒞'
      have hQ₀𝒞 : Q₀ ∈ 𝒞 := Finset.erase_subset P 𝒞 hQ₀𝒞'
      have hnePQ₀ : Q₀ ≠ P := (Finset.mem_erase.1 hQ₀𝒞').1
      have hss : Q₀ ⊂ P := ⟨hmax Q₀ hQ₀𝒞, fun hsub => hnePQ₀ (Subset.antisymm (hmax Q₀ hQ₀𝒞) hsub)⟩
      have hPC := h𝒞.1 hP𝒞
      have hQ₀C := h𝒞.1 hQ₀𝒞
      have hface : IsPolytopeFace P Q₀ := by
        have := C.inter_face hPC hQ₀C
        rwa [inter_eq_right.2 (hmax Q₀ hQ₀𝒞)] at this
      have hsubQ₀ : (𝒞'.image vertexCentroid : Set E) ⊆ Q₀ := by
        intro v hv
        rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨Q, hQ, rfl⟩
        have hQC : Q ∈ C.cells := h𝒞'.1 hQ
        exact hmax' Q hQ (vertexCentroid_mem (C.isPolytope_of_mem hQC) (C.nonempty_of_mem hQC))
      have hbnotQ₀ : vertexCentroid P ∉ affineSpan ℝ Q₀ :=
        vertexCentroid_notMem_affineSpan_of_ssubset (C.isPolytope_of_mem hPC) hface
          (C.nonempty_of_mem hQ₀C) hss
      have hbnot : vertexCentroid P ∉ affineSpan ℝ (𝒞'.image vertexCentroid : Set E) := fun hmem =>
        hbnotQ₀ (affineSpan_mono ℝ hsubQ₀ hmem)
      have himg_eq :
          𝒞.image vertexCentroid = insert (vertexCentroid P) (𝒞'.image vertexCentroid) := by
        rw [← Finset.image_insert, Finset.insert_erase hP𝒞]
      have hins := AffineIndepOn.id_insert (s := (𝒞'.image vertexCentroid : Set E)) hindep' hbnot
      rw [← Finset.coe_insert, ← himg_eq] at hins
      exact hins

private lemma sum_vertexCentroid_mem_top {C : PolytopalComplex E} {A : Finset (Set E)}
    (hA : IsCellChain C A) {P : Set E} (hPC : P ∈ C.cells) (hmax : ∀ Q ∈ A, Q ⊆ P)
    {w : Set E → ℝ} (hw0 : ∀ Q ∈ A, 0 ≤ w Q) (hw1 : ∑ Q ∈ A, w Q = 1) :
    (∑ Q ∈ A, w Q • vertexCentroid Q) ∈ P := by
  classical
  have hhull :
      (∑ Q ∈ A, w Q • vertexCentroid Q) ∈ convexHull ℝ (A.image vertexCentroid : Set E) := by
    let u : E → ℝ := fun v =>
      Finset.sum (A.filter (fun Q => vertexCentroid Q = v)) w
    have hu0 : ∀ v ∈ A.image vertexCentroid, 0 ≤ u v := fun v _ =>
      Finset.sum_nonneg fun Q hQ => hw0 Q (Finset.filter_subset _ _ hQ)
    have hsum_part : ∑ v ∈ A.image vertexCentroid, ∑ Q ∈ A with vertexCentroid Q = v, w Q =
        ∑ Q ∈ A, w Q :=
      Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image vertexCentroid)
        (fun Q hQ => Finset.mem_image_of_mem vertexCentroid hQ) w
    have hu1 : ∑ v ∈ A.image vertexCentroid, u v = 1 := hsum_part.trans hw1
    rw [Finset.convexHull_eq]
    refine ⟨u, hu0, hu1, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id hu1]
    simp only [id_eq, u, Finset.sum_smul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image vertexCentroid)
      (fun Q hQ => Finset.mem_image_of_mem vertexCentroid hQ) (fun Q => w Q • vertexCentroid Q)]
    refine Finset.sum_congr rfl fun v _ => ?_
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [(Finset.mem_filter.1 hQ).2]
  have hsub : (A.image vertexCentroid : Set E) ⊆ P := by
    intro v hv
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨Q, hQ, rfl⟩
    have hQC := hA.1 hQ
    exact hmax Q hQ (vertexCentroid_mem (C.isPolytope_of_mem hQC) (C.nonempty_of_mem hQC))
  exact convexHull_min hsub (C.isPolytope_of_mem hPC).convex hhull

private lemma top_subset_of_face_mem_sum {C : PolytopalComplex E} {A : Finset (Set E)}
    (hA : IsCellChain C A) {P : Set E} (hP : P ∈ A) (hmax : ∀ Q ∈ A, Q ⊆ P)
    {w : Set E → ℝ} (hwpos : ∀ Q ∈ A, 0 < w Q) (hw1 : ∑ Q ∈ A, w Q = 1)
    {F : Set E} (hPF : IsPolytopeFace P F) (hxF : (∑ Q ∈ A, w Q • vertexCentroid Q) ∈ F) :
    P ⊆ F := by
  classical
  have hPC := hA.1 hP
  have hbF : vertexCentroid P ∈ F := by
    set A' := A.erase P
    rcases A'.eq_empty_or_nonempty with hmt | hA'ne
    · have hsingle : A = {P} := by
        ext Q
        constructor
        · intro hQ
          simp only [Finset.mem_singleton]
          by_contra hne
          have hmem : Q ∈ A' := Finset.mem_erase.2 ⟨hne, hQ⟩
          rw [hmt] at hmem
          exact Finset.notMem_empty _ hmem
        · intro hQ
          simp only [Finset.mem_singleton] at hQ
          exact hQ ▸ hP
      subst hsingle
      simp only [Finset.sum_singleton] at hw1 hxF
      rwa [hw1, one_smul] at hxF
    · have hcpos : 0 < w P := hwpos P hP
      have hrem_pos : 0 < ∑ Q ∈ A', w Q :=
        Finset.sum_pos (fun Q hQ => hwpos Q (Finset.erase_subset P A hQ)) hA'ne
      have hsum_split : w P + ∑ Q ∈ A', w Q = 1 := by
        rw [← Finset.add_sum_erase A w hP] at hw1
        exact hw1
      have hrem_eq : ∑ Q ∈ A', w Q = 1 - w P := by linarith
      have h1w_pos : 0 < 1 - w P := hrem_eq ▸ hrem_pos
      have hc_le : w P ≤ 1 := by linarith
      let y : E := ∑ Q ∈ A', (w Q / (1 - w P)) • vertexCentroid Q
      have hy_sum : ∑ Q ∈ A', w Q / (1 - w P) = 1 := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, hrem_eq]
        exact mul_inv_cancel₀ h1w_pos.ne'
      have hyP : y ∈ P :=
        sum_vertexCentroid_mem_top (isCellChain_erase hA hA'ne)
          hPC (fun Q hQ => hmax Q (Finset.erase_subset P A hQ))
          (fun Q hQ => div_nonneg (hwpos Q (Finset.erase_subset P A hQ)).le h1w_pos.le)
          hy_sum
      have hsplit : w P • vertexCentroid P + (1 - w P) • y = ∑ Q ∈ A, w Q • vertexCentroid Q := by
        rw [← Finset.add_sum_erase A (fun Q => w Q • vertexCentroid Q) hP]
        simp only [y, Finset.smul_sum, smul_smul]
        congr 1
        refine Finset.sum_congr rfl fun Q _ => ?_
        rw [mul_div_cancel₀ _ h1w_pos.ne']
      have hbP : vertexCentroid P ∈ P :=
        vertexCentroid_mem (C.isPolytope_of_mem hPC) (C.nonempty_of_mem hPC)
      exact hPF.left_mem_of_smul_add_mem hcpos hc_le hbP hyP (hsplit.symm ▸ hxF)
  by_contra hnot
  have hss : F ⊂ P := ⟨hPF.subset, hnot⟩
  exact vertexCentroid_notMem_of_ssubset (C.isPolytope_of_mem hPC) hPF hss hbF

private lemma top_weight_not_lt {C : PolytopalComplex E} {A₁ A₂ : Finset (Set E)}
    (hA₁ : IsCellChain C A₁) (hA₂ : IsCellChain C A₂) {P : Set E}
    (hP₁ : P ∈ A₁) (hmax₁ : ∀ Q ∈ A₁, Q ⊆ P)
    (hP₂ : P ∈ A₂) (hmax₂ : ∀ Q ∈ A₂, Q ⊆ P)
    {w₁ w₂ : Set E → ℝ} (hw₁ : ∀ Q ∈ A₁, 0 < w₁ Q) (hsum₁ : ∑ Q ∈ A₁, w₁ Q = 1)
    (hw₂ : ∀ Q ∈ A₂, 0 < w₂ Q) (hsum₂ : ∑ Q ∈ A₂, w₂ Q = 1)
    (heq : ∑ Q ∈ A₁, w₁ Q • vertexCentroid Q = ∑ Q ∈ A₂, w₂ Q • vertexCentroid Q) :
    ¬(w₁ P < w₂ P) := by
  classical
  intro hlt
  have hw₂_le : w₂ P ≤ 1 := by
    rw [← hsum₂]
    exact Finset.single_le_sum (fun Q hQ => (hw₂ Q hQ).le) hP₂
  have h1c_pos : 0 < 1 - w₁ P := by linarith
  set A₁' := A₁.erase P
  have hrem₁ : w₁ P + ∑ Q ∈ A₁', w₁ Q = 1 := by
    rw [← Finset.add_sum_erase A₁ w₁ hP₁] at hsum₁
    exact hsum₁
  have hrem₁_eq : ∑ Q ∈ A₁', w₁ Q = 1 - w₁ P := by linarith
  have hA₁'ne : A₁'.Nonempty := by
    by_contra hmt
    rw [Finset.not_nonempty_iff_eq_empty] at hmt
    rw [hmt, Finset.sum_empty] at hrem₁_eq
    linarith
  obtain ⟨P', hP'A₁', hmaxP'⟩ := isCellChain_exists_top (isCellChain_erase hA₁ hA₁'ne)
  have hPC := hA₁.1 hP₁
  have hP'C := (isCellChain_erase hA₁ hA₁'ne).1 hP'A₁'
  have hneP'P : P' ≠ P := (Finset.mem_erase.1 hP'A₁').1
  have hP'sub : P' ⊆ P := hmax₁ P' (Finset.erase_subset P A₁ hP'A₁')
  have hss : P' ⊂ P := ⟨hP'sub, fun hsub => hneP'P (Subset.antisymm hP'sub hsub)⟩
  have hface : IsPolytopeFace P P' := by
    have := C.inter_face hPC hP'C
    rwa [inter_eq_right.2 hP'sub] at this
  let z : E := ∑ Q ∈ A₁', (w₁ Q / (1 - w₁ P)) • vertexCentroid Q
  have hz_sum : ∑ Q ∈ A₁', w₁ Q / (1 - w₁ P) = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hrem₁_eq, mul_inv_cancel₀ h1c_pos.ne']
  have hzP' : z ∈ P' := sum_vertexCentroid_mem_top (isCellChain_erase hA₁ hA₁'ne) hP'C hmaxP'
    (fun Q hQ => div_nonneg (hw₁ Q (Finset.erase_subset P A₁ hQ)).le h1c_pos.le) hz_sum
  have hdiff_eq : ∑ Q ∈ A₁', w₁ Q • vertexCentroid Q =
      (w₂ P - w₁ P) • vertexCentroid P + ∑ Q ∈ A₂.erase P, w₂ Q • vertexCentroid Q := by
    rw [← Finset.add_sum_erase A₁ (fun Q => w₁ Q • vertexCentroid Q) hP₁,
      ← Finset.add_sum_erase A₂ (fun Q => w₂ Q • vertexCentroid Q) hP₂] at heq
    have hsub : ∑ Q ∈ A₁', w₁ Q • vertexCentroid Q =
        w₂ P • vertexCentroid P - w₁ P • vertexCentroid P +
          ∑ Q ∈ A₂.erase P, w₂ Q • vertexCentroid Q := by
      have := eq_sub_of_add_eq' heq
      rw [this]
      abel
    rw [hsub, sub_smul]
  have hz_eq : z = ((w₂ P - w₁ P) / (1 - w₁ P)) • vertexCentroid P +
      ∑ Q ∈ A₂.erase P, (w₂ Q / (1 - w₁ P)) • vertexCentroid Q := by
    have hsmul : (1 - w₁ P) • z = ∑ Q ∈ A₁', w₁ Q • vertexCentroid Q := by
      simp only [z, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun Q _ => by rw [mul_div_cancel₀ _ h1c_pos.ne']
    have hinveq : z = (1 - w₁ P)⁻¹ • ((1 - w₁ P) • z) := by
      rw [smul_smul, inv_mul_cancel₀ h1c_pos.ne', one_smul]
    rw [hinveq, hsmul, hdiff_eq, smul_add, smul_smul, Finset.smul_sum]
    congr 1
    · rw [div_eq_inv_mul]
    · refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, div_eq_inv_mul]
  let c : ℝ := (w₂ P - w₁ P) / (1 - w₁ P)
  have hcpos : 0 < c := div_pos (sub_pos.2 hlt) h1c_pos
  have hc_le : c ≤ 1 := (div_le_one h1c_pos).2 (by linarith)
  set A₂' := A₂.erase P
  have hrem₂ : w₂ P + ∑ Q ∈ A₂', w₂ Q = 1 := by
    rw [← Finset.add_sum_erase A₂ w₂ hP₂] at hsum₂
    exact hsum₂
  rcases A₂'.eq_empty_or_nonempty with hmt₂ | hA₂'ne
  · rw [hmt₂, Finset.sum_empty] at hz_eq hrem₂
    have hw₂1 : w₂ P = 1 := by linarith
    have hc1 : (w₂ P - w₁ P) / (1 - w₁ P) = 1 := by
      rw [hw₂1, div_self h1c_pos.ne']
    rw [hc1, one_smul, add_zero] at hz_eq
    exact vertexCentroid_notMem_of_ssubset (C.isPolytope_of_mem hPC) hface hss (hz_eq ▸ hzP')
  · have hrem₂_pos : 0 < ∑ Q ∈ A₂', w₂ Q :=
      Finset.sum_pos (fun Q hQ => hw₂ Q (Finset.erase_subset P A₂ hQ)) hA₂'ne
    have hrem₂_eq : ∑ Q ∈ A₂', w₂ Q = 1 - w₂ P := by linarith
    have h1w2_pos : 0 < 1 - w₂ P := hrem₂_eq ▸ hrem₂_pos
    have h1c2 : 1 - c = (1 - w₂ P) / (1 - w₁ P) := by
      dsimp only [c]; field_simp; ring
    let y : E := ∑ Q ∈ A₂', (w₂ Q / (1 - w₂ P)) • vertexCentroid Q
    have hy_sum : ∑ Q ∈ A₂', w₂ Q / (1 - w₂ P) = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, hrem₂_eq]
      exact mul_inv_cancel₀ h1w2_pos.ne'
    have hyP : y ∈ P := sum_vertexCentroid_mem_top (isCellChain_erase hA₂ hA₂'ne) hPC
      (fun Q hQ => hmax₂ Q (Finset.erase_subset P A₂ hQ))
      (fun Q hQ => div_nonneg (hw₂ Q (Finset.erase_subset P A₂ hQ)).le h1w2_pos.le) hy_sum
    have hy_eq : (1 - c) • y = ∑ Q ∈ A₂', (w₂ Q / (1 - w₁ P)) • vertexCentroid Q := by
      simp only [y, h1c2, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun Q _ => ?_
      have hne1 : 1 - w₁ P ≠ 0 := h1c_pos.ne'
      have hne2 : 1 - w₂ P ≠ 0 := h1w2_pos.ne'
      congr 1
      field_simp
    have hcomb : c • vertexCentroid P + (1 - c) • y = z := by
      rw [hy_eq, ← hz_eq]
    have hbP : vertexCentroid P ∈ P :=
      vertexCentroid_mem (C.isPolytope_of_mem hPC) (C.nonempty_of_mem hPC)
    have hbin : vertexCentroid P ∈ P' :=
      hface.left_mem_of_smul_add_mem hcpos hc_le hbP hyP (hcomb.symm ▸ hzP')
    exact vertexCentroid_notMem_of_ssubset (C.isPolytope_of_mem hPC) hface hss hbin

open Classical in
private lemma mem_convexHull_inter_of_chains (C : PolytopalComplex E) :
    ∀ n : ℕ, ∀ {A₁ A₂ : Finset (Set E)} {w₁ w₂ : Set E → ℝ},
      A₁.card + A₂.card = n →
      IsCellChain C A₁ → IsCellChain C A₂ →
      (∀ P ∈ A₁, 0 < w₁ P) → ∑ P ∈ A₁, w₁ P = 1 →
      (∀ Q ∈ A₂, 0 < w₂ Q) → ∑ Q ∈ A₂, w₂ Q = 1 →
      ∑ P ∈ A₁, w₁ P • vertexCentroid P = ∑ Q ∈ A₂, w₂ Q • vertexCentroid Q →
      ∑ P ∈ A₁, w₁ P • vertexCentroid P ∈
        convexHull ℝ (((A₁ ∩ A₂).image vertexCentroid : Finset E) : Set E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro A₁ A₂ w₁ w₂ hn hA₁ hA₂ hw₁ hsum₁ hw₂ hsum₂ heq
    classical
    obtain ⟨P₁, hP₁A₁, hmax₁⟩ := isCellChain_exists_top hA₁
    obtain ⟨Q₂, hQ₂A₂, hmax₂⟩ := isCellChain_exists_top hA₂
    let x := ∑ P ∈ A₁, w₁ P • vertexCentroid P
    have hP₁C := hA₁.1 hP₁A₁
    have hQ₂C := hA₂.1 hQ₂A₂
    have hxP₁ : x ∈ P₁ := sum_vertexCentroid_mem_top hA₁ hP₁C hmax₁
      (fun P hP => (hw₁ P hP).le) hsum₁
    have hxQ₂ : x ∈ Q₂ := by
      dsimp only [x]
      rw [heq]
      exact sum_vertexCentroid_mem_top hA₂ hQ₂C hmax₂ (fun Q hQ => (hw₂ Q hQ).le) hsum₂
    have hFP₁ : IsPolytopeFace P₁ (P₁ ∩ Q₂) := C.inter_face hP₁C hQ₂C
    have hFQ₂ : IsPolytopeFace Q₂ (P₁ ∩ Q₂) := by
      rw [Set.inter_comm]; exact C.inter_face hQ₂C hP₁C
    have hP₁sub : P₁ ⊆ P₁ ∩ Q₂ :=
      top_subset_of_face_mem_sum hA₁ hP₁A₁ hmax₁ hw₁ hsum₁ hFP₁ ⟨hxP₁, hxQ₂⟩
    have hQ₂sub : Q₂ ⊆ P₁ ∩ Q₂ :=
      top_subset_of_face_mem_sum hA₂ hQ₂A₂ hmax₂ hw₂ hsum₂ hFQ₂ (heq ▸ ⟨hxP₁, hxQ₂⟩)
    have hP₁Q₂ : P₁ = Q₂ :=
      Subset.antisymm (hP₁sub.trans inter_subset_right) (hQ₂sub.trans inter_subset_left)
    subst hP₁Q₂
    have hw_eq : w₁ P₁ = w₂ P₁ := by
      refine le_antisymm ?_ ?_
      · by_contra! hgt
        exact top_weight_not_lt hA₂ hA₁ hQ₂A₂ hmax₂ hP₁A₁ hmax₁
          hw₂ hsum₂ hw₁ hsum₁ heq.symm hgt
      · by_contra! hlt
        exact top_weight_not_lt hA₁ hA₂ hP₁A₁ hmax₁ hQ₂A₂ hmax₂
          hw₁ hsum₁ hw₂ hsum₂ heq hlt
    have hP₁_inter : vertexCentroid P₁ ∈ (((A₁ ∩ A₂).image vertexCentroid : Finset E) : Set E) :=
      Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_inter.2 ⟨hP₁A₁, hQ₂A₂⟩))
    by_cases h1 : w₁ P₁ = 1
    · have hsingle : A₁ = {P₁} := by
        ext R
        constructor
        · intro hR
          simp only [Finset.mem_singleton]
          by_contra hne
          have hsub : w₁ P₁ + w₁ R ≤ ∑ Q ∈ A₁, w₁ Q := by
            have : {P₁, R} ⊆ A₁ := by intro z hz; simp only [Finset.mem_insert,
              Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
            rw [← Finset.sum_pair (fun h => hne h.symm)]
            exact Finset.sum_le_sum_of_subset_of_nonneg this
              (fun z hz _ => (hw₁ z hz).le)
          linarith [hw₁ R hR]
        · intro hR; simp only [Finset.mem_singleton] at hR; exact hR ▸ hP₁A₁
      have hx_eq : x = vertexCentroid P₁ := by
        simp [x, hsingle, h1]
      change x ∈ _
      rw [hx_eq]
      exact subset_convexHull ℝ _ hP₁_inter
    · have hw1_le : w₁ P₁ ≤ 1 := by
        rw [← hsum₁]
        exact Finset.single_le_sum (fun Q hQ => (hw₁ Q hQ).le) hP₁A₁
      have hw1_lt : w₁ P₁ < 1 := lt_of_le_of_ne hw1_le h1
      have h1t_pos : 0 < 1 - w₁ P₁ := sub_pos.2 hw1_lt
      set A₁' := A₁.erase P₁
      set A₂' := A₂.erase P₁
      have hsum₁' : ∑ Q ∈ A₁', w₁ Q = 1 - w₁ P₁ := by
        rw [← Finset.add_sum_erase A₁ w₁ hP₁A₁] at hsum₁; linarith
      have hsum₂' : ∑ Q ∈ A₂', w₂ Q = 1 - w₁ P₁ := by
        rw [← Finset.add_sum_erase A₂ w₂ hQ₂A₂, ← hw_eq] at hsum₂; linarith
      have hA₁'ne : A₁'.Nonempty := by
        by_contra hmt; rw [Finset.not_nonempty_iff_eq_empty] at hmt
        rw [hmt, Finset.sum_empty] at hsum₁'; linarith
      have hA₂'ne : A₂'.Nonempty := by
        by_contra hmt; rw [Finset.not_nonempty_iff_eq_empty] at hmt
        rw [hmt, Finset.sum_empty] at hsum₂'; linarith
      have hcard' : A₁'.card + A₂'.card < n := by
        rw [← hn]
        have hc₁ := Finset.card_erase_lt_of_mem hP₁A₁
        have hc₂ := Finset.card_erase_lt_of_mem hQ₂A₂
        dsimp only [A₁', A₂']
        omega
      let w₁' : Set E → ℝ := fun Q => w₁ Q / (1 - w₁ P₁)
      let w₂' : Set E → ℝ := fun Q => w₂ Q / (1 - w₁ P₁)
      have heq_rem : ∑ Q ∈ A₁', w₁ Q • vertexCentroid Q = ∑ Q ∈ A₂', w₂ Q • vertexCentroid Q := by
        rw [← Finset.add_sum_erase A₁ (fun Q => w₁ Q • vertexCentroid Q) hP₁A₁,
          ← Finset.add_sum_erase A₂ (fun Q => w₂ Q • vertexCentroid Q) hQ₂A₂, ← hw_eq] at heq
        exact add_left_cancel heq
      have heq' : ∑ Q ∈ A₁', w₁' Q • vertexCentroid Q = ∑ Q ∈ A₂', w₂' Q • vertexCentroid Q := by
        simp only [w₁', w₂', div_eq_inv_mul, ← smul_smul, ← Finset.smul_sum, heq_rem]
      have hy := ih (A₁'.card + A₂'.card) hcard' rfl
        (isCellChain_erase hA₁ hA₁'ne) (isCellChain_erase hA₂ hA₂'ne)
        (fun Q hQ => div_pos (hw₁ Q (Finset.erase_subset P₁ A₁ hQ)) h1t_pos)
        (by simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum₁']; exact mul_inv_cancel₀ h1t_pos.ne')
        (fun Q hQ => div_pos (hw₂ Q (Finset.erase_subset P₁ A₂ hQ)) h1t_pos)
        (by simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum₂']; exact mul_inv_cancel₀ h1t_pos.ne')
        heq'
      have hy' : (∑ Q ∈ A₁', w₁' Q • vertexCentroid Q) ∈
          convexHull ℝ (((A₁ ∩ A₂).image vertexCentroid : Finset E) : Set E) := by
        refine convexHull_mono (Finset.coe_subset.2 (Finset.image_subset_image ?_)) hy
        exact Finset.inter_subset_inter (Finset.erase_subset P₁ A₁) (Finset.erase_subset P₁ A₂)
      have hx_split : x = w₁ P₁ • vertexCentroid P₁ +
          (1 - w₁ P₁) • ∑ Q ∈ A₁', w₁' Q • vertexCentroid Q := by
        rw [Finset.smul_sum]
        have hcongr : ∑ Q ∈ A₁', (1 - w₁ P₁) • (w₁' Q • vertexCentroid Q) =
            ∑ Q ∈ A₁', w₁ Q • vertexCentroid Q :=
          Finset.sum_congr rfl fun Q _ => by
            simp only [w₁', smul_smul, mul_div_cancel₀ _ h1t_pos.ne']
        rw [hcongr]
        exact (Finset.add_sum_erase A₁ (fun Q => w₁ Q • vertexCentroid Q) hP₁A₁).symm
      change x ∈ _
      rw [hx_split]
      exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ hP₁_inter) hy'
        (hw₁ P₁ hP₁A₁).le h1t_pos.le (by ring)

open Classical in
private lemma convexHull_chain_support_decomp {C : PolytopalComplex E} {𝒞 : Finset (Set E)}
    (h𝒞 : IsCellChain C 𝒞) {x : E}
    (hx : x ∈ convexHull ℝ ((𝒞.image vertexCentroid : Finset E) : Set E)) :
    ∃ A : Finset (Set E), A ⊆ 𝒞 ∧ IsCellChain C A ∧
      ∃ w : Set E → ℝ, (∀ P ∈ A, 0 < w P) ∧ ∑ P ∈ A, w P = 1 ∧
        x = ∑ P ∈ A, w P • vertexCentroid P := by
  rw [Finset.convexHull_eq] at hx
  obtain ⟨u, hu0, hu1, hux⟩ := hx
  rw [Finset.centerMass_eq_of_sum_1 _ id hu1] at hux
  simp only [id_eq] at hux
  let A := 𝒞.filter (fun P => 0 < u (vertexCentroid P))
  have hAsub : A ⊆ 𝒞 := Finset.filter_subset _ _
  have hu_pos : ∀ P ∈ A, 0 < u (vertexCentroid P) := fun P hP => (Finset.mem_filter.1 hP).2
  have hsum_img : ∑ v ∈ 𝒞.image vertexCentroid, u v = ∑ P ∈ 𝒞, u (vertexCentroid P) :=
    (Finset.sum_image (f := u)
      (fun P hP Q hQ => (vertexCentroid_injOn_cells C) (h𝒞.1 hP) (h𝒞.1 hQ)))
  have hcomb_img : ∑ v ∈ 𝒞.image vertexCentroid, u v • v =
      ∑ P ∈ 𝒞, u (vertexCentroid P) • vertexCentroid P :=
    Finset.sum_image (f := fun v => u v • v)
      (fun P hP Q hQ => (vertexCentroid_injOn_cells C) (h𝒞.1 hP) (h𝒞.1 hQ))
  have hsumA : ∑ P ∈ A, u (vertexCentroid P) = 1 := by
    rw [← hu1, hsum_img,
      ← Finset.sum_filter_add_sum_filter_not 𝒞 (fun P => 0 < u (vertexCentroid P))]
    have h0 : ∑ P ∈ 𝒞.filter (fun P => ¬0 < u (vertexCentroid P)), u (vertexCentroid P) = 0 :=
      Finset.sum_eq_zero fun P hP => by
        have hmem := Finset.mem_filter.1 hP
        exact le_antisymm (not_lt.1 hmem.2)
          (hu0 _ (Finset.mem_image_of_mem _ hmem.1))
    rw [h0, add_zero]
  have hAne : A.Nonempty := by
    by_contra hmt
    rw [Finset.not_nonempty_iff_eq_empty] at hmt
    rw [hmt, Finset.sum_empty] at hsumA
    linarith
  have hcombA : x = ∑ P ∈ A, u (vertexCentroid P) • vertexCentroid P := by
    rw [← hux, hcomb_img, ← Finset.sum_filter_add_sum_filter_not 𝒞
      (fun P => 0 < u (vertexCentroid P))]
    have h0 : ∑ P ∈ 𝒞.filter (fun P => ¬0 < u (vertexCentroid P)),
        u (vertexCentroid P) • vertexCentroid P = 0 :=
      Finset.sum_eq_zero fun P hP => by
        have hmem := Finset.mem_filter.1 hP
        have hz : u (vertexCentroid P) = 0 :=
          le_antisymm (not_lt.1 hmem.2) (hu0 _ (Finset.mem_image_of_mem _ hmem.1))
        simp [hz]
    rw [h0, add_zero]
  exact ⟨A, hAsub, ⟨(Finset.coe_subset.2 hAsub).trans h𝒞.1, hAne,
    h𝒞.2.2.mono (Finset.coe_subset.2 hAsub)⟩,
    fun P => u (vertexCentroid P), hu_pos, hsumA, hcombA⟩

open Classical in
/-- The **barycentric subdivision** of a polytopal complex `C`, realized as a mathlib
`Geometry.SimplicialComplex ℝ E`. -/
def PolytopalComplex.barycentricSubdivision (C : PolytopalComplex E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ 𝒞 : Finset (Set E), IsCellChain C 𝒞 ∧ s = 𝒞.image vertexCentroid}
  indep := by
    rintro s ⟨𝒞, h𝒞, rfl⟩
    exact affineIndependent_vertexCentroid_of_isCellChain C 𝒞.card 𝒞 rfl h𝒞
  isRelLowerSet_faces := by
    rintro s ⟨𝒞, h𝒞, rfl⟩
    refine ⟨(h𝒞.2.1.image vertexCentroid), fun t hts ht => ?_⟩
    classical
    let 𝒞' := 𝒞.filter (fun P => vertexCentroid P ∈ t)
    have h𝒞'ne : 𝒞'.Nonempty := by
      obtain ⟨v, hvt⟩ := ht
      rcases Finset.mem_image.1 (hts hvt) with ⟨P, hP𝒞, rfl⟩
      exact ⟨P, Finset.mem_filter.2 ⟨hP𝒞, hvt⟩⟩
    have himg : 𝒞'.image vertexCentroid = t := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, 𝒞']
      constructor
      · rintro ⟨P, ⟨_, hvt⟩, rfl⟩
        exact hvt
      · intro hvt
        rcases Finset.mem_image.1 (hts hvt) with ⟨P, hP𝒞, rfl⟩
        exact ⟨P, ⟨hP𝒞, hvt⟩, rfl⟩
    exact ⟨𝒞', ⟨(Finset.coe_subset.2 (Finset.filter_subset _ _)).trans h𝒞.1, h𝒞'ne,
      h𝒞.2.2.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))⟩, himg.symm⟩
  inter_subset_convexHull := by
    rintro s₁ s₂ ⟨𝒞₁, h𝒞₁, rfl⟩ ⟨𝒞₂, h𝒞₂, rfl⟩ x ⟨hx₁, hx₂⟩
    obtain ⟨A₁, hA₁𝒞, hA₁, w₁, hw₁, hsum₁, hx₁'⟩ :=
      convexHull_chain_support_decomp h𝒞₁ hx₁
    obtain ⟨A₂, hA₂𝒞, hA₂, w₂, hw₂, hsum₂, hx₂'⟩ :=
      convexHull_chain_support_decomp h𝒞₂ hx₂
    have hmem := mem_convexHull_inter_of_chains C (A₁.card + A₂.card) rfl hA₁ hA₂
      hw₁ hsum₁ hw₂ hsum₂ (hx₁'.symm.trans hx₂')
    rw [← hx₁'] at hmem
    rw [← Finset.coe_inter]
    refine convexHull_mono (Finset.coe_subset.2 ?_) hmem
    intro v hv
    rcases Finset.mem_image.1 hv with ⟨P, hP, rfl⟩
    rw [Finset.mem_inter] at hP ⊢
    exact ⟨Finset.mem_image_of_mem _ (hA₁𝒞 hP.1), Finset.mem_image_of_mem _ (hA₂𝒞 hP.2)⟩

theorem PolytopalComplex.barycentricSubdivision_faces_finite (C : PolytopalComplex E) :
    C.barycentricSubdivision.faces.Finite := by
  classical
  let cf := C.finite_cells.toFinset
  refine (Finset.finite_toSet (cf.powerset.image (fun 𝒞 => 𝒞.image vertexCentroid))).subset ?_
  rintro s ⟨𝒞, h𝒞, rfl⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨𝒞, ?_, rfl⟩)
  exact Finset.mem_powerset.2 fun P hP => C.finite_cells.mem_toFinset.2 (h𝒞.1 hP)

theorem PolytopalComplex.barycentricSubdivision_simplex_subset (C : PolytopalComplex E)
    {s : Finset E} (hs : s ∈ C.barycentricSubdivision.faces) :
    ∃ P ∈ C.cells, convexHull ℝ (s : Set E) ⊆ P := by
  classical
  rcases hs with ⟨𝒞, h𝒞, rfl⟩
  obtain ⟨P, hP𝒞, hmax⟩ := isCellChain_exists_top h𝒞
  refine ⟨P, h𝒞.1 hP𝒞, convexHull_min ?_ (C.isPolytope_of_mem (h𝒞.1 hP𝒞)).convex⟩
  intro v hv
  rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨Q, hQ, rfl⟩
  have hQC := h𝒞.1 hQ
  exact hmax Q hQ (vertexCentroid_mem (C.isPolytope_of_mem hQC) (C.nonempty_of_mem hQC))

open Classical in
private lemma mem_barycentricSubdivision_of_cell (C : PolytopalComplex E) :
    ∀ n : ℕ, ∀ P ∈ C.cells,
      (C.finite_cells.toFinset.filter (fun Q => Q ⊆ P)).card = n →
      ∀ x ∈ P, ∃ 𝒞 : Finset (Set E), IsCellChain C 𝒞 ∧ (∀ Q ∈ 𝒞, Q ⊆ P) ∧
        x ∈ convexHull ℝ ((𝒞.image vertexCentroid : Finset E) : Set E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro P hP hcard x hxP
    classical
    by_cases hxb : x = vertexCentroid P
    · subst hxb
      refine ⟨{P}, ⟨by simpa using hP, Finset.singleton_nonempty P, by simp⟩,
        fun Q hQ => by simp only [Finset.mem_singleton] at hQ; rw [hQ], ?_⟩
      apply subset_convexHull ℝ
      simp
    · obtain ⟨F, hPF, hFne, hFss, y, hyF, hseg⟩ :=
        exists_isPolytopeFace_ssubset_of_ne_vertexCentroid (C.isPolytope_of_mem hP) hxP hxb
      have hFC : F ∈ C.cells := C.face_mem hP hPF hFne
      have hlt : (C.finite_cells.toFinset.filter (fun Q => Q ⊆ F)).card < n := by
        rw [← hcard]
        refine Finset.card_lt_card ⟨fun Q hQ => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter] at hQ ⊢
          exact ⟨hQ.1, hQ.2.trans hPF.subset⟩
        · have hP_mem : P ∈ C.finite_cells.toFinset.filter (fun Q => Q ⊆ P) :=
            Finset.mem_filter.2 ⟨C.finite_cells.mem_toFinset.2 hP, Subset.refl P⟩
          have hPF_mem := hsub hP_mem
          rw [Finset.mem_filter] at hPF_mem
          exact hFss.not_subset hPF_mem.2
      obtain ⟨𝒞F, h𝒞F, hsubF, hy_hull⟩ := ih _ hlt F hFC rfl y hyF
      have hP_notin : P ∉ 𝒞F := fun hmem => hFss.not_subset (hsubF P hmem)
      refine ⟨insert P 𝒞F, ⟨?_, Finset.insert_nonempty P 𝒞F, ?_⟩, fun Q hQ => ?_, ?_⟩
      · intro Q hQ
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hQ
        rcases hQ with rfl | hQ'
        · exact hP
        · exact h𝒞F.1 hQ'
      · simp only [Finset.coe_insert]
        refine h𝒞F.2.2.insert fun Q hQ _ =>
          ⟨.inr ((hsubF Q hQ).trans hPF.subset), .inl ((hsubF Q hQ).trans hPF.subset)⟩
      · rcases Finset.mem_insert.1 hQ with rfl | hQ'
        · exact Subset.refl _
        · exact (hsubF Q hQ').trans hPF.subset
      · have hsub_img : (𝒞F.image vertexCentroid : Set E) ⊆
            ((insert P 𝒞F).image vertexCentroid : Set E) :=
          Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert P 𝒞F))
        have hy' : y ∈ convexHull ℝ (((insert P 𝒞F).image vertexCentroid : Finset E) : Set E) :=
          convexHull_mono hsub_img hy_hull
        have hb' : vertexCentroid P ∈
            convexHull ℝ (((insert P 𝒞F).image vertexCentroid : Finset E) : Set E) := by
          apply subset_convexHull ℝ
          exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self P 𝒞F))
        exact (convex_convexHull ℝ _).segment_subset hb' hy' hseg

theorem PolytopalComplex.barycentricSubdivision_space (C : PolytopalComplex E) :
    C.barycentricSubdivision.space = C.space := by
  classical
  ext x
  simp only [Geometry.SimplicialComplex.space, PolytopalComplex.mem_space_iff, Set.mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨P, hP, hsub⟩ := C.barycentricSubdivision_simplex_subset hs
    exact ⟨P, hP, hsub hx⟩
  · rintro ⟨P, hP, hx⟩
    obtain ⟨𝒞, h𝒞, _, hx𝒞⟩ :=
      mem_barycentricSubdivision_of_cell C _ P hP rfl x hx
    exact ⟨𝒞.image vertexCentroid, ⟨𝒞, h𝒞, rfl⟩, hx𝒞⟩

end Barycentric

section Polyhedra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A set `P` in `E` is a compact **polyhedron** if it is the underlying space of a finite
simplicial complex (equivalently, a finite union of simplices or polytopes). -/
@[expose] def IsPolyhedron (P : Set E) : Prop :=
  ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P

theorem isPolyhedron_iff_exists_polytopalComplex {P : Set E} :
    IsPolyhedron P ↔ ∃ C : PolytopalComplex E, C.space = P := by
  constructor
  · rintro ⟨K, hfin, rfl⟩
    exact ⟨PolytopalComplex.ofSimplicialComplex K hfin,
      PolytopalComplex.space_ofSimplicialComplex K hfin⟩
  · rintro ⟨C, rfl⟩
    exact ⟨C.barycentricSubdivision, C.barycentricSubdivision_faces_finite,
      C.barycentricSubdivision_space⟩

theorem isPolyhedron_iff_finite_union_polytopes {P : Set E} :
    IsPolyhedron P ↔ ∃ ℱ : Set (Set E), ℱ.Finite ∧ (∀ Q ∈ ℱ, IsPolytope Q) ∧
      P = ⋃ Q ∈ ℱ, Q := by
  constructor
  · rintro ⟨K, hfin, rfl⟩
    let ℱ : Set (Set E) := (fun s : Finset E => convexHull ℝ (s : Set E)) '' K.faces
    refine ⟨ℱ, hfin.image _, ?_, ?_⟩
    · rintro _ ⟨s, _, rfl⟩
      exact isPolytope_convexHull s.finite_toSet
    · ext x
      simp only [Geometry.SimplicialComplex.space, Set.mem_iUnion, Set.mem_image, exists_prop, ℱ]
      exact ⟨fun ⟨s, hs, hx⟩ => ⟨_, ⟨s, hs, rfl⟩, hx⟩,
        fun ⟨_, ⟨s, hs, rfl⟩, hx⟩ => ⟨s, hs, hx⟩⟩
  · rintro ⟨ℱ, hℱ, hpoly, rfl⟩
    rw [isPolyhedron_iff_exists_polytopalComplex]
    exact ⟨PolytopalComplex.ofFinitePolytopes hℱ hpoly,
      PolytopalComplex.space_ofFinitePolytopes hℱ hpoly⟩

theorem isPolyhedron_iff_finite_union_simplices {P : Set E} :
    IsPolyhedron P ↔ ∃ 𝒮 : Set (Finset E), 𝒮.Finite ∧
      (∀ s ∈ 𝒮, AffineIndependent ℝ ((↑) : s → E)) ∧
      P = ⋃ s ∈ 𝒮, convexHull ℝ (s : Set E) := by
  constructor
  · rintro ⟨K, hfin, rfl⟩
    exact ⟨K.faces, hfin, fun s hs => K.indep hs, rfl⟩
  · rintro ⟨𝒮, h𝒮, hindep, rfl⟩
    rw [isPolyhedron_iff_finite_union_polytopes]
    refine ⟨(fun s : Finset E => convexHull ℝ (s : Set E)) '' 𝒮, h𝒮.image _, ?_, ?_⟩
    · rintro _ ⟨s, _, rfl⟩
      exact isPolytope_convexHull s.finite_toSet
    · ext x
      simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
      exact ⟨fun ⟨s, hs, hx⟩ => ⟨_, ⟨s, hs, rfl⟩, hx⟩,
        fun ⟨_, ⟨s, hs, rfl⟩, hx⟩ => ⟨s, hs, hx⟩⟩

theorem isPolyhedron_empty : IsPolyhedron (∅ : Set E) :=
  isPolyhedron_iff_exists_polytopalComplex.2
    ⟨PolytopalComplex.empty, PolytopalComplex.space_empty⟩

theorem IsPolytope.isPolyhedron {P : Set E} (hP : IsPolytope P) : IsPolyhedron P :=
  isPolyhedron_iff_exists_polytopalComplex.2
    ⟨PolytopalComplex.ofPolytope hP, PolytopalComplex.space_ofPolytope hP⟩

theorem IsPolyhedron.isCompact {P : Set E} (hP : IsPolyhedron P) : IsCompact P := by
  obtain ⟨C, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  exact C.isCompact_space

theorem IsPolyhedron.isClosed {P : Set E} (hP : IsPolyhedron P) : IsClosed P :=
  hP.isCompact.isClosed

theorem IsPolyhedron.isBounded {P : Set E} (hP : IsPolyhedron P) : Bornology.IsBounded P :=
  hP.isCompact.isBounded

theorem IsPolyhedron.union {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ∪ Q) := by
  obtain ⟨C₁, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  obtain ⟨C₂, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  rw [isPolyhedron_iff_finite_union_polytopes]
  refine ⟨C₁.cells ∪ C₂.cells, C₁.finite_cells.union C₂.finite_cells, ?_, ?_⟩
  · rintro R (hR | hR)
    · exact C₁.isPolytope_of_mem hR
    · exact C₂.isPolytope_of_mem hR
  · ext x
    simp only [Set.mem_union, PolytopalComplex.mem_space_iff, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => h.elim (fun ⟨R, hR, hx⟩ => ⟨R, .inl hR, hx⟩)
      (fun ⟨R, hR, hx⟩ => ⟨R, .inr hR, hx⟩),
      fun ⟨R, hR, hx⟩ => hR.elim (fun h1 => .inl ⟨R, h1, hx⟩) (fun h2 => .inr ⟨R, h2, hx⟩)⟩

theorem IsPolyhedron.biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) {P : ι → Set E}
    (hP : ∀ i ∈ s, IsPolyhedron (P i)) : IsPolyhedron (⋃ i ∈ s, P i) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    simpa only [Set.biUnion_empty] using (isPolyhedron_empty : IsPolyhedron (∅ : Set E))
  | @insert a s' _ _ ih =>
    rw [Set.biUnion_insert]
    exact (hP a (Set.mem_insert a s')).union (ih fun i hi => hP i (Set.mem_insert_of_mem a hi))

theorem IsPolyhedron.inter {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ∩ Q) := by
  obtain ⟨C₁, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  obtain ⟨C₂, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  rw [isPolyhedron_iff_finite_union_polytopes]
  let ℱ := (fun p : Set E × Set E => p.1 ∩ p.2) '' (C₁.cells ×ˢ C₂.cells)
  refine ⟨ℱ, (C₁.finite_cells.prod C₂.finite_cells).image _, ?_, ?_⟩
  · rintro _ ⟨⟨R₁, R₂⟩, ⟨hR₁, hR₂⟩, rfl⟩
    exact (C₁.isPolytope_of_mem hR₁).inter (C₂.isPolytope_of_mem hR₂)
  · ext x
    simp only [Set.mem_inter_iff, PolytopalComplex.mem_space_iff, Set.mem_iUnion,
      Set.mem_image, Set.mem_prod, Prod.exists, exists_prop, ℱ]
    constructor
    · rintro ⟨⟨R₁, hR₁, hx1⟩, ⟨R₂, hR₂, hx2⟩⟩
      exact ⟨R₁ ∩ R₂, ⟨R₁, R₂, ⟨hR₁, hR₂⟩, rfl⟩, hx1, hx2⟩
    · rintro ⟨_, ⟨R₁, R₂, ⟨hR₁, hR₂⟩, rfl⟩, hx1, hx2⟩
      exact ⟨⟨R₁, hR₁, hx1⟩, ⟨R₂, hR₂, hx2⟩⟩

theorem IsPolyhedron.prod {P : Set E} {Q : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ×ˢ Q) := by
  obtain ⟨C₁, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  obtain ⟨C₂, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  exact isPolyhedron_iff_exists_polytopalComplex.2 ⟨C₁.prod C₂, C₁.space_prod C₂⟩

theorem IsPolyhedron.image {P : Set E} (hP : IsPolyhedron P) (f : E →ᵃ[ℝ] F) :
    IsPolyhedron (f '' P) := by
  obtain ⟨C, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  rw [isPolyhedron_iff_finite_union_polytopes]
  refine ⟨(fun R => f '' R) '' C.cells, C.finite_cells.image _, ?_, ?_⟩
  · rintro _ ⟨R, hR, rfl⟩
    exact (C.isPolytope_of_mem hR).image f
  · ext y
    simp only [Set.mem_image, PolytopalComplex.mem_space_iff, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨R, hR, hx⟩, rfl⟩
      exact ⟨f '' R, ⟨R, hR, rfl⟩, x, hx, rfl⟩
    · rintro ⟨_, ⟨R, hR, rfl⟩, x, hx, rfl⟩
      exact ⟨x, ⟨R, hR, hx⟩, rfl⟩

theorem IsPolyhedron.preimage_inter {P : Set E} {Q : Set F} (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) (f : E →ᵃ[ℝ] F) : IsPolyhedron (P ∩ f ⁻¹' Q) := by
  obtain ⟨C₁, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  obtain ⟨C₂, rfl⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  rw [isPolyhedron_iff_finite_union_polytopes]
  let ℱ := (fun p : Set E × Set F => p.1 ∩ f ⁻¹' p.2) '' (C₁.cells ×ˢ C₂.cells)
  refine ⟨ℱ, (C₁.finite_cells.prod C₂.finite_cells).image _, ?_, ?_⟩
  · rintro _ ⟨⟨R₁, R₂⟩, ⟨hR₁, hR₂⟩, rfl⟩
    exact (C₁.isPolytope_of_mem hR₁).preimage_inter (C₂.isPolytope_of_mem hR₂) f
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, PolytopalComplex.mem_space_iff, Set.mem_iUnion,
      Set.mem_image, Set.mem_prod, Prod.exists, exists_prop, ℱ]
    constructor
    · rintro ⟨⟨R₁, hR₁, hx1⟩, ⟨R₂, hR₂, hx2⟩⟩
      exact ⟨R₁ ∩ f ⁻¹' R₂, ⟨R₁, R₂, ⟨hR₁, hR₂⟩, rfl⟩, hx1, hx2⟩
    · rintro ⟨_, ⟨R₁, R₂, ⟨hR₁, hR₂⟩, rfl⟩, hx1, hx2⟩
      exact ⟨⟨R₁, hR₁, hx1⟩, ⟨R₂, hR₂, hx2⟩⟩

theorem exists_common_refinement_of_finite_complexes {ι : Type*} [Finite ι] [Nonempty ι]
    {P : Set E} (C : ι → PolytopalComplex E) (hsp : ∀ i, (C i).space = P) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ s ∈ K.faces, ∀ i, ∃ R ∈ (C i).cells, convexHull ℝ (s : Set E) ⊆ R := by
  classical
  let ℱ : Set (Set E) := ⋃ i, (C i).cells
  have hℱ : ℱ.Finite := Set.finite_iUnion fun i => (C i).finite_cells
  have hpoly : ∀ R ∈ ℱ, IsPolytope R := by
    intro R hR
    rcases Set.mem_iUnion.1 hR with ⟨i, hi⟩
    exact (C i).isPolytope_of_mem hi
  let D := PolytopalComplex.ofFinitePolytopes hℱ hpoly
  let K := D.barycentricSubdivision
  refine ⟨K, D.barycentricSubdivision_faces_finite, ?_, ?_⟩
  · rw [D.barycentricSubdivision_space, PolytopalComplex.space_ofFinitePolytopes hℱ hpoly]
    ext x
    simp only [Set.mem_iUnion, ℱ]
    constructor
    · rintro ⟨R, ⟨i, hi⟩, hx⟩
      exact (hsp i) ▸ (C i).subset_space hi hx
    · intro hx
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      have hx' : x ∈ (C i₀).space := (hsp i₀).symm ▸ hx
      rw [PolytopalComplex.mem_space_iff] at hx'
      rcases hx' with ⟨R, hR, hxR⟩
      exact ⟨R, ⟨i₀, hR⟩, hxR⟩
  · intro s hs i
    rcases hs with ⟨𝒞, h𝒞, rfl⟩
    obtain ⟨Q, hQ𝒞, hmax⟩ := isCellChain_exists_top h𝒞
    have hQD : Q ∈ D.cells := h𝒞.1 hQ𝒞
    have hbD : vertexCentroid Q ∈ D.space :=
      D.subset_space hQD (vertexCentroid_mem (D.isPolytope_of_mem hQD) (D.nonempty_of_mem hQD))
    have hbP : vertexCentroid Q ∈ P := by
      rw [PolytopalComplex.space_ofFinitePolytopes hℱ hpoly] at hbD
      rcases Set.mem_iUnion₂.1 hbD with ⟨R₀, hR₀, hxR₀⟩
      rcases Set.mem_iUnion.1 hR₀ with ⟨j, hj⟩
      exact (hsp j) ▸ (C j).subset_space hj hxR₀
    have hbi : vertexCentroid Q ∈ (C i).space := (hsp i).symm ▸ hbP
    rw [PolytopalComplex.mem_space_iff] at hbi
    rcases hbi with ⟨R, hRi, hbR⟩
    have hQR : Q ⊆ R :=
      (PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid hℱ hpoly hQD
        (Set.mem_iUnion.2 ⟨i, hRi⟩)).2 hbR
    refine ⟨R, hRi, convexHull_min ?_ (C i |>.isPolytope_of_mem hRi).convex⟩
    intro v hv
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨Q', hQ', rfl⟩
    have hQ'D := h𝒞.1 hQ'
    exact hQR (hmax Q' hQ' (vertexCentroid_mem (D.isPolytope_of_mem hQ'D) (D.nonempty_of_mem hQ'D)))

theorem exists_common_refinement (C₁ C₂ : PolytopalComplex E) (hsp : C₁.space = C₂.space) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = C₁.space ∧
      ∀ s ∈ K.faces,
        (∃ R₁ ∈ C₁.cells, convexHull ℝ (s : Set E) ⊆ R₁) ∧
        (∃ R₂ ∈ C₂.cells, convexHull ℝ (s : Set E) ⊆ R₂) := by
  let C : Bool → PolytopalComplex E := fun b => if b then C₁ else C₂
  have hC : ∀ b, (C b).space = C₁.space := fun b => by cases b <;> simp [C, hsp]
  obtain ⟨K, hfin, hKsp, href⟩ := exists_common_refinement_of_finite_complexes C hC
  exact ⟨K, hfin, hKsp, fun s hs => ⟨href s hs true, href s hs false⟩⟩

theorem exists_common_triangulation_of_complexes (K₁ K₂ : Geometry.SimplicialComplex ℝ E)
    (hfin₁ : K₁.faces.Finite) (hfin₂ : K₂.faces.Finite) (hsp : K₁.space = K₂.space) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = K₁.space ∧
      ∀ s ∈ K.faces,
        (∃ t₁ ∈ K₁.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t₁ : Set E)) ∧
        (∃ t₂ ∈ K₂.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t₂ : Set E)) := by
  let C₁ := PolytopalComplex.ofSimplicialComplex K₁ hfin₁
  let C₂ := PolytopalComplex.ofSimplicialComplex K₂ hfin₂
  have hCsp : C₁.space = C₂.space := by
    simp only [C₁, C₂, PolytopalComplex.space_ofSimplicialComplex, hsp]
  obtain ⟨K, hfin, hKsp, href⟩ := exists_common_refinement C₁ C₂ hCsp
  rw [PolytopalComplex.space_ofSimplicialComplex] at hKsp
  refine ⟨K, hfin, hKsp, fun s hs => ?_⟩
  obtain ⟨⟨R₁, hR₁, hs₁⟩, ⟨R₂, hR₂, hs₂⟩⟩ := href s hs
  rcases hR₁ with ⟨t₁, ht₁, rfl⟩
  rcases hR₂ with ⟨t₂, ht₂, rfl⟩
  exact ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩

/-- Given a compact polyhedron `P` and a finite family of compact polyhedra `Q i`, there is a
finite triangulation `K` of `P` that simultaneously induces a triangulation of each `P ∩ Q i` as a
subcomplex (in particular of each `Q i` when `Q i ⊆ P`). Cited in issue #4325 notes as
`STOC 1056 Lemma B.1(1)` (unverified against the primary manuscript). -/
theorem exists_triangulation_compatible_with_subpolyhedra {ι : Type*} [Finite ι]
    {P : Set E} (hP : IsPolyhedron P) {Q : ι → Set E} (hQ : ∀ i, IsPolyhedron (Q i)) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ i, ∃ Kᵢ : Geometry.SimplicialComplex ℝ E,
        Kᵢ.faces = {s ∈ K.faces | (s : Set E) ⊆ Q i} ∧ Kᵢ.space = P ∩ Q i := by
  classical
  obtain ⟨CP, hCP⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  choose CQ hCQ using fun i => isPolyhedron_iff_exists_polytopalComplex.1 (hQ i)
  let ℱ : Set (Set E) := CP.cells ∪ ⋃ i, (CQ i).cells
  have hℱ : ℱ.Finite := CP.finite_cells.union (Set.finite_iUnion fun i => (CQ i).finite_cells)
  have hpoly : ∀ R ∈ ℱ, IsPolytope R := by
    rintro R (hR | hR)
    · exact CP.isPolytope_of_mem hR
    · rcases Set.mem_iUnion.1 hR with ⟨i, hi⟩
      exact (CQ i).isPolytope_of_mem hi
  let D := PolytopalComplex.ofFinitePolytopes hℱ hpoly
  let Kall := D.barycentricSubdivision
  let subComplex : Set E → Geometry.SimplicialComplex ℝ E := fun S =>
    { faces := {s ∈ Kall.faces | (s : Set E) ⊆ S}
      indep := fun hs => Kall.indep hs.1
      isRelLowerSet_faces := fun {_} hs =>
        ⟨(Kall.isRelLowerSet_faces hs.1).1, fun _ hts ht =>
          ⟨Kall.down_closed hs.1 hts ht, (Finset.coe_subset.2 hts).trans hs.2⟩⟩
      inter_subset_convexHull := fun hs ht => Kall.inter_subset_convexHull hs.1 ht.1 }
  let K := subComplex P
  have hchain_top : ∀ {𝒞 : Finset (Set E)}, IsCellChain D 𝒞 →
      ∃ Qtop ∈ D.cells, Qtop ∈ 𝒞 ∧
        convexHull ℝ ((𝒞.image vertexCentroid : Finset E) : Set E) ⊆ Qtop := by
    intro 𝒞 h𝒞
    obtain ⟨Qtop, hQtop𝒞, hmax⟩ := isCellChain_exists_top h𝒞
    have hQtopD : Qtop ∈ D.cells := h𝒞.1 hQtop𝒞
    refine ⟨Qtop, hQtopD, hQtop𝒞, convexHull_min ?_ (D.isPolytope_of_mem hQtopD).convex⟩
    intro v hv
    rcases Finset.mem_image.1 (Finset.mem_coe.1 hv) with ⟨Q', hQ', rfl⟩
    have hQ'D := h𝒞.1 hQ'
    exact hmax Q' hQ' (vertexCentroid_mem (D.isPolytope_of_mem hQ'D) (D.nonempty_of_mem hQ'D))
  have hx_Kall : ∀ x ∈ P, x ∈ Kall.space := by
    intro x hxP
    rw [D.barycentricSubdivision_space, PolytopalComplex.space_ofFinitePolytopes hℱ hpoly]
    have hxCP : x ∈ CP.space := hCP.symm ▸ hxP
    rw [PolytopalComplex.mem_space_iff] at hxCP
    rcases hxCP with ⟨R, hR, hxR⟩
    exact Set.mem_biUnion (Or.inl hR) hxR
  have hsubset_cell : ∀ {s : Finset E} {C : PolytopalComplex E},
      s ∈ Kall.faces → (∀ R ∈ C.cells, R ∈ ℱ) → (s : Set E) ⊆ C.space →
      convexHull ℝ (s : Set E) ⊆ C.space := by
    intro s C hs hCℱ hsS
    rcases hs with ⟨𝒞, h𝒞, rfl⟩
    obtain ⟨Qtop, hQtopD, hQtop𝒞, hsQtop⟩ := hchain_top h𝒞
    have hb_mem : vertexCentroid Qtop ∈ C.space :=
      hsS (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hQtop𝒞))
    rw [PolytopalComplex.mem_space_iff] at hb_mem
    rcases hb_mem with ⟨R, hRC, hbR⟩
    have hQtopR : Qtop ⊆ R :=
      (PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid hℱ hpoly hQtopD
        (hCℱ R hRC)).2 hbR
    exact hsQtop.trans (hQtopR.trans (C.subset_space hRC))
  refine ⟨K, D.barycentricSubdivision_faces_finite.subset fun _ hs => hs.1, ?_, fun i => ?_⟩
  · refine Subset.antisymm (Set.iUnion₂_subset fun s hs => ?_) fun x hxP => ?_
    · exact hCP ▸ hsubset_cell hs.1 (fun _ h => Or.inl h) (hCP.symm ▸ hs.2)
    · rcases Set.mem_iUnion₂.1 (hx_Kall x hxP) with ⟨s, hs, hxs⟩
      rcases hs with ⟨𝒞, h𝒞, rfl⟩
      obtain ⟨Qtop, hQtopD, _, hsQtop⟩ := hchain_top h𝒞
      have hxCP : x ∈ CP.space := hCP.symm ▸ hxP
      rw [PolytopalComplex.mem_space_iff] at hxCP
      rcases hxCP with ⟨RP, hRP, hxRP⟩
      have hface := (PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid hℱ hpoly
        hQtopD (.inl hRP)).1
      obtain ⟨t, hts, htne, htRP, hxt⟩ := exists_finset_subset_convexHull_of_isExtreme
        (D.isPolytope_of_mem hQtopD).convex (Subset.trans (subset_convexHull ℝ _) hsQtop)
        hface.isExtreme ⟨hxs, hsQtop hxs, hxRP⟩
      exact Set.mem_biUnion ⟨Kall.down_closed ⟨𝒞, h𝒞, rfl⟩ hts htne,
        htRP.trans (inter_subset_right.trans ((CP.subset_space hRP).trans (hCP ▸ Subset.rfl)))⟩ hxt
  · refine ⟨subComplex (P ∩ Q i), ?_, ?_⟩
    · ext s
      dsimp only [subComplex, K]
      simp only [mem_ofPred_eq, Set.subset_inter_iff, and_assoc]
    · refine Subset.antisymm (Set.iUnion₂_subset fun s hs => ?_) fun x ⟨hxP, hxQ⟩ => ?_
      · have hs1 : (s : Set E) ⊆ CP.space :=
          hCP.symm ▸ hs.2.trans inter_subset_left
        have hs2 : (s : Set E) ⊆ (CQ i).space :=
          (hCQ i).symm ▸ hs.2.trans inter_subset_right
        exact Set.subset_inter
          (hCP ▸ hsubset_cell hs.1 (fun _ h => Or.inl h) hs1)
          ((hCQ i) ▸ hsubset_cell hs.1 (fun _ h => Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)) hs2)
      · rcases Set.mem_iUnion₂.1 (hx_Kall x hxP) with ⟨s, hs, hxs⟩
        have hsf := hs
        rcases hs with ⟨𝒞, h𝒞, rfl⟩
        obtain ⟨Qtop, hQtopD, _, hsQtop⟩ := hchain_top h𝒞
        have hxCP : x ∈ CP.space := hCP.symm ▸ hxP
        have hxCQ : x ∈ (CQ i).space := (hCQ i).symm ▸ hxQ
        rw [PolytopalComplex.mem_space_iff] at hxCP hxCQ
        rcases hxCP with ⟨RP, hRP, hxRP⟩
        rcases hxCQ with ⟨RQ, hRQ, hxRQ⟩
        have hfaceP := (PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid hℱ hpoly
          hQtopD (.inl hRP)).1
        have hfaceQ := (PolytopalComplex.ofFinitePolytopes_inter_face_and_vertexCentroid hℱ hpoly
          hQtopD (.inr (Set.mem_iUnion.2 ⟨i, hRQ⟩))).1
        have hfacePQ : IsPolytopeFace Qtop (Qtop ∩ (RP ∩ RQ)) := by
          rw [show Qtop ∩ (RP ∩ RQ) = (Qtop ∩ RP) ∩ (Qtop ∩ RQ) by
            ext y; simp only [mem_inter_iff]; tauto]
          exact hfaceP.inter hfaceQ
        obtain ⟨t, hts, htne, htR, hxt⟩ := exists_finset_subset_convexHull_of_isExtreme
          (D.isPolytope_of_mem hQtopD).convex (Subset.trans (subset_convexHull ℝ _) hsQtop)
          hfacePQ.isExtreme ⟨hxs, hsQtop hxs, hxRP, hxRQ⟩
        refine Set.mem_biUnion ⟨Kall.down_closed hsf hts htne, fun v hv => ?_⟩ hxt
        have hv' := htR hv
        exact ⟨hCP ▸ CP.subset_space hRP hv'.2.1, (hCQ i) ▸ (CQ i).subset_space hRQ hv'.2.2⟩

end Polyhedra

end Cslib.Polyhedra
