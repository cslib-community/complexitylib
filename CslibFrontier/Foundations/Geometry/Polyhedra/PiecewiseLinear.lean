/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/PiecewiseLinear.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.Polyhedra.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Piecewise-linear maps on compact polyhedra

This module defines affine maps on subsets (`IsAffineOn`) and piecewise-linear (PL) maps on compact
polyhedra (`IsPLOn`), and establishes Rourke–Sanderson-style closure rules: continuity,
restriction to subpolyhedra, gluing on finite closed covers and piecewise unions, real linear
combinations, products/tuples, `min`/`max`/`abs`/finite suprema, composition, polyhedrality of
images and preimages, and triangulation compatibility.

## Main definitions

* `Cslib.Polyhedra.IsAffineOn`: `f` agrees with an affine map `E →ᵃ[ℝ] F` on a set `S`.
* `Cslib.Polyhedra.IsPLOn`: `f` is piecewise-linear on a compact polyhedron `P`, meaning `P` is a
  compact polyhedron covered by a finite polytopal complex on whose cells `f` is affine.

## Main results

* `Cslib.Polyhedra.isPLOn_iff_simplicialComplex`,
  `Cslib.Polyhedra.isPLOn_iff_finite_polytope_cover`: equivalent characterizations by finite
  simplicial complexes and finite polytope covers.
* `Cslib.Polyhedra.IsPLOn.continuousOn`: PL maps are continuous on `P`.
* `Cslib.Polyhedra.IsPLOn.restrict`, `Cslib.Polyhedra.IsPLOn.of_finiteCover`,
  `Cslib.Polyhedra.IsPLOn.piecewise_union`: restriction and gluing on finite closed covers.
* `Cslib.Polyhedra.IsPLOn.add`, `Cslib.Polyhedra.IsPLOn.sub`, `Cslib.Polyhedra.IsPLOn.smul`,
  `Cslib.Polyhedra.IsPLOn.sum`, `Cslib.Polyhedra.IsPLOn.prodMk`, `Cslib.Polyhedra.IsPLOn.pi`,
  `Cslib.Polyhedra.IsPLOn.min`, `Cslib.Polyhedra.IsPLOn.max`, `Cslib.Polyhedra.IsPLOn.abs`,
  `Cslib.Polyhedra.IsPLOn.comp`: Rourke–Sanderson-style closure rules.
* `Cslib.Polyhedra.IsPLOn.image_isPolyhedron`,
  `Cslib.Polyhedra.IsPLOn.preimage_inter_isPolyhedron`,
  `Cslib.Polyhedra.exists_triangulation_of_isPLOn_compatible`: images, preimages, and compatible
  triangulations under PL maps.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
* Issue #4325 notes (`STOC 1056 Lemma B.1` label; unverified against the primary manuscript).
-/

public section

namespace Cslib.Polyhedra

open Set Finset

section BasicAffine

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A map `f : E → F` is **affine on `S`** if it agrees on `S` with a global affine map
`g : E →ᵃ[ℝ] F`. -/
@[expose] def IsAffineOn (f : E → F) (S : Set E) : Prop :=
  ∃ g : E →ᵃ[ℝ] F, Set.EqOn f g S

theorem IsAffineOn.congr {f f' : E → F} {S : Set E} (h : IsAffineOn f S)
    (heq : Set.EqOn f' f S) : IsAffineOn f' S :=
  let ⟨g, hg⟩ := h
  ⟨g, fun _ hx => (heq hx).trans (hg hx)⟩

theorem IsAffineOn.mono {f : E → F} {S T : Set E} (hST : S ⊆ T) (h : IsAffineOn f T) :
    IsAffineOn f S :=
  let ⟨g, hg⟩ := h
  ⟨g, hg.mono hST⟩

theorem isAffineOn_empty (f : E → F) : IsAffineOn f ∅ :=
  ⟨AffineMap.const ℝ E 0, fun _ h => False.elim h⟩

theorem IsAffineOn.const (S : Set E) (c : F) : IsAffineOn (fun _ => c) S :=
  ⟨AffineMap.const ℝ E c, fun _ _ => rfl⟩

theorem IsAffineOn.id (S : Set E) : IsAffineOn (id : E → E) S :=
  ⟨AffineMap.id ℝ E, fun _ _ => rfl⟩

theorem IsAffineOn.affineMap (g : E →ᵃ[ℝ] F) (S : Set E) : IsAffineOn g S :=
  ⟨g, fun _ _ => rfl⟩

theorem IsAffineOn.add {f g : E → F} {S : Set E} (hf : IsAffineOn f S) (hg : IsAffineOn g S) :
    IsAffineOn (fun x => f x + g x) S := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨a + b, fun x hx => by simp only [AffineMap.coe_add, Pi.add_apply, ha hx, hb hx]⟩

theorem IsAffineOn.neg {f : E → F} {S : Set E} (hf : IsAffineOn f S) :
    IsAffineOn (fun x => -f x) S := by
  rcases hf with ⟨a, ha⟩
  exact ⟨-a, fun x hx => by simp only [AffineMap.coe_neg, Pi.neg_apply, ha hx]⟩

theorem IsAffineOn.sub {f g : E → F} {S : Set E} (hf : IsAffineOn f S) (hg : IsAffineOn g S) :
    IsAffineOn (fun x => f x - g x) S :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsAffineOn.smul {f : E → F} {S : Set E} (c : ℝ) (hf : IsAffineOn f S) :
    IsAffineOn (fun x => c • f x) S := by
  rcases hf with ⟨a, ha⟩
  exact ⟨c • a, fun x hx => by simp only [AffineMap.coe_smul, Pi.smul_apply, ha hx]⟩

theorem IsAffineOn.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {S : Set E}
    (hf : ∀ i ∈ s, IsAffineOn (f i) S) :
    IsAffineOn (fun x => ∑ i ∈ s, f i x) S := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsAffineOn.const S (0 : F)
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr fun x _ => by rw [Finset.sum_insert ha]

theorem IsAffineOn.prodMk {f : E → F} {g : E → G} {S : Set E} (hf : IsAffineOn f S)
    (hg : IsAffineOn g S) : IsAffineOn (fun x => (f x, g x)) S := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨a.prod b, fun x hx => Prod.ext (ha hx) (hb hx)⟩

theorem IsAffineOn.fst (S : Set (E × F)) : IsAffineOn (Prod.fst : E × F → E) S :=
  ⟨AffineMap.fst, fun _ _ => rfl⟩

theorem IsAffineOn.snd (S : Set (E × F)) : IsAffineOn (Prod.snd : E × F → F) S :=
  ⟨AffineMap.snd, fun _ _ => rfl⟩

theorem IsAffineOn.pi {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)] {f : ∀ i, E → H i}
    {S : Set E} (hf : ∀ i, IsAffineOn (f i) S) :
    IsAffineOn (fun x i => f i x) S := by
  choose g hg using hf
  exact ⟨AffineMap.pi g, fun x hx => funext fun i => hg i hx⟩

theorem IsAffineOn.comp {f : E → F} {g : F → G} {S : Set E} {T : Set F}
    (hf : IsAffineOn f S) (hg : IsAffineOn g T) (hST : MapsTo f S T) :
    IsAffineOn (g ∘ f) S := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  exact ⟨b.comp a, fun x hx => by
    simp only [Function.comp_apply, AffineMap.coe_comp]
    rw [← ha hx, hb (hST hx)]⟩

theorem IsAffineOn.map_convex_combo {f : E → F} {S : Set E} (hf : IsAffineOn f S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) {a b : ℝ} (hab : a + b = 1)
    (hxy : a • x + b • y ∈ S) :
    f (a • x + b • y) = a • f x + b • f y := by
  rcases hf with ⟨g, hg⟩
  have ha : a = 1 - b := eq_sub_of_add_eq hab
  rw [hg hxy, hg hx, hg hy, ha, ← AffineMap.lineMap_apply_module, g.apply_lineMap,
    AffineMap.lineMap_apply_module]

end BasicAffine

section GeneralTarget

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsAffineOn.image_isPolytope {f : E → F} {P : Set E}
    (hP : IsPolytope P) (hf : IsAffineOn f P) : IsPolytope (f '' P) := by
  rcases hf with ⟨g, hg⟩
  rw [Set.EqOn.image_eq hg]
  exact hP.image g

/-- Shared schema for functions on a compact polyhedron `P` satisfying a local cell predicate
`PropCell` on every cell of a finite polytopal complex covering `P`. -/
@[expose] def IsPiecewiseOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (PropCell : (E → F) → Set E → Prop) (P : Set E) (f : E → F) : Prop :=
  ∃ C : PolytopalComplex E, C.space = P ∧ ∀ Q ∈ C.cells, PropCell f Q

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isPiecewiseOn_congr {PropCell : (E → F) → Set E → Prop}
    (hcongr : ∀ {g g' : E → F} {S : Set E}, Set.EqOn g' g S → PropCell g S → PropCell g' S)
    {P : Set E} {f f' : E → F} (hf : IsPiecewiseOn PropCell P f) (heq : Set.EqOn f' f P) :
    IsPiecewiseOn PropCell P f' := by
  rcases hf with ⟨C, hC, hprop⟩
  exact ⟨C, hC, fun Q hQ => hcongr (heq.mono (hC ▸ C.subset_space hQ)) (hprop Q hQ)⟩

omit [NormedSpace ℝ F] in
theorem isPiecewiseOn_continuousOn {PropCell : (E → F) → Set E → Prop}
    (hcont : ∀ {g : E → F} {S : Set E}, PropCell g S → ContinuousOn g S)
    {P : Set E} {f : E → F} (hf : IsPiecewiseOn PropCell P f) : ContinuousOn f P := by
  rcases hf with ⟨C, rfl, hprop⟩
  rw [PolytopalComplex.space, Set.biUnion_eq_iUnion]
  have : Finite C.cells := C.finite_cells.to_subtype
  exact (locallyFinite_of_finite fun Q : C.cells => (Q : Set E)).continuousOn_iUnion
    (fun Q => (C.isPolytope_of_mem Q.2).isClosed)
    (fun Q => hcont (hprop Q Q.2))

/-- A map `f : E → F` is **piecewise-linear on `P`** (`IsPLOn P f`) if `P` is a compact
polyhedron admitted as the space of a finite polytopal complex on whose cells `f` is affine. -/
@[expose] def IsPLOn (P : Set E) (f : E → F) : Prop :=
  IsPiecewiseOn IsAffineOn P f

theorem IsPLOn.congr {P : Set E} {f f' : E → F} (hf : IsPLOn P f) (heq : Set.EqOn f' f P) :
    IsPLOn P f' :=
  isPiecewiseOn_congr (fun heq hg => hg.congr heq) hf heq

theorem IsPLOn.neg {P : Set E} {f : E → F} (hf : IsPLOn P f) : IsPLOn P (fun x => -f x) := by
  rcases hf with ⟨C, hC, haff⟩
  exact ⟨C, hC, fun Q hQ => (haff Q hQ).neg⟩

theorem IsPLOn.smul {P : Set E} (c : ℝ) {f : E → F} (hf : IsPLOn P f) :
    IsPLOn P (fun x => c • f x) := by
  rcases hf with ⟨C, hC, haff⟩
  exact ⟨C, hC, fun Q hQ => (haff Q hQ).smul c⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isPiecewiseOn_empty (PropCell : (E → F) → Set E → Prop) (f : E → F) :
    IsPiecewiseOn PropCell (∅ : Set E) f := by
  refine ⟨PolytopalComplex.empty, PolytopalComplex.space_empty, fun Q hQ => ?_⟩
  exfalso
  obtain ⟨x, hx⟩ := PolytopalComplex.empty.nonempty_of_mem hQ
  have hxsp : x ∈ (PolytopalComplex.empty : PolytopalComplex E).space :=
    PolytopalComplex.empty.subset_space hQ hx
  rw [PolytopalComplex.space_empty] at hxsp
  exact hxsp

theorem isPLOn_empty (f : E → F) : IsPLOn (∅ : Set E) f :=
  isPiecewiseOn_empty IsAffineOn f

end GeneralTarget

section SchemaFiniteDim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPiecewiseOn_iff_simplicialComplex {F : Type*} {PropCell : (E → F) → Set E → Prop}
    (hmono : ∀ {g : E → F} {S T : Set E}, T ⊆ S → PropCell g S → PropCell g T)
    {P : Set E} {f : E → F} :
    IsPiecewiseOn PropCell P f ↔
      ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
        ∀ s ∈ K.faces, PropCell f (convexHull ℝ (s : Set E)) := by
  constructor
  · rintro ⟨C, rfl, hprop⟩
    refine ⟨C.barycentricSubdivision, C.barycentricSubdivision_faces_finite,
      C.barycentricSubdivision_space, fun s hs => ?_⟩
    obtain ⟨Q, hQ, hsub⟩ := C.barycentricSubdivision_simplex_subset hs
    exact hmono hsub (hprop Q hQ)
  · rintro ⟨K, hfin, rfl, hprop⟩
    refine ⟨PolytopalComplex.ofSimplicialComplex K hfin,
      PolytopalComplex.space_ofSimplicialComplex K hfin, ?_⟩
    rw [PolytopalComplex.cells_ofSimplicialComplex]
    rintro _ ⟨s, hs, rfl⟩
    exact hprop s hs

theorem isPiecewiseOn_iff_finite_polytope_cover {F : Type*} {PropCell : (E → F) → Set E → Prop}
    (hmono : ∀ {g : E → F} {S T : Set E}, T ⊆ S → PropCell g S → PropCell g T)
    {P : Set E} {f : E → F} :
    IsPiecewiseOn PropCell P f ↔ ∃ ℱ : Set (Set E), ℱ.Finite ∧
      (∀ Q ∈ ℱ, IsPolytope Q ∧ PropCell f Q) ∧ P = ⋃ Q ∈ ℱ, Q := by
  constructor
  · rintro ⟨C, rfl, hprop⟩
    exact ⟨C.cells, C.finite_cells, fun Q hQ => ⟨C.isPolytope_of_mem hQ, hprop Q hQ⟩, rfl⟩
  · rintro ⟨ℱ, hℱ, hcov, rfl⟩
    have hpoly : ∀ Q ∈ ℱ, IsPolytope Q := fun Q hQ => (hcov Q hQ).1
    refine ⟨PolytopalComplex.ofFinitePolytopes hℱ hpoly,
      PolytopalComplex.space_ofFinitePolytopes hℱ hpoly, fun S hS => ?_⟩
    obtain ⟨Q, hQ, hSQ⟩ := PolytopalComplex.ofFinitePolytopes_cell_subset hℱ hpoly hS
    exact hmono hSQ (hcov Q hQ).2

theorem isPiecewiseOn_of_finiteCover {F : Type*} {PropCell : (E → F) → Set E → Prop}
    (hmono : ∀ {g : E → F} {S T : Set E}, T ⊆ S → PropCell g S → PropCell g T)
    {ι : Type*} [Finite ι] {P : Set E} {Q : ι → Set E}
    {f : E → F} (hcov : (⋃ i, Q i) = P) (hf : ∀ i, IsPiecewiseOn PropCell (Q i) f) :
    IsPiecewiseOn PropCell P f := by
  classical
  choose C hC using hf
  let ℱ : Set (Set E) := ⋃ i, (C i).cells
  have hℱ : ℱ.Finite := Set.finite_iUnion fun i => (C i).finite_cells
  refine (isPiecewiseOn_iff_finite_polytope_cover (PropCell := PropCell) hmono).2
    ⟨ℱ, hℱ, fun R hR => ?_, ?_⟩
  · rcases Set.mem_iUnion.1 hR with ⟨i, hi⟩
    exact ⟨(C i).isPolytope_of_mem hi, (hC i).2 R hi⟩
  · rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, ℱ]
    constructor
    · rintro ⟨i, hi⟩
      have hxsp : x ∈ (C i).space := (hC i).1.symm ▸ hi
      rw [PolytopalComplex.mem_space_iff] at hxsp
      rcases hxsp with ⟨R, hR, hxR⟩
      exact ⟨R, ⟨i, hR⟩, hxR⟩
    · rintro ⟨R, ⟨i, hi⟩, hxR⟩
      exact ⟨i, (hC i).1 ▸ (C i).subset_space hi hxR⟩

open Classical in
theorem isPiecewiseOn_piecewise_union {F : Type*} {PropCell : (E → F) → Set E → Prop}
    (hmono : ∀ {g : E → F} {S T : Set E}, T ⊆ S → PropCell g S → PropCell g T)
    (hcongr : ∀ {g g' : E → F} {S : Set E}, Set.EqOn g' g S → PropCell g S → PropCell g' S)
    {P Q : Set E} {f g : E → F}
    (hf : IsPiecewiseOn PropCell P f) (hg : IsPiecewiseOn PropCell Q g)
    (hagree : ∀ x ∈ P ∩ Q, f x = g x) :
    IsPiecewiseOn PropCell (P ∪ Q) (fun x => if x ∈ P then f x else g x) := by
  let h := fun x => if x ∈ P then f x else g x
  have hP : IsPiecewiseOn PropCell P h := isPiecewiseOn_congr hcongr hf fun x hx => by
    dsimp only [h]
    split_ifs
    rfl
  have hQ : IsPiecewiseOn PropCell Q h := isPiecewiseOn_congr hcongr hg fun x hx => by
    dsimp only [h]
    split_ifs with hxP
    · exact hagree x ⟨hxP, hx⟩
    · rfl
  have hcov : (⋃ b : Bool, bif b then P else Q) = P ∪ Q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool, Bool.cond_false, Bool.cond_true]
    tauto
  refine isPiecewiseOn_of_finiteCover (PropCell := PropCell) (f := h) hmono hcov fun b => ?_
  cases b
  · exact hQ
  · exact hP

theorem isPiecewiseOn_restrict {F : Type*} {PropCell : (E → F) → Set E → Prop}
    (hmono : ∀ {g : E → F} {S T : Set E}, T ⊆ S → PropCell g S → PropCell g T)
    {P Q : Set E} {f : E → F} (hf : IsPiecewiseOn PropCell P f)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) : IsPiecewiseOn PropCell Q f := by
  rcases hf with ⟨CP, hCP, hprop⟩
  obtain ⟨CQ, hCQ⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  let ℱ : Set (Set E) := (fun p : Set E × Set E => p.1 ∩ p.2) '' (CP.cells ×ˢ CQ.cells)
  refine (isPiecewiseOn_iff_finite_polytope_cover (PropCell := PropCell) hmono).2
    ⟨ℱ, (CP.finite_cells.prod CQ.finite_cells).image _, ?_, ?_⟩
  · rintro _ ⟨⟨RP, RQ⟩, ⟨hRP, hRQ⟩, rfl⟩
    exact ⟨(CP.isPolytope_of_mem hRP).inter (CQ.isPolytope_of_mem hRQ),
      hmono inter_subset_left (hprop RP hRP)⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Prod.exists, exists_prop, ℱ]
    constructor
    · intro hxQ
      have hxP : x ∈ CP.space := hCP.symm ▸ hQP hxQ
      have hxQ' : x ∈ CQ.space := hCQ.symm ▸ hxQ
      rw [PolytopalComplex.mem_space_iff] at hxP hxQ'
      rcases hxP with ⟨RP, hRP, hxRP⟩
      rcases hxQ' with ⟨RQ, hRQ, hxRQ⟩
      exact ⟨RP ∩ RQ, ⟨RP, RQ, ⟨hRP, hRQ⟩, rfl⟩, hxRP, hxRQ⟩
    · rintro ⟨_, ⟨RP, RQ, ⟨_, hRQ⟩, rfl⟩, _, hxRQ⟩
      exact hCQ ▸ CQ.subset_space hRQ hxRQ

theorem isPiecewiseOn_exists_common_complex {F G : Type*}
    {Prop₁ : (E → F) → Set E → Prop} {Prop₂ : (E → G) → Set E → Prop}
    (hmono₁ : ∀ {f : E → F} {S T : Set E}, T ⊆ S → Prop₁ f S → Prop₁ f T)
    (hmono₂ : ∀ {g : E → G} {S T : Set E}, T ⊆ S → Prop₂ g S → Prop₂ g T)
    {P : Set E} {f : E → F} {g : E → G}
    (hf : IsPiecewiseOn Prop₁ P f) (hg : IsPiecewiseOn Prop₂ P g) :
    ∃ C : PolytopalComplex E, C.space = P ∧
      (∀ Q ∈ C.cells, Prop₁ f Q) ∧ (∀ Q ∈ C.cells, Prop₂ g Q) := by
  rcases hf with ⟨Cf, hCf, hp₁⟩
  rcases hg with ⟨Cg, hCg, hp₂⟩
  have hsp : Cf.space = Cg.space := hCf.trans hCg.symm
  obtain ⟨K, hKfin, hKsp, href⟩ := exists_common_refinement Cf Cg hsp
  refine ⟨PolytopalComplex.ofSimplicialComplex K hKfin, ?_, ?_, ?_⟩
  · rw [PolytopalComplex.space_ofSimplicialComplex, hKsp, hCf]
  · rw [PolytopalComplex.cells_ofSimplicialComplex]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨Rf, hRf, hsub⟩ := (href s hs).1
    exact hmono₁ hsub (hp₁ Rf hRf)
  · rw [PolytopalComplex.cells_ofSimplicialComplex]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨Rg, hRg, hsub⟩ := (href s hs).2
    exact hmono₂ hsub (hp₂ Rg hRg)

end SchemaFiniteDim

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPLOn.isPolyhedron {P : Set E} {f : E → F} (hf : IsPLOn P f) : IsPolyhedron P :=
  let ⟨C, hC, _⟩ := hf
  isPolyhedron_iff_exists_polytopalComplex.2 ⟨C, hC⟩

theorem IsAffineOn.continuousOn {f : E → F} {S : Set E} (hf : IsAffineOn f S) :
    ContinuousOn f S := by
  rcases hf with ⟨g, hg⟩
  exact g.continuous_of_finiteDimensional.continuousOn.congr hg

theorem isPLOn_iff_simplicialComplex {P : Set E} {f : E → F} :
    IsPLOn P f ↔ ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ s ∈ K.faces, IsAffineOn f (convexHull ℝ (s : Set E)) :=
  isPiecewiseOn_iff_simplicialComplex (fun hsub hg => hg.mono hsub)

theorem isPLOn_iff_finite_polytope_cover {P : Set E} {f : E → F} :
    IsPLOn P f ↔ ∃ ℱ : Set (Set E), ℱ.Finite ∧
      (∀ Q ∈ ℱ, IsPolytope Q ∧ IsAffineOn f Q) ∧ P = ⋃ Q ∈ ℱ, Q :=
  isPiecewiseOn_iff_finite_polytope_cover (fun hsub hg => hg.mono hsub)

theorem IsPLOn.affineMap {P : Set E} (hP : IsPolyhedron P) (g : E →ᵃ[ℝ] F) : IsPLOn P g := by
  obtain ⟨C, hC⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  exact ⟨C, hC, fun Q _ => IsAffineOn.affineMap g Q⟩

theorem IsPLOn.const {P : Set E} (hP : IsPolyhedron P) (c : F) :
    IsPLOn P (fun _ => c) :=
  IsPLOn.affineMap hP (AffineMap.const ℝ E c)

theorem IsPLOn.id {P : Set E} (hP : IsPolyhedron P) : IsPLOn P (id : E → E) :=
  IsPLOn.affineMap hP (AffineMap.id ℝ E)

theorem IsPLOn.continuousOn {P : Set E} {f : E → F} (hf : IsPLOn P f) : ContinuousOn f P :=
  isPiecewiseOn_continuousOn (fun h => h.continuousOn) hf

theorem IsPLOn.of_finiteCover {ι : Type*} [Finite ι] {P : Set E} {Q : ι → Set E}
    {f : E → F} (hcov : (⋃ i, Q i) = P) (hf : ∀ i, IsPLOn (Q i) f) : IsPLOn P f :=
  isPiecewiseOn_of_finiteCover (fun hsub hg => hg.mono hsub) hcov hf

open Classical in
theorem IsPLOn.piecewise_union {P Q : Set E} {f g : E → F} (hf : IsPLOn P f) (hg : IsPLOn Q g)
    (hagree : ∀ x ∈ P ∩ Q, f x = g x) :
    IsPLOn (P ∪ Q) (fun x => if x ∈ P then f x else g x) :=
  isPiecewiseOn_piecewise_union (fun hsub hu => hu.mono hsub)
    (fun heq hu => hu.congr heq) hf hg hagree

theorem IsPLOn.restrict {P Q : Set E} {f : E → F} (hf : IsPLOn P f)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) : IsPLOn Q f :=
  isPiecewiseOn_restrict (fun hsub hg => hg.mono hsub) hf hQ hQP

theorem IsPLOn.exists_common_complex {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Set E} {f : E → F} {g : E → G}
    (hf : IsPLOn P f) (hg : IsPLOn P g) :
    ∃ C : PolytopalComplex E, C.space = P ∧
      (∀ Q ∈ C.cells, IsAffineOn f Q) ∧ (∀ Q ∈ C.cells, IsAffineOn g Q) :=
  isPiecewiseOn_exists_common_complex (fun hsub hu => hu.mono hsub)
    (fun hsub hv => hv.mono hsub) hf hg

theorem IsPLOn.add {P : Set E} {f g : E → F} (hf : IsPLOn P f) (hg : IsPLOn P g) :
    IsPLOn P (fun x => f x + g x) := by
  obtain ⟨C, hC, haff_f, haff_g⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ => (haff_f Q hQ).add (haff_g Q hQ)⟩

theorem IsPLOn.sub {P : Set E} {f g : E → F} (hf : IsPLOn P f) (hg : IsPLOn P g) :
    IsPLOn P (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsPLOn.sum {ι : Type*} (s : Finset ι) {P : Set E} (hP : IsPolyhedron P)
    {f : ι → E → F} (hf : ∀ i ∈ s, IsPLOn P (f i)) :
    IsPLOn P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => exact (IsPLOn.const hP (0 : F)).congr fun _ _ => Finset.sum_empty
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr fun x _ => Finset.sum_insert ha

theorem IsPLOn.prodMk {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Set E} {f : E → F} {g : E → G}
    (hf : IsPLOn P f) (hg : IsPLOn P g) : IsPLOn P (fun x => (f x, g x)) := by
  obtain ⟨C, hC, haff_f, haff_g⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ => (haff_f Q hQ).prodMk (haff_g Q hQ)⟩

theorem IsPLOn.fst [FiniteDimensional ℝ F] {P : Set (E × F)} (hP : IsPolyhedron P) :
    IsPLOn P (Prod.fst : E × F → E) :=
  IsPLOn.affineMap hP AffineMap.fst

theorem IsPLOn.snd [FiniteDimensional ℝ F] {P : Set (E × F)} (hP : IsPolyhedron P) :
    IsPLOn P (Prod.snd : E × F → F) :=
  IsPLOn.affineMap hP AffineMap.snd

theorem IsPLOn.pi {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    {P : Set E} (hP : IsPolyhedron P)
    {f : ∀ i, E → H i} (hf : ∀ i, IsPLOn P (f i)) :
    IsPLOn P (fun x i => f i x) := by
  rcases isEmpty_or_nonempty ι with hemp | hne
  · refine (IsPLOn.const hP (fun i => False.elim (hemp.false i))).congr ?_
    intro x _
    funext i
    exact False.elim (hemp.false i)
  · choose C hC using hf
    obtain ⟨K, hKfin, hKsp, href⟩ :=
      exists_common_refinement_of_finite_complexes C fun i => (hC i).1
    refine ⟨PolytopalComplex.ofSimplicialComplex K hKfin, ?_, ?_⟩
    · rw [PolytopalComplex.space_ofSimplicialComplex, hKsp]
    · rw [PolytopalComplex.cells_ofSimplicialComplex]
      rintro _ ⟨s, hs, rfl⟩
      refine IsAffineOn.pi fun i => ?_
      obtain ⟨R, hR, hsub⟩ := href s hs i
      exact ((hC i).2 R hR).mono hsub

theorem IsPLOn.min {P : Set E} {f g : E → ℝ} (hf : IsPLOn P f) (hg : IsPLOn P g) :
    IsPLOn P (fun x => min (f x) (g x)) := by
  classical
  obtain ⟨C, hC, haff_f, haff_g⟩ := hf.exists_common_complex hg
  have hcov : (⋃ Q : C.finite_cells.toFinset, (Q : Set E)) = P := by
    rw [← hC]
    ext x
    simp only [Set.mem_iUnion, PolytopalComplex.mem_space_iff, Subtype.exists,
      Set.Finite.mem_toFinset, exists_prop]
  refine IsPLOn.of_finiteCover hcov fun Q => ?_
  have hQpoly : IsPolytope (Q : Set E) := C.isPolytope_of_mem (C.finite_cells.mem_toFinset.1 Q.2)
  rcases haff_f (Q : Set E) (C.finite_cells.mem_toFinset.1 Q.2) with ⟨a, ha⟩
  rcases haff_g (Q : Set E) (C.finite_cells.mem_toFinset.1 Q.2) with ⟨b, hb⟩
  let Q₁ := (Q : Set E) ∩ {x | ∀ m ∈ ({a - b} : Set (E →ᵃ[ℝ] ℝ)), m x ≤ 0}
  let Q₂ := (Q : Set E) ∩ {x | ∀ m ∈ ({b - a} : Set (E →ᵃ[ℝ] ℝ)), m x ≤ 0}
  have hQ₁ : IsPolytope Q₁ := hQpoly.inter_setOf_le (finite_singleton _)
  have hQ₂ : IsPolytope Q₂ := hQpoly.inter_setOf_le (finite_singleton _)
  have hcovQ : (⋃ t : Bool, if t then Q₁ else Q₂) = (Q : Set E) := by
    ext x
    simp only [Set.mem_iUnion, Bool.exists_bool, ↓reduceIte, Q₁, Q₂, mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, AffineMap.coe_sub, Pi.sub_apply,
      sub_nonpos]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_total (a x) (b x) with hle | hge
      · exact .inr ⟨hx, hle⟩
      · exact .inl ⟨hx, hge⟩
  refine IsPLOn.of_finiteCover hcovQ fun t => ?_
  cases t
  · refine (IsPLOn.affineMap hQ₂.isPolyhedron b).congr fun x ⟨hxQ, hxle⟩ => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, AffineMap.coe_sub,
      Pi.sub_apply, sub_nonpos] at hxle
    rw [ha hxQ, hb hxQ, min_eq_right hxle]
  · refine (IsPLOn.affineMap hQ₁.isPolyhedron a).congr fun x ⟨hxQ, hxle⟩ => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, AffineMap.coe_sub,
      Pi.sub_apply, sub_nonpos] at hxle
    rw [ha hxQ, hb hxQ, min_eq_left hxle]

theorem IsPLOn.max {P : Set E} {f g : E → ℝ} (hf : IsPLOn P f) (hg : IsPLOn P g) :
    IsPLOn P (fun x => max (f x) (g x)) := by
  have hmin := (hf.neg).min (hg.neg)
  refine hmin.neg.congr fun x _ => ?_
  dsimp only
  rcases le_total (f x) (g x) with hle | hge
  · rw [max_eq_right hle, min_eq_right (neg_le_neg hle), neg_neg]
  · rw [max_eq_left hge, min_eq_left (neg_le_neg hge), neg_neg]

theorem IsPLOn.abs {P : Set E} {f : E → ℝ} (hf : IsPLOn P f) :
    IsPLOn P (fun x => |f x|) :=
  (hf.max hf.neg).congr fun x _ => by rw [abs_eq_max_neg]

theorem IsPLOn.finset_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {P : Set E}
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPLOn P (f i)) :
    IsPLOn P (fun x => s.sup' hs fun i => f i x) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact (hf a (Finset.mem_singleton_self a)).congr fun x _ => by rw [Finset.sup'_singleton]
  | cons a t ha ht ih =>
    have ha_pl := hf a (Finset.mem_cons_self a t)
    have ht_pl := ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
    exact (ha_pl.max ht_pl).congr fun x _ => by rw [Finset.sup'_cons]

private lemma finset_inf'_eq_neg_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℝ) :
    s.inf' hs g = -(s.sup' hs fun i => -g i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp only [Finset.inf'_singleton, Finset.sup'_singleton, neg_neg]
  | cons a t ha ht ih =>
    rw [Finset.inf'_cons (H := ht), Finset.sup'_cons (H := ht), neg_sup, neg_neg, ih]

theorem IsPLOn.finset_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {P : Set E}
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPLOn P (f i)) :
    IsPLOn P (fun x => s.inf' hs fun i => f i x) :=
  (IsPLOn.finset_sup' s hs fun i hi => (hf i hi).neg).neg.congr fun x _ =>
    finset_inf'_eq_neg_sup' s hs fun i => f i x

/-- Pull back a finite polytopal complex `CF` covering a target region along a PL map `f : E → F`
defined on `P` to get a finite polytopal complex covering `P ∩ f ⁻¹' CF.space`, on each cell of
which `f` is affine and maps into a single cell of `CF`. -/
theorem IsPLOn.exists_preimage_complex [FiniteDimensional ℝ F] {P : Set E} {f : E → F}
    (hf : IsPLOn P f) (CF : PolytopalComplex F) :
    ∃ D : PolytopalComplex E, D.space = P ∩ f ⁻¹' CF.space ∧
      ∀ S ∈ D.cells, IsAffineOn f S ∧ ∃ R ∈ CF.cells, f '' S ⊆ R := by
  classical
  rcases hf with ⟨CP, hCP, haff⟩
  let aOf : Set E → E →ᵃ[ℝ] F := fun Q =>
    if h : Q ∈ CP.cells then (haff Q h).choose else AffineMap.const ℝ E 0
  have haOf : ∀ Q ∈ CP.cells, Set.EqOn f (aOf Q) Q := fun Q hQ => by
    simp only [aOf, dite_eq_left hQ]
    exact (haff Q hQ).choose_spec
  let ℱ : Set (Set E) :=
    (fun p : Set E × Set F => p.1 ∩ (aOf p.1) ⁻¹' p.2) '' (CP.cells ×ˢ CF.cells)
  have hℱ : ℱ.Finite := (CP.finite_cells.prod CF.finite_cells).image _
  have hpoly : ∀ S ∈ ℱ, IsPolytope S := by
    rintro _ ⟨⟨Q, R⟩, ⟨hQ, hR⟩, rfl⟩
    exact (CP.isPolytope_of_mem hQ).preimage_inter (CF.isPolytope_of_mem hR) (aOf Q)
  let D := PolytopalComplex.ofFinitePolytopes hℱ hpoly
  refine ⟨D, ?_, fun S hS => ?_⟩
  · rw [PolytopalComplex.space_ofFinitePolytopes hℱ hpoly]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Set.mem_prod,
      Prod.exists, exists_prop, ℱ]
    constructor
    · rintro ⟨_, ⟨Q, R, ⟨hQ, hR⟩, rfl⟩, hxQ, haxR⟩
      refine ⟨hCP ▸ CP.subset_space hQ hxQ, ?_⟩
      rw [haOf Q hQ hxQ]
      exact CF.subset_space hR haxR
    · rintro ⟨hxP, hfxCF⟩
      have hxCP : x ∈ CP.space := hCP.symm ▸ hxP
      rw [PolytopalComplex.mem_space_iff] at hxCP hfxCF
      rcases hxCP with ⟨Q, hQ, hxQ⟩
      rcases hfxCF with ⟨R, hR, hfxR⟩
      exact ⟨Q ∩ (aOf Q) ⁻¹' R, ⟨Q, R, ⟨hQ, hR⟩, rfl⟩,
        hxQ, Set.mem_preimage.2 (by rw [← haOf Q hQ hxQ]; exact hfxR)⟩
  · obtain ⟨S₀, hS₀ℱ, hSS₀⟩ := PolytopalComplex.ofFinitePolytopes_cell_subset hℱ hpoly hS
    rcases hS₀ℱ with ⟨⟨Q, R⟩, ⟨hQ, hR⟩, rfl⟩
    have hsubQ : S ⊆ Q := hSS₀.trans inter_subset_left
    have hsubR : S ⊆ (aOf Q) ⁻¹' R := hSS₀.trans inter_subset_right
    refine ⟨(haff Q hQ).mono hsubQ, R, hR, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [haOf Q hQ (hsubQ hx)]
    exact hsubR hx

theorem IsPLOn.comp [FiniteDimensional ℝ F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Set E} {T : Set F} {f : E → F} {g : F → G}
    (hf : IsPLOn P f) (hg : IsPLOn T g) (hmaps : MapsTo f P T) :
    IsPLOn P (g ∘ f) := by
  rcases hg with ⟨CT, hCT, haff_g⟩
  obtain ⟨D, hDsp, hDcell⟩ := hf.exists_preimage_complex CT
  have hsp : D.space = P := by
    rw [hDsp, hCT]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hmaps hx⟩⟩
  refine ⟨D, hsp, fun S hS => ?_⟩
  obtain ⟨haffS, R, hR, hsubR⟩ := hDcell S hS
  exact haffS.comp (haff_g R hR) fun x hx => hsubR (Set.mem_image_of_mem f hx)

omit [FiniteDimensional ℝ E] in
theorem IsPLOn.image_isPolyhedron [FiniteDimensional ℝ F] {P : Set E} {f : E → F}
    (hf : IsPLOn P f) : IsPolyhedron (f '' P) := by
  rcases hf with ⟨C, rfl, haff⟩
  rw [isPolyhedron_iff_finite_union_polytopes]
  refine ⟨(fun Q => f '' Q) '' C.cells, C.finite_cells.image _, ?_, ?_⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    exact (haff Q hQ).image_isPolytope (C.isPolytope_of_mem hQ)
  · ext y
    simp only [Set.mem_image, PolytopalComplex.mem_space_iff, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨Q, hQ, hxQ⟩, rfl⟩
      exact ⟨f '' Q, ⟨Q, hQ, rfl⟩, x, hxQ, rfl⟩
    · rintro ⟨_, ⟨Q, hQ, rfl⟩, x, hxQ, rfl⟩
      exact ⟨x, ⟨Q, hQ, hxQ⟩, rfl⟩

theorem IsPLOn.preimage_inter_isPolyhedron [FiniteDimensional ℝ F] {P : Set E} {Q : Set F}
    {f : E → F} (hf : IsPLOn P f) (hQ : IsPolyhedron Q) : IsPolyhedron (P ∩ f ⁻¹' Q) := by
  obtain ⟨CQ, hCQ⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hQ
  obtain ⟨D, hDsp, _⟩ := hf.exists_preimage_complex CQ
  rw [hCQ] at hDsp
  exact isPolyhedron_iff_exists_polytopalComplex.2 ⟨D, hDsp⟩

/-- Given a PL map `f : E → F` on `P` and a finite polytopal complex `CF` covering `f '' P`, there
is a finite triangulation `KE` of `P` on whose every simplex `f` is affine and maps into a single
cell of `CF`. Cited in issue #4325 notes as `STOC 1056 Lemma B.1(2)` (unverified against the
primary manuscript). -/
theorem exists_triangulation_of_isPLOn_compatible [FiniteDimensional ℝ F] {P : Set E} {f : E → F}
    (hf : IsPLOn P f) (CF : PolytopalComplex F) (hcov : f '' P ⊆ CF.space) :
    ∃ KE : Geometry.SimplicialComplex ℝ E, KE.faces.Finite ∧ KE.space = P ∧
      ∀ s ∈ KE.faces, IsAffineOn f (convexHull ℝ (s : Set E)) ∧
        ∃ R ∈ CF.cells, f '' convexHull ℝ (s : Set E) ⊆ R := by
  obtain ⟨D, hDsp, hDcell⟩ := hf.exists_preimage_complex CF
  refine ⟨D.barycentricSubdivision, D.barycentricSubdivision_faces_finite, ?_, fun s hs => ?_⟩
  · rw [D.barycentricSubdivision_space, hDsp]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hcov (Set.mem_image_of_mem f hx)⟩⟩
  · obtain ⟨S, hSD, hsS⟩ := D.barycentricSubdivision_simplex_subset hs
    obtain ⟨haffS, R, hR, hsubR⟩ := hDcell S hSD
    exact ⟨haffS.mono hsS, R, hR, (Set.image_mono hsS).trans hsubR⟩

end FiniteDim

end Cslib.Polyhedra
