/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace
public import Complexity.Foundations.Geometry.Polygonal.RayParityDirection
public import Complexity.Foundations.Geometry.Polygonal.RayParityEven
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ray parity on the actual segments of a polygonal drawing

Vertex-even edge labels induce even incidence at every actual segment endpoint: internal
bends cancel in pairs and the original endpoints sum to `Graph.vertexParity`. A single
complex rotation and positive scaling makes every nondegenerate segment nonhorizontal.
The generic finite-arrangement theorem then makes the selected ray parity locally constant
off its actual support, including all endpoint heights and arbitrary coincident bends.

These are original finite calculations. Local constancy alone does not identify the
right-side samples of a rotation's face successor, and no colors on `RotationSystem.Face`
or numerical-genus converse are asserted here.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

variable {G : Graph} (D : PolygonalDrawing G)

/-- An actual listed segment, retaining its edge occurrence and its position on that route. -/
abbrev SegmentIndex := (e : Fin G.2.length) × Fin (D.route e).segments

/-- First listed point of an actual segment. -/
@[expose] def segmentStart (s : D.SegmentIndex) : ℂ := (D.route s.1).point s.2.castSucc

/-- Second listed point of an actual segment. -/
@[expose] def segmentFinish (s : D.SegmentIndex) : ℂ := (D.route s.1).point s.2.succ

/-- Even incidence on original indexed darts remains even on all actual segment endpoints.
Both loop ends and repeated edge occurrences are retained. Internal bends contribute twice,
including when different listed bends have coincident coordinates. No endpoint-declaration,
simplicity, connectedness, degree or coordinate assumption is needed for this identity. -/
theorem segment_endpoints_even (x : Fin G.2.length → Bool) (hx : G.VertexEven x)
    (u p : ℂ) :
    (∑ s : D.SegmentIndex, ((if u * D.segmentStart s = p then x s.1 else 0) +
      (if u * D.segmentFinish s = p then x s.1 else 0))) = false := by
  classical
  have hroute (e : Fin G.2.length) :
      (∑ i : Fin (D.route e).segments,
        ((if u * (D.route e).point i.castSucc = p then x e else 0) +
          (if u * (D.route e).point i.succ = p then x e else 0))) =
        (if u * (D.route e).start = p then x e else 0) +
          (if u * (D.route e).finish = p then x e else 0) := by
    let f (i : Fin ((D.route e).segments + 1)) : Bool :=
      if u * (D.route e).point i = p then x e else 0
    have hlast := Fin.sum_univ_castSucc f
    have hfirst := Fin.sum_univ_succ f
    change (∑ i : Fin (D.route e).segments, (f i.castSucc + f i.succ)) =
      f 0 + f (Fin.last (D.route e).segments)
    rw [Finset.sum_add_distrib,
      eq_sub_iff_add_eq.mpr hlast.symm,
      eq_sub_iff_add_eq'.mpr hfirst.symm]
    simp only [sub_eq_add_neg, BooleanRing.neg_eq]
    calc
      _ = ((∑ i, f i) + ∑ i, f i) +
          (f 0 + f (Fin.last (D.route e).segments)) := by ac_rfl
      _ = _ := by rw [BooleanRing.add_self, zero_add]
  rw [Fintype.sum_sigma]
  change (∑ e, ∑ i : Fin (D.route e).segments,
    ((if u * (D.route e).point i.castSucc = p then x e else 0) +
      (if u * (D.route e).point i.succ = p then x e else 0))) = false
  simp only [hroute]
  have hends (e : Fin G.2.length) :
      (if u * (D.route e).start = p then x e else 0) +
        (if u * (D.route e).finish = p then x e else 0) =
      (∑ b : Bool, if u * D.vertex (Dart.vertex (e, b)) = p then x e else 0) := by
    rw [Fintype.sum_bool]
    rw [show (D.route e).start = D.vertex (Dart.vertex (e, false)) from D.endpoint_eq e false,
      show (D.route e).finish = D.vertex (Dart.vertex (e, true)) from D.endpoint_eq e true]
    exact add_comm _ _
  simp only [hends]
  rw [← Fintype.sum_prod_type (fun d : Dart G =>
    if u * D.vertex d.vertex = p then x d.1 else 0)]
  let s := Finset.univ.image (Dart.vertex (G := G))
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s)
    (g := Dart.vertex) (fun d _ => Finset.mem_image_of_mem _ (Finset.mem_univ d))
    (fun d : Dart G => if u * D.vertex d.vertex = p then x d.1 else 0)]
  apply Finset.sum_eq_zero
  intro v _
  rw [Finset.sum_filter]
  by_cases hv : u * D.vertex v = p
  · have hterms (d : Dart G) :
        (if d.vertex = v then (if u * D.vertex d.vertex = p then x d.1 else 0) else 0) =
          if d.vertex = v then x d.1 else 0 := by
      split_ifs with hd <;> simp_all
    simp only [hterms]
    exact hx v
  · apply Finset.sum_eq_zero
    intro d _
    by_cases hd : d.vertex = v
    · rw [ite_eq_left hd, hd, ite_eq_right hv]
    · rw [ite_eq_right hd]

/-- A genuine polygonal embedding admits a single ray direction for which every even edge
label gives locally constant parity on the complement of its selected actual segments.
The multiplier is chosen from the drawing alone, before the edge label or observation point.
This is a local geometric theorem, not yet transport along the right side of a face walk. -/
theorem IsEmbedding.exists_rayParity_locally_constant {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ x : Fin G.2.length → Bool, G.VertexEven x →
      ∀ z : ℂ, (∀ s : D.SegmentIndex, x s.1 = true →
        z ∉ segment ℝ (u * D.segmentStart s) (u * D.segmentFinish s)) →
      ∀ᶠ w in nhds z,
        Polygonal.rayParity (fun s => u * D.segmentStart s)
          (fun s => u * D.segmentFinish s) (fun s => x s.1) w =
        Polygonal.rayParity (fun s => u * D.segmentStart s)
          (fun s => u * D.segmentFinish s) (fun s => x s.1) z := by
  classical
  let s := Finset.univ.image D.segmentStart ∪ Finset.univ.image D.segmentFinish
  obtain ⟨u, hu, hinj⟩ := Polygonal.exists_mul_im_injOn s
  refine ⟨u, hu, fun x hx z hz => ?_⟩
  apply Polygonal.eventually_rayParity_eq_of_even
  · intro i heq
    exact (hD.simple i.1).segment_ne i.2 (hinj
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) heq)
  · exact D.segment_endpoints_even x hx u
  · exact hz

end Cslib.Complexity.Graph.PolygonalDrawing
