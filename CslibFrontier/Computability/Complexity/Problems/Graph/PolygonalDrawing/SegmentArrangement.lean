/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColorsRayParity
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityColors
public import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
public import CslibFrontier.Foundations.Geometry.Polygonal.SegmentRays

/-!
# The segment arrangement underlying a polygonal embedding

The interior of each actual listed segment is disjoint from every other segment
occurrence. Consecutive bends may coincide only as the shared endpoints allowed by
the route parameter, and the two original ends of a loop remain distinct.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- Distinct indexed segments in an embedding cannot meet in the open interior
of either segment. The statement includes different segments on the same loop route. -/
theorem IsEmbedding.segment_interior_disjoint {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (s j : D.SegmentIndex) (hne : j ≠ s)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap (D.segmentStart s) (D.segmentFinish s) t ∉
      segment ℝ (D.segmentStart j) (D.segmentFinish j) := by
  rw [segment_eq_image_lineMap]
  rintro ⟨u, hu, heq⟩
  have hpoint : (D.route s.1).eval s.2 t = (D.route j.1).eval j.2 u := heq.symm
  by_cases hedge : s.1 = j.1
  · rcases s with ⟨e, i⟩
    rcases j with ⟨f, k⟩
    change e = f at hedge
    subst f
    obtain hpos | ⟨hstart, -⟩ | ⟨hfinish, -⟩ :=
      hD.simple e i k t u ⟨ht.1.le, ht.2.le⟩ hu hpoint
    · have hik : i = k := by
        apply Fin.ext
        rcases lt_trichotomy i.val k.val with h | h | h
        · have hik : (i.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
          dsimp [Route.position] at hpos
          linarith [ht.2, hu.1]
        · exact h
        · have hki : (k.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
          dsimp [Route.position] at hpos
          linarith [ht.1, hu.2]
      exact hne (by subst k; rfl)
    · exact Route.not_atEnd_of_mem_Ioo _ _ ht false hstart
    · exact Route.not_atEnd_of_mem_Ioo _ _ ht true hfinish
  · obtain ⟨tag, _, hs, _, _⟩ := hD.edge_contacts s.1 j.1 hedge _ _ _ _
      ⟨ht.1.le, ht.2.le⟩ hu hpoint
    exact Route.not_atEnd_of_mem_Ioo _ _ ht tag hs

/-- At any listed segment endpoint, another segment can contain the point only
as one of its own endpoints. This uses the actual continuum of each segment. -/
theorem IsEmbedding.segment_endpoint_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (k : D.SegmentIndex × Bool) (j : D.SegmentIndex)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k ∈
      segment ℝ (D.segmentStart j) (D.segmentFinish j)) :
    D.segmentStart j = rayEndpoint D.segmentStart D.segmentFinish k ∨
      D.segmentFinish j = rayEndpoint D.segmentStart D.segmentFinish k := by
  classical
  rcases k with ⟨s, tag⟩
  by_cases hj : j = s
  · subst j
    cases tag <;> simp [rayEndpoint]
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, heq⟩ := hp
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · left
    simpa only [← ht0, AffineMap.lineMap_apply_zero] using heq
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · right
    simpa only [ht1, AffineMap.lineMap_apply_one] using heq
  have hp' : AffineMap.lineMap (D.segmentStart j) (D.segmentFinish j) t ∈
      segment ℝ (D.segmentStart s) (D.segmentFinish s) := by
    rw [heq]
    cases tag <;> simp only [rayEndpoint, Bool.false_eq_true, ↓reduceIte]
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  exact (hD.segment_interior_disjoint j s (Ne.symm hj) t ⟨ht0, ht1⟩ hp').elim

/-- The actual point of a segment-end occurrence is its affine endpoint parameter. -/
theorem segment_endpoint_eq_eval {G : Graph} (D : PolygonalDrawing G)
    (s : D.SegmentIndex) (tag : Bool) :
    rayEndpoint D.segmentStart D.segmentFinish (s, tag) =
      (D.route s.1).eval s.2 (if tag then 1 else 0) := by
  rcases s with ⟨e, i⟩
  cases tag <;> simp [rayEndpoint, segmentStart, segmentFinish, Route.eval]

/-- At an internal bend, the only incident segment ends are the two consecutive
occurrences of its route. This includes bends of closed loop routes. -/
theorem IsEmbedding.segment_ends_at_bend {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (e : Fin G.2.length) (i : Fin (D.route e).bends)
    (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k =
      (D.route e).point i.castSucc.succ) :
    k = (⟨e, i.castSucc⟩, true) ∨ k = (⟨e, i.succ⟩, false) := by
  rcases k with ⟨⟨f, j⟩, tag⟩
  have htime : (if tag then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    cases tag <;> simp
  have hpoint : (D.route e).eval i.castSucc 1 =
      (D.route f).eval j (if tag then 1 else 0) := by
    rw [← D.segment_endpoint_eq_eval ⟨f, j⟩ tag]
    simpa only [Route.eval, AffineMap.lineMap_apply_one] using hp.symm
  have hnot (b : Bool) : ¬(D.route e).AtEnd i.castSucc 1 b := by
    have hi : (i.val : ℝ) + 1 < (D.route e).segments := by
      have := i.isLt
      exact_mod_cast Nat.add_lt_add_right this 1
    have hlo : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    cases b <;> simp only [Route.AtEnd, Route.position, Fin.val_castSucc,
      Bool.false_eq_true, ↓reduceIte] <;> linarith
  by_cases hedge : e = f
  · subst f
    obtain hpos | ⟨hstart, -⟩ | ⟨hfinish, -⟩ :=
      hD.simple e _ _ _ _ (by simp) htime hpoint
    · cases tag
      · right
        have hj : j = i.succ := by
          apply Fin.ext
          dsimp [Route.position] at hpos
          simp only [add_zero] at hpos
          have hnat : j.val = i.val + 1 := by exact_mod_cast hpos.symm
          exact hnat
        subst j
        rfl
      · left
        have hj : j = i.castSucc := by
          apply Fin.ext
          dsimp [Route.position] at hpos
          exact_mod_cast (add_right_cancel hpos).symm
        subst j
        rfl
    · exact (hnot false hstart).elim
    · exact (hnot true hfinish).elim
  · obtain ⟨b, _, hb, _, _⟩ := hD.edge_contacts e f hedge _ _ _ _
      (by simp) htime hpoint
    exact (hnot b hb).elim

/-- The segment-end occurrence corresponding to one actual graph dart. -/
@[expose] def segmentEnd {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    D.SegmentIndex × Bool := (⟨d.1, (D.route d.1).endSegment d.2⟩, d.2)

/-- Distinct graph darts retain distinct indexed segment ends, including loop ends. -/
theorem segmentEnd_injective {G : Graph} (D : PolygonalDrawing G) :
    Function.Injective D.segmentEnd := by
  intro a b h
  exact congrArg (fun k : D.SegmentIndex × Bool => (k.1.1, k.2)) h

/-- The segment-end point of a dart is its actual named vertex. -/
theorem segmentEnd_endpoint {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    rayEndpoint D.segmentStart D.segmentFinish (D.segmentEnd d) = D.vertex d.vertex := by
  rw [← D.endpoint_eq d.1 d.2]
  rcases d with ⟨e, tag⟩
  cases tag <;> simp [segmentEnd, rayEndpoint, segmentStart, segmentFinish,
    Route.endSegment, Route.endpoint, Route.start, Route.finish]

/-- The outgoing vector at a dart's segment end is its actual drawing germ. -/
theorem segmentEnd_vector {G : Graph} (D : PolygonalDrawing G) (d : Dart G) :
    rayEndVector D.segmentStart D.segmentFinish (D.segmentEnd d) = D.germ d := by
  rcases d with ⟨e, tag⟩
  cases tag <;> simp [segmentEnd, rayEndVector, segmentStart, segmentFinish,
    Route.endSegment, germ, Route.germ, Route.start, Route.finish]

/-- Every segment end at a declared vertex is an actual original graph dart there.
Internal bends cannot be mistaken for vertex incidences. -/
theorem IsEmbedding.segment_end_at_vertex {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) (k : D.SegmentIndex × Bool)
    (hp : rayEndpoint D.segmentStart D.segmentFinish k = D.vertex v) :
    ∃ d : Dart G, d.vertex = v ∧ D.segmentEnd d = k := by
  rcases k with ⟨⟨e, i⟩, tag⟩
  rw [D.segment_endpoint_eq_eval] at hp
  have ht : (if tag then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    cases tag <;> simp
  obtain ⟨b, hb, hvertex⟩ := hD.vertex_contacts e i _ ht v hv hp
  refine ⟨(e, b), hvertex, ?_⟩
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ (D.route e).segments := by exact_mod_cast i.isLt
  cases b <;> cases tag <;>
    simp only [Route.AtEnd, Route.position, Bool.false_eq_true, ↓reduceIte] at hb
  · have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hreal : (i.val : ℝ) = 0 := by linarith
      exact_mod_cast hreal
    subst i
    rfl
  · exfalso
    linarith
  · exfalso
    linarith
  · have hi : i = Fin.last (D.route e).bends := by
      apply Fin.ext
      have hreal : (i.val : ℝ) = (D.route e).bends := by
        dsimp [Route.segments] at hb
        push_cast at hb
        linarith
      exact_mod_cast hreal
    subst i
    rfl

end Cslib.Complexity.Graph.PolygonalDrawing
