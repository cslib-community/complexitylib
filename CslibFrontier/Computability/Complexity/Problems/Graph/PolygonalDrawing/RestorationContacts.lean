/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationRoutes
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitLayout
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Contacts when attaching split fans to exterior routes

Every contact between an interior spoke and an exterior cut route is its own boundary
port, at the corresponding actual route end. Distinct edge-end occurrences remain
separate, including the two cut ends of a target loop.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- The lifted original end of a retained contracted occurrence has its original name. -/
theorem contractionLift_vertex_contractedIndex (G : Graph) (u v : ℕ)
    (e : Fin G.2.length) (side : Bool) :
    (contractionLift G u v (contractedIndex G u v e, side)).vertex =
      Dart.vertex (G := G) (e, side) := by
  have h := contractionLift_relabelEquiv G u v (e, side)
  change contractionLift G u v (contractedIndex G u v e, side) =
    retainedLastEdgeDart G u v (e, side) at h
  rw [h, vertex_retainedLastEdgeDart]

/-- The automatically separated fans meet only at their own centers, including
the two distinct ends of one target loop. Opposite fan assignments cannot meet. -/
theorem IsEmbedding.split_spoke_contact {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding)
    {ρ : ℝ} (hρ : 0 < ρ) {a b : ℂ}
    (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (f : ℂ →ᵃ[ℝ] ℝ) (hsep : f b < f a)
    (hpa : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val))
    (hpb : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b)
    (d e : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) (hde : d ≠ e)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
        (D.cutPort ρ d.val) s =
      AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v e.val).vertex)
        (D.cutPort ρ e.val) t) : s = 0 ∧ t = 0 := by
  have hsphere (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) :
      D.cutPort ρ d.val ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [d.property] using hD.dist_cutPort hρ.le d.val
  have hports : D.cutPort ρ d.val ≠ D.cutPort ρ e.val := fun h => hde (Subtype.ext
    (hD.cutPort_injective hρ d.val e.val (d.property.trans e.property.symm) h))
  by_cases hdu : (contractionLift G u v d.val).vertex = u
  · by_cases heu : (contractionLift G u v e.val).vertex = u
    · simp only [restoredVertex, ite_eq_left hdu, ite_eq_left heu] at heq
      exact fan_contact ha (hsphere d) (hsphere e) hports hs ht heq
    · have hev := ((contractionLift_vertex_eq_iff G u v e.val).mp e.property).resolve_left heu
      simp only [restoredVertex, ite_eq_left hdu, ite_eq_right heu, ite_eq_left hev] at heq
      exact False.elim (split_spokes_ne f hsep (hpa d hdu) (hpb e hev) hs ht heq)
  · have hdv := ((contractionLift_vertex_eq_iff G u v d.val).mp d.property).resolve_left hdu
    by_cases heu : (contractionLift G u v e.val).vertex = u
    · simp only [restoredVertex, ite_eq_right hdu, ite_eq_left hdv, ite_eq_left heu] at heq
      exact False.elim (split_spokes_ne f hsep (hpa e heu) (hpb d hdv) ht hs heq.symm)
    · have hev := ((contractionLift_vertex_eq_iff G u v e.val).mp e.property).resolve_left heu
      simp only [restoredVertex, ite_eq_right hdu, ite_eq_left hdv,
        ite_eq_right heu, ite_eq_left hev] at heq
      exact fan_contact hb (hsphere d) (hsphere e) hports hs ht heq

/-- A split spoke meets the new connector only at its assigned center and the
corresponding original source endpoint. Every real connector parameter is included. -/
theorem split_spoke_connector_contact {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (f : ℂ →ᵃ[ℝ] ℝ) (hsep : f b < f a)
    (hpa : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val))
    (hpb : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b)
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v})
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
      (D.cutPort ρ d.val) s = AffineMap.lineMap a b t) :
    s = 0 ∧ (((contractionLift G u v d.val).vertex = u ∧ t = 0) ∨
      ((contractionLift G u v d.val).vertex = v ∧ t = 1)) := by
  by_cases hdu : (contractionLift G u v d.val).vertex = u
  · simp only [restoredVertex, ite_eq_left hdu] at heq
    obtain ⟨hs0, ht0⟩ := split_connector_contact f hsep (hpa d hdu) hs ht heq
    exact ⟨hs0, Or.inl ⟨hdu, ht0⟩⟩
  · have hdv := ((contractionLift_vertex_eq_iff G u v d.val).mp d.property).resolve_left hdu
    simp only [restoredVertex, ite_eq_right hdu, ite_eq_left hdv] at heq
    have hsep' : (-f) a < (-f) b := by change -f a < -f b; linarith
    have hport : (-f) b < (-f) (D.cutPort ρ d.val) := by
      change -f b < -f (D.cutPort ρ d.val)
      linarith [hpb d hdv]
    have hrev : AffineMap.lineMap b (D.cutPort ρ d.val) s =
        AffineMap.lineMap b a (1 - t) := by
      rw [AffineMap.lineMap_apply_one_sub]
      exact heq
    obtain ⟨hs0, ht0⟩ := split_connector_contact (-f) hsep' hport hs
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ hrev
    exact ⟨hs0, Or.inr ⟨hdv, by linarith⟩⟩

/-- A split spoke visits a restored source vertex only at its own original end. -/
theorem split_spoke_vertex_contact {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (f : ℂ →ᵃ[ℝ] ℝ) (hsep : f b < f a)
    (hpa : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val))
    (hpb : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b)
    (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v})
    (w : ℕ) (hw : w = u ∨ w = v) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
      (D.cutPort ρ d.val) s = D.restoredVertex a b w) :
    s = 0 ∧ (contractionLift G u v d.val).vertex = w := by
  rcases hw with hwu | hwv
  · have hconn : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
        (D.cutPort ρ d.val) s = AffineMap.lineMap a b (0 : ℝ) := by
      have h := heq.trans (congrArg (D.restoredVertex a b) hwu)
      simpa only [restoredVertex, ↓reduceIte, AffineMap.lineMap_apply_zero] using h
    obtain ⟨hs0, hu | hv⟩ := D.split_spoke_connector_contact ρ a b f hsep hpa hpb d hs
      ⟨le_rfl, by norm_num⟩ hconn
    · exact ⟨hs0, hu.1.trans hwu.symm⟩
    · norm_num at hv
  · have hconn : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
        (D.cutPort ρ d.val) s = AffineMap.lineMap a b (1 : ℝ) := by
      have h := heq.trans (congrArg (D.restoredVertex a b) hwv)
      simpa only [restoredVertex, ite_eq_right huv.symm, ↓reduceIte,
        AffineMap.lineMap_apply_one] using h
    obtain ⟨hs0, hu | hv⟩ := D.split_spoke_connector_contact ρ a b f hsep hpa hpb d hs
      ⟨by norm_num, le_rfl⟩ hconn
    · norm_num at hu
    · exact ⟨hs0, hv.1.trans hwv.symm⟩

/-- An interior spoke can meet an exterior route only at its own cut port and
corresponding actual end. The radius's exterior-contact property is supplied by
`IsEmbedding.exists_restriction`, rather than by a geometric drawing provider. -/
theorem IsEmbedding.spoke_outsideRoute_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {a : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ)
    (d : Dart G) (hd : d.vertex = v) (e : Fin G.2.length)
    (i : Fin (D.outsideRoute v ρ e).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap a (D.cutPort ρ d) s = (D.outsideRoute v ρ e).eval i t) :
    s = 1 ∧ ∃ side, d = (e, side) ∧ (D.outsideRoute v ρ e).AtEnd i t side := by
  have hsphere (d : Dart G) (hd : d.vertex = v) :
      D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [hd] using hD.dist_cutPort hρ.le d
  have hball : AffineMap.lineMap a (D.cutPort ρ d) s ∈ Metric.closedBall (D.vertex v) ρ :=
    (convex_closedBall (D.vertex v) ρ).lineMap_mem (Metric.ball_subset_closedBall ha)
      (Metric.sphere_subset_closedBall (hsphere d hd)) hs
  obtain ⟨side, hat, hvertex, hpoint⟩ := hcut e i t ht (heq ▸ hball)
  have hboundary : AffineMap.lineMap a (D.cutPort ρ d) s ∈
      Metric.sphere (D.vertex v) ρ := (heq.trans hpoint).symm ▸ hsphere (e, side) hvertex
  have hs1 := lineMap_sphere_parameter ha (hsphere d hd) hs hboundary
  have hports : D.cutPort ρ d = D.cutPort ρ (e, side) := by
    simpa only [hs1, AffineMap.lineMap_apply_one] using heq.trans hpoint
  exact ⟨hs1, side, hD.cutPort_injective hρ d (e, side) (hd.trans hvertex.symm) hports, hat⟩

/-- The exterior restriction is disjoint from the open replacement ball. -/
theorem IsEmbedding.outsideRoute_not_mem_ball {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    (e : Fin G.2.length) (i : Fin (D.outsideRoute v ρ e).segments) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : (D.outsideRoute v ρ e).eval i t ∉ Metric.ball (D.vertex v) ρ := by
  intro hin
  obtain ⟨side, _, hv, hp⟩ := hcut e i t ht (Metric.ball_subset_closedBall hin)
  have hdist := hD.dist_cutPort hρ.le (e, side)
  rw [hv, ← hp] at hdist
  exact (ne_of_lt hin) hdist

/-- An exterior route cannot contain the old center of its replacement circle. -/
theorem outsideRoute_ne_center_of_contacts {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hports : ∀ d : Dart G, d.vertex = v → dist (D.cutPort ρ d) (D.vertex v) = ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    (e : Fin G.2.length) (i : Fin (D.outsideRoute v ρ e).segments) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : (D.outsideRoute v ρ e).eval i t ≠ D.vertex v := by
  intro heq
  have hball : (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ := by
    rw [heq]
    exact Metric.mem_closedBall_self hρ.le
  obtain ⟨side, _, hv, hp⟩ := hcut e i t ht hball
  have hdist := hports (e, side) hv
  rw [← hp, heq, dist_self] at hdist
  exact hρ.ne hdist

/-- Contacts of two different exterior pieces are inherited from old common ends.
Both real parameters are transported through the independent cut maps. -/
theorem IsEmbedding.outsideRoute_edge_contacts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (e f : Fin G.2.length) (hef : e ≠ f)
    (i : Fin (D.outsideRoute v ρ e).segments) (j : Fin (D.outsideRoute v ρ f).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (D.outsideRoute v ρ e).eval i s = (D.outsideRoute v ρ f).eval j t) :
    ∃ side tag, (D.outsideRoute v ρ e).AtEnd i s side ∧
      (D.outsideRoute v ρ f).AtEnd j t tag ∧ Dart.vertex (e, side) = Dart.vertex (f, tag) := by
  let lo (e : Fin G.2.length) := D.restrictionTime v ρ (e, false)
  let hi (e : Fin G.2.length) := D.restrictionTime v ρ (e, true)
  have hbounds (e : Fin G.2.length) : 0 ≤ lo e ∧ 0 ≤ hi e ∧ lo e + hi e < 1 :=
    hD.restrictionTime_bounds v hρ hlen e
  change Fin (D.route e).segments at i
  change Fin (D.route f).segments at j
  let σ := (D.route e).cutTime (lo e) (hi e) i s
  let τ := (D.route f).cutTime (lo f) (hi f) j t
  have hσ := (D.route e).cutTime_mem (hbounds e).1 (hbounds e).2.1 (hbounds e).2.2 i hs
  have hτ := (D.route f).cutTime_mem (hbounds f).1 (hbounds f).2.1 (hbounds f).2.2 j ht
  have heval : (D.route e).eval i σ = (D.route f).eval j τ :=
    ((D.route e).eval_cutEnds (lo e) (hi e) i s).symm.trans
      (heq.trans ((D.route f).eval_cutEnds (lo f) (hi f) j t))
  obtain ⟨side, tag, hside, htag, hv⟩ := hD.edge_contacts e f hef i j σ τ hσ hτ heval
  exact ⟨side, tag,
    Route.atEnd_cutEnds_of_atEnd (hbounds e).1 (hbounds e).2.1 (hbounds e).2.2 i hs side hside,
    Route.atEnd_cutEnds_of_atEnd (hbounds f).1 (hbounds f).2.1 (hbounds f).2.2 j ht tag htag, hv⟩

/-- A declared old vertex on an exterior piece remains at its own unchanged original
end. The two independent cut maps preserve its endpoint occurrence. -/
theorem IsEmbedding.outsideRoute_vertex_contacts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (e : Fin G.2.length) (i : Fin (D.outsideRoute v ρ e).segments) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) (w : ℕ) (hw : w ∈ G.1)
    (heq : (D.outsideRoute v ρ e).eval i t = D.vertex w) :
    ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = w := by
  let lo := D.restrictionTime v ρ (e, false)
  let hi := D.restrictionTime v ρ (e, true)
  obtain ⟨hlo, hhi, hsum⟩ := hD.restrictionTime_bounds v hρ hlen e
  change Fin (D.route e).segments at i
  let τ := (D.route e).cutTime lo hi i t
  have hτ := (D.route e).cutTime_mem hlo hhi hsum i ht
  have heval : (D.route e).eval i τ = D.vertex w :=
    ((D.route e).eval_cutEnds lo hi i t).symm.trans heq
  obtain ⟨side, hside, hv⟩ := hD.vertex_contacts e i τ hτ w hw heval
  exact ⟨side, Route.atEnd_cutEnds_of_atEnd hlo hhi hsum i ht side hside, hv⟩

/-- Attach a new first spoke to an actual exterior piece, preserving full continuous
simplicity. Its only contact with that piece is the intended first cut port. -/
theorem IsEmbedding.prepend_outsideRoute_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {a : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (e : Fin G.2.length)
    (he : Dart.vertex (e, false) = v) (hp : (D.outsideRoute v ρ e).IsSimple) :
    (Route.prepend a (D.outsideRoute v ρ e)).IsSimple := by
  have hstart : (D.outsideRoute v ρ e).start = D.cutPort ρ (e, false) := by
    simpa only [he, ↓reduceIte, Route.endpoint, Bool.false_eq_true] using
      D.endpoint_outsideRoute v ρ e false
  have hsphere : D.cutPort ρ (e, false) ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [he] using hD.dist_cutPort hρ.le (e, false)
  apply hp.prepend
  · rw [hstart]
    intro heq
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hsphere (heq ▸ ha)
  · intro j s t hs ht heq
    rw [hstart] at heq
    obtain ⟨hs1, side, hside, hat⟩ :=
      hD.spoke_outsideRoute_contact v hρ hcut ha (e, false) he e j hs ht heq
    have htag : side = false := (congrArg Prod.snd hside).symm
    subst side
    exact Or.inl ⟨hs1, hat⟩

/-- Attach a new last spoke to an actual exterior piece. The old first end, if
unmodified, is retained exactly. -/
theorem IsEmbedding.append_outsideRoute_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {b : ℂ} (hb : b ∈ Metric.ball (D.vertex v) ρ) (e : Fin G.2.length)
    (he : Dart.vertex (e, true) = v) (hp : (D.outsideRoute v ρ e).IsSimple) :
    ((D.outsideRoute v ρ e).append b).IsSimple := by
  have hfinish : (D.outsideRoute v ρ e).finish = D.cutPort ρ (e, true) := by
    simpa only [he, ↓reduceIte, Route.endpoint] using D.endpoint_outsideRoute v ρ e true
  have hsphere : D.cutPort ρ (e, true) ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [he] using hD.dist_cutPort hρ.le (e, true)
  apply hp.append
  · rw [hfinish]
    intro heq
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hsphere (heq.symm ▸ hb)
  · intro j s t hs ht heq
    have hrev : AffineMap.lineMap b (D.cutPort ρ (e, true)) (1 - t) =
        (D.outsideRoute v ρ e).eval j s := by
      rw [AffineMap.lineMap_apply_one_sub, ← hfinish]
      exact heq.symm
    obtain ⟨ht1, side, hside, hat⟩ := hD.spoke_outsideRoute_contact v hρ hcut hb
      (e, true) he e j ⟨by linarith [ht.2], by linarith [ht.1]⟩ hs hrev
    have htag : side = true := (congrArg Prod.snd hside).symm
    subst side
    exact Or.inl ⟨hat, by linarith⟩

/-- Reattach two independent ends of a cut route, permitting precisely the intended
new loop closure. The spoke-contact premise is discharged by the internally constructed
same-center fan or separated two-fan geometry, including reopened target loops. -/
theorem IsEmbedding.attach_outsideRoute_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (e : Fin G.2.length) (he₀ : Dart.vertex (e, false) = v) (he₁ : Dart.vertex (e, true) = v)
    (hp : (D.outsideRoute v ρ e).IsSimple)
    (hspokes : ∀ s t : ℝ, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a (D.cutPort ρ (e, false)) s =
        AffineMap.lineMap b (D.cutPort ρ (e, true)) t → s = 0 ∧ t = 0) :
    ((Route.prepend a (D.outsideRoute v ρ e)).append b).IsSimple := by
  let p := D.outsideRoute v ρ e
  have hstart : p.start = D.cutPort ρ (e, false) := by
    simpa only [he₀, ↓reduceIte, Route.endpoint, Bool.false_eq_true] using
      D.endpoint_outsideRoute v ρ e false
  have hfinish : p.finish = D.cutPort ρ (e, true) := by
    simpa only [he₁, ↓reduceIte, Route.endpoint] using D.endpoint_outsideRoute v ρ e true
  have hfinish' : (Route.prepend a p).finish = D.cutPort ρ (e, true) :=
    (Route.endpoint_prepend a p true).trans hfinish
  have hsphere : D.cutPort ρ (e, true) ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [he₁] using hD.dist_cutPort hρ.le (e, true)
  have hp' : (Route.prepend a p).IsSimple :=
    hD.prepend_outsideRoute_simple v hρ hcut ha e he₀ hp
  apply hp'.append
  · rw [hfinish']
    intro heq
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hsphere (heq.symm ▸ hb)
  · intro j s t hs ht heq
    induction j using Fin.cases with
    | zero =>
      rw [Route.eval_prepend_zero, hstart, hfinish'] at heq
      have hrev : AffineMap.lineMap a (D.cutPort ρ (e, false)) s =
          AffineMap.lineMap b (D.cutPort ρ (e, true)) (1 - t) := by
        rw [AffineMap.lineMap_apply_one_sub]
        exact heq
      obtain ⟨hs0, ht0⟩ := hspokes s (1 - t) hs ⟨by linarith [ht.2], by linarith [ht.1]⟩ hrev
      right
      refine ⟨?_, by linarith⟩
      simp [Route.AtEnd, Route.position, hs0]
    | succ j =>
      change Fin p.segments at j
      have heq' : p.eval j s = AffineMap.lineMap (Route.prepend a p).finish b t :=
        (Route.eval_prepend_succ a p j s).symm.trans heq
      rw [hfinish'] at heq'
      have hrev : AffineMap.lineMap b (D.cutPort ρ (e, true)) (1 - t) = p.eval j s := by
        rw [AffineMap.lineMap_apply_one_sub]
        exact heq'.symm
      obtain ⟨ht1, side, hside, hat⟩ := hD.spoke_outsideRoute_contact v hρ hcut hb
        (e, true) he₁ e j ⟨by linarith [ht.2], by linarith [ht.1]⟩ hs hrev
      have htag : side = true := (congrArg Prod.snd hside).symm
      subst side
      left
      refine ⟨?_, by linarith⟩
      change (Route.prepend a p).position j.succ s = (Route.prepend a p).segments
      calc
        _ = 1 + p.position j s := Route.position_prepend_succ a p j s
        _ = _ := by
          rw [show p.position j s = p.segments from hat, Route.segments_prepend]
          push_cast
          ring

end Cslib.Complexity.Graph.PolygonalDrawing
