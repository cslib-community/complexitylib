/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Neighborhood
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitRestriction

/-!
# Closed neighborhoods and cut ports of polygonal embeddings

A declared vertex has a positive closed neighborhood avoiding every other declared point
and every nonincident segment. Its radius is smaller than one third of every incident end
segment. This includes both separate ends of a loop and imposes no shape on the drawing.

The cut ports are actual real affine points on those end segments, at a common distance
from the vertex. They are distinct for distinct incident darts. These are preparation
lemmas for local replacement, not a vertex-splitting or general realization theorem.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- A sufficiently small closed ball isolates the straight star of a declared vertex,
avoids the other declared points, and cuts every incident segment before its first third.
Repeated vertex declarations and arbitrary natural vertex names are allowed. -/
theorem IsEmbedding.exists_restriction_radius {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) :
    ∃ ρ > 0,
      (∀ w ∈ G.1, D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v) ∧
      (∀ e (i : Fin (D.route e).segments) z,
        z ∈ Metric.closedBall (D.vertex v) ρ →
        z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
          (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
          (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v)) ∧
      (∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) := by
  classical
  obtain ⟨ε, hε, hseg⟩ := hD.exists_vertex_ball v hv
  let K : Set ℂ := D.vertex '' {w | w ∈ G.1 ∧ w ≠ v}
  have hfinite : Set.Finite {w | w ∈ G.1 ∧ w ≠ v} :=
    G.1.finite_toSet.subset (fun _ h => h.1)
  have hK : IsClosed K := (hfinite.image D.vertex).isClosed
  have hvK : D.vertex v ∈ Kᶜ := by
    rintro ⟨w, ⟨hw, hne⟩, heq⟩
    exact hne (hD.vertices_injective hw hv heq)
  obtain ⟨δ, hδ, hpoint⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hvK
  let lengths : Finset ℝ := insert 1
    (Finset.univ.image fun d : Dart G => if d.vertex = v then ‖D.germ d‖ else 1)
  have hnonempty : lengths.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let m := lengths.min' hnonempty
  have hm : 0 < m := by
    dsimp [m]
    have hmem := lengths.min'_mem hnonempty
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]
      norm_num
    · obtain ⟨d, _, hd⟩ := Finset.mem_image.mp h
      rw [← hd]
      split_ifs
      · exact norm_pos_iff.mpr (hD.germ_ne_zero d)
      · norm_num
  have hmd (d : Dart G) (hd : d.vertex = v) : m ≤ ‖D.germ d‖ := by
    apply Finset.min'_le
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, by rw [ite_eq_left hd]⟩
  let ρ := min ε (min δ (m / 3)) / 2
  have hρ : 0 < ρ := div_pos (lt_min hε (lt_min hδ (by positivity))) (by norm_num)
  have hρε : ρ < ε := by
    have h := min_le_left ε (min δ (m / 3))
    dsimp [ρ]
    linarith
  have hρδ : ρ < δ := by
    have h := (min_le_right ε (min δ (m / 3))).trans (min_le_left δ (m / 3))
    dsimp [ρ]
    linarith
  have hρm : 3 * ρ < m := by
    have h := (min_le_right ε (min δ (m / 3))).trans (min_le_right δ (m / 3))
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ, ?_, ?_, fun d hd => hρm.trans_le (hmd d hd)⟩
  · intro w hw hdist
    by_contra hne
    exact hpoint (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hdist).trans_lt hρδ))
      ⟨w, ⟨hw, hne⟩, rfl⟩
  · intro e i z hz hzi
    exact hseg e i z
      (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hρε)) hzi

/-- The cut port on an actual outgoing end segment, with no chosen angular coordinates. -/
@[expose] noncomputable def cutPort {G : Graph} (D : PolygonalDrawing G)
    (ρ : ℝ) (d : Dart G) : ℂ :=
  D.vertex d.vertex + (ρ / ‖D.germ d‖) • D.germ d

/-- The common-radius cut port lies at precisely that distance from its own vertex. -/
theorem IsEmbedding.dist_cutPort {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G) :
    dist (D.cutPort ρ d) (D.vertex d.vertex) = ρ := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  rw [cutPort, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hρ hn.le), div_mul_cancel₀ _ (ne_of_gt hn)]

/-- Cutting before the end of the first outgoing segment is an actual segment parameter,
including the reversed final segment at the second end of an edge or loop. -/
theorem cutPort_eq_eval {G : Graph} (D : PolygonalDrawing G) (ρ : ℝ) (d : Dart G) :
    D.cutPort ρ d = (D.route d.1).eval ((D.route d.1).endSegment d.2)
      (Route.endTime d.2 (ρ / ‖D.germ d‖)) := by
  rw [Route.eval_near_end, D.endpoint_eq]
  rfl

/-- A cut strictly shorter than its outgoing segment is on that original route. -/
theorem IsEmbedding.cutPort_mem_support {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : Dart G)
    (hd : ρ ≤ ‖D.germ d‖) : D.cutPort ρ d ∈ (D.route d.1).support := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  rw [D.cutPort_eq_eval]
  apply Route.at_mem_support
  exact Route.endTime_mem _ ⟨div_nonneg hρ hn.le, (div_le_one hn).mpr hd⟩

/-- The cut operation preserves the actual outgoing ray in the fixed plane. -/
theorem IsEmbedding.arg_cutPort_sub {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 < ρ) (d : Dart G) :
    (D.cutPort ρ d - D.vertex d.vertex).arg = (D.germ d).arg := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  rw [cutPort, add_sub_cancel_left, Complex.real_smul, Complex.arg_real_mul _ (div_pos hρ hn)]

/-- Distinct actual darts at one vertex yield distinct common-radius boundary ports.
The two ends of the same loop are included. -/
theorem IsEmbedding.cutPort_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {ρ : ℝ} (hρ : 0 < ρ) (a b : Dart G)
    (hv : a.vertex = b.vertex) (heq : D.cutPort ρ a = D.cutPort ρ b) : a = b := by
  apply hD.directions_injective a b hv
  have heq' : D.cutPort ρ a - D.vertex a.vertex =
      D.cutPort ρ b - D.vertex b.vertex := by rw [heq, hv]
  have harg := congrArg Complex.arg heq'
  rw [hD.arg_cutPort_sub hρ, hD.arg_cutPort_sub hρ] at harg
  exact congrArg (fun x : ℝ => (x : Real.Angle)) harg

/-- Cut an end precisely when it belongs to the vertex being replaced. The other end
of an edge stays unchanged; the two ends of a loop are cut separately. -/
@[expose] noncomputable def restrictionTime {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (d : Dart G) : ℝ :=
  if d.vertex = v then ρ / ‖D.germ d‖ else 0

/-- The exterior part of an edge after cutting at a named vertex. This is route data,
not a drawing of a graph with invented port vertices. -/
@[expose] noncomputable def outsideRoute {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (e : Fin G.2.length) : Route :=
  (D.route e).cutEnds (D.restrictionTime v ρ (e, false))
    (D.restrictionTime v ρ (e, true))

/-- A restriction radius gives independent small nonnegative cuts at every edge end. -/
theorem IsEmbedding.restrictionTime_mem {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (d : Dart G) :
    D.restrictionTime v ρ d ∈ Set.Ico 0 (1 / 3 : ℝ) := by
  have hn : 0 < ‖D.germ d‖ := norm_pos_iff.mpr (hD.germ_ne_zero d)
  dsimp [restrictionTime]
  split_ifs with hd
  · refine ⟨div_nonneg hρ.le hn.le, ?_⟩
    rw [div_lt_iff₀ hn]
    linarith [hlen d hd]
  · constructor <;> norm_num

/-- The two ends of the exterior piece are their respective cut ports or unchanged
original endpoints, according to actual incidence with the named vertex. -/
theorem endpoint_outsideRoute {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (e : Fin G.2.length) (b : Bool) :
    (D.outsideRoute v ρ e).endpoint b =
      if Dart.vertex (e, b) = v then D.cutPort ρ (e, b) else D.vertex (Dart.vertex (e, b)) := by
  rw [outsideRoute, Route.endpoint_cutEnds]
  cases b <;> rw [Route.eval_near_end, D.endpoint_eq] <;>
    dsimp [restrictionTime] <;> split_ifs <;> simp [cutPort, germ]

/-- Exterior pieces retain continuous simplicity, with no assumptions on their slopes,
number of bends, loop status or the incidence of their other end. -/
theorem IsEmbedding.outsideRoute_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (e : Fin G.2.length) :
    (D.outsideRoute v ρ e).IsSimple := by
  have hs := hD.restrictionTime_mem v hρ hlen (e, false)
  have ht := hD.restrictionTime_mem v hρ hlen (e, true)
  exact (hD.simple e).cutEnds hs.1 ht.1 (by linarith [hs.2, ht.2])

/-- Cutting the star does not create any point outside an old edge's continuous support. -/
theorem IsEmbedding.support_outsideRoute_subset {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖) (e : Fin G.2.length) :
    (D.outsideRoute v ρ e).support ⊆ (D.route e).support := by
  have hs := hD.restrictionTime_mem v hρ hlen (e, false)
  have ht := hD.restrictionTime_mem v hρ hlen (e, true)
  exact (D.route e).support_cutEnds_subset hs.1 ht.1 (by linarith [hs.2, ht.2])

/-- Every point where an exterior piece meets the closed replacement ball is its own
boundary port at an original end incident to the replaced vertex. Thus an interior patch
cannot meet an exterior route interior. Both loop ends remain separate cases. -/
theorem IsEmbedding.outsideRoute_ball_contact {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (hlocal : ∀ e (i : Fin (D.route e).segments) z,
      z ∈ Metric.closedBall (D.vertex v) ρ →
      z ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v))
    (e : Fin G.2.length) (i : Fin (D.outsideRoute v ρ e).segments)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (hz : (D.outsideRoute v ρ e).eval i u ∈ Metric.closedBall (D.vertex v) ρ) :
    ∃ b, (D.outsideRoute v ρ e).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
      (D.outsideRoute v ρ e).eval i u = D.cutPort ρ (e, b) := by
  let s := D.restrictionTime v ρ (e, false)
  let t := D.restrictionTime v ρ (e, true)
  have hs := hD.restrictionTime_mem v hρ hlen (e, false)
  have ht := hD.restrictionTime_mem v hρ hlen (e, true)
  have hst : s + t < 1 := by dsimp [s, t]; linarith [hs.2, ht.2]
  change Fin (D.route e).segments at i
  let τ := (D.route e).cutTime s t i u
  have hτ := (D.route e).cutTime_mem hs.1 ht.1 hst i hu
  have hbounds := (D.route e).cutTime_bounds hs.1 ht.1 hst i hu
  have heval : (D.outsideRoute v ρ e).eval i u = (D.route e).eval i τ :=
    (D.route e).eval_cutEnds s t i u
  have hτball : (D.route e).eval i τ ∈ Metric.closedBall (D.vertex v) ρ := heval ▸ hz
  have hseg : (D.route e).eval i τ ∈
      segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) :=
    lineMap_mem_segment ℝ _ _ hτ
  rcases hlocal e i _ hτball hseg with ⟨hi, hv⟩ | ⟨hi, hv⟩
  · have hi0 : i = 0 := Fin.ext hi
    have hsval : s = ρ / ‖D.germ (e, false)‖ := by
      simp only [s, restrictionTime, hv, ↓reduceIte]
    have hlo : (D.route e).cutLower s i = s := by simp [Route.cutLower, hi]
    have hn : 0 < ‖D.germ (e, false)‖ := norm_pos_iff.mpr (hD.germ_ne_zero _)
    have hpoint : (D.route e).eval i τ = D.vertex v + τ • D.germ (e, false) := by
      rw [hi0, show (0 : Fin (D.route e).segments) = (D.route e).endSegment false from rfl,
        ← show Route.endTime false τ = τ from rfl, Route.eval_near_end, D.endpoint_eq, hv]
      rfl
    have hdist : τ * ‖D.germ (e, false)‖ ≤ ρ := by
      rw [Metric.mem_closedBall, hpoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hτ.1] at hτball
      exact hτball
    have hτs : τ = s := by
      have hle : τ ≤ ρ / ‖D.germ (e, false)‖ := (le_div_iff₀ hn).mpr hdist
      rw [hlo] at hbounds
      exact le_antisymm (hle.trans_eq hsval.symm) hbounds.1
    have hu0 : u = 0 := ((D.route e).cutTime_eq_lower_iff hs.1 ht.1 hst i u).mp
      (hτs.trans hlo.symm)
    refine ⟨false, ?_, hv, ?_⟩
    · simp [Route.AtEnd, Route.position, hi, hu0]
    · rw [heval, hpoint, hτs, hsval, cutPort, hv]
  · have hilast : i = Fin.last (D.route e).bends := by
      apply Fin.ext
      change i.val = (D.route e).bends
      dsimp [Route.segments] at hi
      omega
    have htval : t = ρ / ‖D.germ (e, true)‖ := by
      simp only [t, restrictionTime, hv, ↓reduceIte]
    have hhi : (D.route e).cutUpper t i = 1 - t := by simp [Route.cutUpper, hi]
    have hn : 0 < ‖D.germ (e, true)‖ := norm_pos_iff.mpr (hD.germ_ne_zero _)
    have hpoint : (D.route e).eval i τ = D.vertex v + (1 - τ) • D.germ (e, true) := by
      calc
        _ = (D.route e).eval ((D.route e).endSegment true)
            (Route.endTime true (1 - τ)) := by
          rw [show Route.endTime true (1 - τ) = τ by dsimp [Route.endTime]; ring]
          rw [hilast]
          rfl
        _ = _ := by rw [Route.eval_near_end, D.endpoint_eq, hv]; rfl
    have hdist : (1 - τ) * ‖D.germ (e, true)‖ ≤ ρ := by
      rw [Metric.mem_closedBall, hpoint, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr hτ.2)] at hτball
      exact hτball
    have hτt : τ = 1 - t := by
      have hle : 1 - τ ≤ ρ / ‖D.germ (e, true)‖ := (le_div_iff₀ hn).mpr hdist
      rw [hhi] at hbounds
      rw [← htval] at hle
      linarith [hbounds.2]
    have hu1 : u = 1 := ((D.route e).cutTime_eq_upper_iff hs.1 ht.1 hst i u).mp
      (hτt.trans hhi.symm)
    refine ⟨true, ?_, hv, ?_⟩
    · simp only [Route.AtEnd, Route.position, hu1, ↓reduceIte]
      change (i.val : ℝ) + 1 = (D.route e).segments
      exact_mod_cast hi
    · rw [heval, hpoint, hτt, show 1 - (1 - t) = t by ring, htval, cutPort, hv]

/-- An actual embedding supplies its own common-radius cut and all exterior contact
conditions. No local disk, prescribed slopes, port coordinates or patch is a premise.
This stops at the exterior pieces: constructing and attaching a split patch is separate. -/
theorem IsEmbedding.exists_restriction {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.1) :
    ∃ ρ > 0,
      (∀ w ∈ G.1, D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v) ∧
      (∀ e, (D.outsideRoute v ρ e).IsSimple) ∧
      (∀ e, (D.outsideRoute v ρ e).support ⊆ (D.route e).support) ∧
      (∀ e (i : Fin (D.outsideRoute v ρ e).segments) (u : ℝ), u ∈ Set.Icc 0 1 →
        (D.outsideRoute v ρ e).eval i u ∈ Metric.closedBall (D.vertex v) ρ →
          ∃ b, (D.outsideRoute v ρ e).AtEnd i u b ∧ Dart.vertex (e, b) = v ∧
            (D.outsideRoute v ρ e).eval i u = D.cutPort ρ (e, b)) := by
  obtain ⟨ρ, hρ, hvertices, hlocal, hlen⟩ := hD.exists_restriction_radius v hv
  exact ⟨ρ, hρ, hvertices, hD.outsideRoute_simple v hρ hlen,
    hD.support_outsideRoute_subset v hρ hlen,
    fun e i _ hu hz => hD.outsideRoute_ball_contact v hρ hlen hlocal e i hu hz⟩

end Cslib.Complexity.Graph.PolygonalDrawing
