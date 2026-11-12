/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Geodesic.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Geodesics and shortest paths in metric graphs

This module develops unit-speed geodesics, `PathConnectedSpace`, and metric intervals
(shortest paths through a point) in `SimpleGraph.MetricGraph`.

## Main definitions

* `SimpleGraph.MetricGraph.IsGeodesic`: predicate for a unit-speed geodesic between two points.
* `SimpleGraph.MetricGraph.IsGeodesic.toPath`: turn a geodesic into a continuous `_root_.Path`.
* `SimpleGraph.MetricGraph.interval`: the metric interval `{ z | dist x z + dist z y = dist x y }`
  of points lying on a shortest path between `x` and `y`.

## Main results

* `SimpleGraph.MetricGraph.isGeodesic_of_lip`: a 1-Lipschitz curve between `x` and `y` of total
  parameter length `dist x y` is a geodesic.
* `SimpleGraph.MetricGraph.exists_isGeodesic`: every pair of points in `MetricGraph W` is joined
  by a unit-speed geodesic.
* `SimpleGraph.MetricGraph.instPathConnectedSpace`: `MetricGraph W` is path-connected.
* `SimpleGraph.MetricGraph.mem_interval_iff_exists_isGeodesic`: `z ∈ interval x y` holds if and
  only if there exists a geodesic from `x` to `y` passing through `z`.
* `SimpleGraph.MetricGraph.dist_edgePoint_eq_min_of_edge_ne`,
  `SimpleGraph.MetricGraph.dist_edgePoint_eq_min_same`: vertex-factored distance formulas for
  arbitrary fixed points along an edge.
* `SimpleGraph.MetricGraph.edgePoint_mem_interval_of_fst`,
  `SimpleGraph.MetricGraph.edgePoint_mem_interval_of_snd`: intermediate edge points on shortest
  paths routing through edge endpoints.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Unit-speed geodesics -/

/-- A unit-speed geodesic from `x` to `y` in `MetricGraph W`: a map `γ : ℝ → MetricGraph W`
starting at `x`, reaching `y` at time `dist x y`, and preserving Euclidean distance on
`[0, dist x y]`. -/
structure IsGeodesic [Finite V] (x y : MetricGraph W)
    (γ : ℝ → MetricGraph W) : Prop where
  /-- A geodesic starts at `x`. -/
  map_zero : γ 0 = x
  /-- A geodesic ends at `y` at parameter `dist x y`. -/
  map_dist : γ (dist x y) = y
  /-- A geodesic preserves Euclidean distance on `[0, dist x y]`. -/
  dist_eq : ∀ ⦃s t : ℝ⦄, s ∈ Set.Icc 0 (dist x y) → t ∈ Set.Icc 0 (dist x y) →
    dist (γ s) (γ t) = |s - t|

theorem isGeodesic_of_lip [Finite V] {x y : MetricGraph W} {γ : ℝ → MetricGraph W}
    (h0 : γ 0 = x) (hL : γ (dist x y) = y)
    (hlip : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ dist x y → dist (γ s) (γ t) ≤ t - s) :
    IsGeodesic x y γ := by
  refine ⟨h0, hL, fun s t hs ht => ?_⟩
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this t s ht hs (le_of_not_ge hst)
  have h1 : dist (γ 0) (γ s) ≤ s - 0 := hlip le_rfl hs.1 hs.2
  have h2 : dist (γ s) (γ t) ≤ t - s := hlip hs.1 hst ht.2
  have h3 : dist (γ t) (γ (dist x y)) ≤ dist x y - t := hlip ht.1 ht.2 le_rfl
  have htri : dist x y ≤ dist (γ 0) (γ s) + dist (γ s) (γ t) + dist (γ t) (γ (dist x y)) := by
    conv_lhs => rw [← h0, ← hL]
    exact dist_triangle4 (γ 0) (γ s) (γ t) (γ (dist x y))
  have hge : t - s ≤ dist (γ s) (γ t) := by linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  exact le_antisymm h2 hge

namespace IsGeodesic

variable [Finite V] {x y : MetricGraph W} {γ : ℝ → MetricGraph W}

theorem isometry (h : IsGeodesic x y γ) :
    Isometry (fun t : Set.Icc 0 (dist x y) => γ t) :=
  Isometry.of_dist_eq fun s t => by rw [Subtype.dist_eq, Real.dist_eq, h.dist_eq s.2 t.2]

theorem continuousOn (h : IsGeodesic x y γ) : ContinuousOn γ (Set.Icc 0 (dist x y)) :=
  continuousOn_iff_continuous_domRestrict.mpr h.isometry.continuous

/-- Turn a unit-speed geodesic from `x` to `y` into a continuous path. -/
noncomputable def toPath (h : IsGeodesic x y γ) : _root_.Path x y where
  toFun t := γ ((t : ℝ) * dist x y)
  continuous_toFun := by
    have hcont : Continuous (fun t : unitInterval =>
        (⟨(t : ℝ) * dist x y,
          mul_nonneg t.2.1 dist_nonneg,
          mul_le_of_le_one_left dist_nonneg t.2.2⟩ : Set.Icc 0 (dist x y))) :=
      Continuous.subtype_mk (continuous_subtype_val.mul continuous_const) _
    exact h.isometry.continuous.comp hcont
  source' := by simp [h.map_zero]
  target' := by simp [h.map_dist]

theorem reverse (h : IsGeodesic x y γ) :
    IsGeodesic y x (fun t => γ (dist x y - t)) := by
  refine ⟨by simp [h.map_dist], by simp [dist_comm, h.map_zero], fun s t hs ht => ?_⟩
  have hs' : dist x y - s ∈ Set.Icc 0 (dist x y) :=
    ⟨by linarith [hs.2, dist_comm x y], by linarith [hs.1]⟩
  have ht' : dist x y - t ∈ Set.Icc 0 (dist x y) :=
    ⟨by linarith [ht.2, dist_comm x y], by linarith [ht.1]⟩
  rw [h.dist_eq hs' ht', ← abs_neg]
  congr 1
  ring

theorem subsegment (h : IsGeodesic x y γ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ dist x y) : IsGeodesic (γ a) (γ b) (fun t => γ (a + t)) := by
  have haI : a ∈ Set.Icc 0 (dist x y) := ⟨ha, hab.trans hb⟩
  have hbI : b ∈ Set.Icc 0 (dist x y) := ⟨ha.trans hab, hb⟩
  have hd : dist (γ a) (γ b) = b - a := by
    rw [h.dist_eq haI hbI, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  refine ⟨by simp, by simp [hd, add_sub_cancel], fun s t hs ht => ?_⟩
  have hs' : a + s ∈ Set.Icc 0 (dist x y) := ⟨by linarith [hs.1], by linarith [hs.2, hd]⟩
  have ht' : a + t ∈ Set.Icc 0 (dist x y) := ⟨by linarith [ht.1], by linarith [ht.2, hd]⟩
  rw [h.dist_eq hs' ht']
  congr 1
  ring

end IsGeodesic

/-! ### Construction of geodesics -/

private noncomputable def dartRay (W : WeightedGraph V) (d : W.graph.Dart) (t₀ : unitInterval)
    (dir : Bool) (s : ℝ) : MetricGraph W :=
  edgePoint d (Set.projIcc 0 1 zero_le_one (if dir then (t₀ : ℝ) + s / W.weight d.edge
    else (t₀ : ℝ) - s / W.weight d.edge))

private theorem dartRay_zero (W : WeightedGraph V) (d : W.graph.Dart) (t₀ : unitInterval)
    (dir : Bool) : dartRay W d t₀ dir 0 = edgePoint d t₀ := by
  simp only [dartRay, zero_div, add_zero, sub_zero, ite_self, Set.projIcc_val]

private theorem dartRay_lip [Finite V] (W : WeightedGraph V) (d : W.graph.Dart)
    (t₀ : unitInterval) (dir : Bool) (s₁ s₂ : ℝ) :
    dist (dartRay W d t₀ dir s₁) (dartRay W d t₀ dir s₂) ≤ |s₁ - s₂| := by
  refine (dist_edgePoint_self_le d _ _).trans ?_
  have hw := W.dart_weight_pos d
  have hclip := (LipschitzWith.projIcc zero_le_one).dist_le_mul
    (if dir then (t₀ : ℝ) + s₁ / W.weight d.edge else (t₀ : ℝ) - s₁ / W.weight d.edge)
    (if dir then (t₀ : ℝ) + s₂ / W.weight d.edge else (t₀ : ℝ) - s₂ / W.weight d.edge)
  rw [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq] at hclip
  refine (mul_le_mul_of_nonneg_left hclip hw.le).trans ?_
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have heq : ((t₀ : ℝ) - s₁ / W.weight d.edge) - ((t₀ : ℝ) - s₂ / W.weight d.edge) =
        -(s₁ - s₂) / W.weight d.edge := by ring
    rw [heq, abs_div, abs_neg, abs_of_pos hw, mul_div_cancel₀ _ hw.ne']
  · simp only [↓reduceIte]
    have heq : ((t₀ : ℝ) + s₁ / W.weight d.edge) - ((t₀ : ℝ) + s₂ / W.weight d.edge) =
        (s₁ - s₂) / W.weight d.edge := by ring
    rw [heq, abs_div, abs_of_pos hw, mul_div_cancel₀ _ hw.ne']

private noncomputable def splice (L₁ : ℝ) (γ₁ γ₂ : ℝ → MetricGraph W) (s : ℝ) :
    MetricGraph W :=
  if s ≤ L₁ then γ₁ s else γ₂ (s - L₁)

private theorem splice_zero {L₁ : ℝ} (hL₁ : 0 ≤ L₁) (γ₁ γ₂ : ℝ → MetricGraph W) :
    splice L₁ γ₁ γ₂ 0 = γ₁ 0 := by
  simp [splice, hL₁]

private theorem splice_end {L₁ L₂ : ℝ} (hL₂ : 0 ≤ L₂) {γ₁ γ₂ : ℝ → MetricGraph W}
    (hjoin : γ₁ L₁ = γ₂ 0) :
    splice L₁ γ₁ γ₂ (L₁ + L₂) = γ₂ L₂ := by
  by_cases h0 : L₂ = 0
  · subst h0; simp [splice, hjoin]
  · have hgt : ¬(L₁ + L₂ ≤ L₁) := by linarith [lt_of_le_of_ne hL₂ (Ne.symm h0)]
    simp [splice, hgt]

private theorem splice_lip [Finite V] {L₁ L₂ : ℝ} (_hL₁ : 0 ≤ L₁) (_hL₂ : 0 ≤ L₂)
    {γ₁ γ₂ : ℝ → MetricGraph W} (hjoin : γ₁ L₁ = γ₂ 0)
    (hlip₁ : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ L₁ → dist (γ₁ s) (γ₁ t) ≤ t - s)
    (hlip₂ : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ L₂ → dist (γ₂ s) (γ₂ t) ≤ t - s) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ L₁ + L₂ →
      dist (splice L₁ γ₁ γ₂ s) (splice L₁ γ₁ γ₂ t) ≤ t - s := by
  intro s t hs hst ht
  by_cases hsL : s ≤ L₁ <;> by_cases htL : t ≤ L₁
  · simp only [splice, hsL, htL, ↓reduceIte]
    exact hlip₁ hs hst htL
  · simp only [splice, hsL, htL, ↓reduceIte]
    have h1 : dist (γ₁ s) (γ₁ L₁) ≤ L₁ - s := hlip₁ hs hsL le_rfl
    have h2 : dist (γ₂ 0) (γ₂ (t - L₁)) ≤ (t - L₁) - 0 :=
      hlip₂ le_rfl (by linarith) (by linarith)
    calc dist (γ₁ s) (γ₂ (t - L₁))
        ≤ dist (γ₁ s) (γ₁ L₁) + dist (γ₁ L₁) (γ₂ (t - L₁)) := dist_triangle _ _ _
      _ = dist (γ₁ s) (γ₁ L₁) + dist (γ₂ 0) (γ₂ (t - L₁)) := by rw [hjoin]
      _ ≤ (L₁ - s) + ((t - L₁) - 0) := add_le_add h1 h2
      _ = t - s := by ring
  · exact absurd (hst.trans htL) hsL
  · simp only [splice, hsL, htL, ↓reduceIte]
    exact (hlip₂ (by linarith) (by linarith) (by linarith)).trans_eq (by ring)

private noncomputable def walkCurve (W : WeightedGraph V) :
    ∀ {u v : V}, W.graph.Walk u v → ℝ → MetricGraph W
  | u, _, .nil => fun _ => vertex u
  | u, _, .cons (v := x) h q =>
    splice (W.weight s(u, x)) (dartRay W ⟨(u, x), h⟩ 0 true) (walkCurve W q)

private theorem walkCurve_zero (W : WeightedGraph V) {u v : V} (p : W.graph.Walk u v) :
    walkCurve W p 0 = vertex u := by
  cases p with
  | nil => rfl
  | cons h q =>
    rw [walkCurve, splice_zero (W.weight_nonneg h), dartRay_zero, edgePoint_zero]

private theorem walkCurve_cons_join (W : WeightedGraph V) {u x z : V} (h : W.graph.Adj u x)
    (q : W.graph.Walk x z) :
    dartRay W ⟨(u, x), h⟩ 0 true (W.weight s(u, x)) = walkCurve W q 0 := by
  have hw := W.weight_pos h
  rw [walkCurve_zero]
  simp only [dartRay, ↓reduceIte, Set.Icc.coe_zero, zero_add, Dart.edge_mk,
    div_self hw.ne', Set.projIcc_right zero_le_one]
  exact edgePoint_one ⟨(u, x), h⟩

private theorem walkCurve_end (W : WeightedGraph V) {u v : V} (p : W.graph.Walk u v) :
    walkCurve W p (walkLength W.weight p) = vertex v := by
  induction p with
  | nil => rfl
  | cons h q ih =>
    rw [walkLength_cons, walkCurve]
    exact (splice_end (walkLength_nonneg W.weight W.weight_nonneg q)
      (walkCurve_cons_join W h q)).trans ih

private theorem walkCurve_lip [Finite V] (W : WeightedGraph V) {u v : V} (p : W.graph.Walk u v) :
    ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ walkLength W.weight p →
      dist (walkCurve W p s) (walkCurve W p t) ≤ t - s := by
  induction p with
  | nil =>
    intro s t hs hst ht
    simp only [walkLength_nil] at ht
    simp only [walkCurve, dist_self]
    linarith
  | cons h q ih =>
    rw [walkLength_cons, walkCurve]
    exact splice_lip (W.weight_nonneg h) (walkLength_nonneg W.weight W.weight_nonneg q)
      (walkCurve_cons_join W h q)
      (fun s t _ hst _ => (dartRay_lip W _ 0 true s t).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]))
      ih

private theorem exists_isGeodesic_vertex_vertex [Finite V] (u v : V) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic (vertex u : MetricGraph W) (vertex v) γ := by
  obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
  refine ⟨walkCurve W p, isGeodesic_of_lip (walkCurve_zero W p) ?_ ?_⟩
  · rw [dist_vertex, ← hp]
    exact walkCurve_end W p
  · intro s t hs hst ht
    rw [dist_vertex, ← hp] at ht
    exact walkCurve_lip W p hs hst ht

private noncomputable def dartToEndCurve (W : WeightedGraph V) (d : W.graph.Dart)
    (t : unitInterval) (b : Bool) (s : ℝ) : MetricGraph W :=
  dartRay W d t b s

private theorem dartToEndCurve_zero (W : WeightedGraph V) (d : W.graph.Dart)
    (t : unitInterval) (b : Bool) : dartToEndCurve W d t b 0 = edgePoint d t :=
  dartRay_zero W d t b

private theorem dartToEndCurve_end (W : WeightedGraph V) (d : W.graph.Dart)
    (t : unitInterval) (b : Bool) :
    dartToEndCurve W d t b
        (if b then (1 - (t : ℝ)) * W.weight d.edge else (t : ℝ) * W.weight d.edge) =
      vertex (if b then d.snd else d.fst) := by
  have hw := W.dart_weight_pos d
  cases b <;> simp only [dartToEndCurve, dartRay, Bool.false_eq_true, ↓reduceIte,
    mul_div_cancel_right₀ _ hw.ne']
  · simp only [sub_self, Set.projIcc_left zero_le_one]
    exact edgePoint_zero d
  · have : (t : ℝ) + (1 - t) = 1 := by ring
    rw [this, Set.projIcc_right zero_le_one]
    exact edgePoint_one d

private noncomputable def endToDartCurve (W : WeightedGraph V) (d : W.graph.Dart)
    (b : Bool) (s : ℝ) : MetricGraph W :=
  dartRay W d (if b then 1 else 0) (!b) s

private theorem endToDartCurve_zero (W : WeightedGraph V) (d : W.graph.Dart)
    (b : Bool) : endToDartCurve W d b 0 = vertex (if b then d.snd else d.fst) := by
  cases b <;> simp only [endToDartCurve, dartRay_zero, Bool.false_eq_true, ↓reduceIte,
    edgePoint_zero, edgePoint_one]

private theorem endToDartCurve_end (W : WeightedGraph V) (d : W.graph.Dart)
    (t : unitInterval) (b : Bool) :
    endToDartCurve W d b
        (if b then (1 - (t : ℝ)) * W.weight d.edge else (t : ℝ) * W.weight d.edge) =
      edgePoint d t := by
  have hw := W.dart_weight_pos d
  cases b
  · simp only [endToDartCurve, dartRay, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Set.Icc.coe_zero, zero_add, mul_div_cancel_right₀ _ hw.ne', Set.projIcc_val]
  · simp only [endToDartCurve, dartRay, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Set.Icc.coe_one, mul_div_cancel_right₀ _ hw.ne']
    have : 1 - (1 - (t : ℝ)) = t := by ring
    rw [this, Set.projIcc_val]

private theorem exists_isGeodesic_vertex_edgePoint [Finite V] (u : V) (d : W.graph.Dart)
    (t : unitInterval) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic (vertex u : MetricGraph W) (edgePoint d t) γ := by
  have hd := dist_vertex_edgePoint u d t (W := W)
  have branch : ∀ b : Bool,
      dist (vertex u : MetricGraph W) (edgePoint d t) =
        vertexDist W.graph W.weight u (if b then d.snd else d.fst) +
          (if b then (1 - (t : ℝ)) * W.weight d.edge else (t : ℝ) * W.weight d.edge) →
      ∃ γ : ℝ → MetricGraph W, IsGeodesic (vertex u : MetricGraph W) (edgePoint d t) γ := by
    intro b hb
    let v := if b then d.snd else d.fst
    let L₁ := vertexDist W.graph W.weight u v
    let L₂ := if b then (1 - (t : ℝ)) * W.weight d.edge else (t : ℝ) * W.weight d.edge
    have hL₁ : 0 ≤ L₁ := vertexDist_nonneg W.weight_nonneg u v
    have hL₂ : 0 ≤ L₂ := by
      cases b <;> simp only [L₂, Bool.false_eq_true, ↓reduceIte]
      · exact mul_nonneg t.2.1 (W.dart_weight_nonneg d)
      · exact mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d)
    obtain ⟨γ₁, hγ₁⟩ := exists_isGeodesic_vertex_vertex (W := W) u v
    have hL₁eq : dist (vertex u : MetricGraph W) (vertex v) = L₁ := dist_vertex u v
    have hjoin : γ₁ L₁ = endToDartCurve W d b 0 := by
      rw [← hL₁eq, hγ₁.map_dist, endToDartCurve_zero]
    refine ⟨splice L₁ γ₁ (endToDartCurve W d b), isGeodesic_of_lip ?_ ?_ ?_⟩
    · rw [splice_zero hL₁, hγ₁.map_zero]
    · rw [hb]
      exact (splice_end hL₂ hjoin).trans (endToDartCurve_end W d t b)
    · intro x y hx hxy hy
      rw [hb] at hy
      exact splice_lip hL₁ hL₂ hjoin
        (fun s a hs hsa ha => by
          rw [hγ₁.dist_eq ⟨hs, hsa.trans (ha.trans_eq hL₁eq.symm)⟩
            ⟨hs.trans hsa, ha.trans_eq hL₁eq.symm⟩,
            abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsa)])
        (fun s a _ hsa _ => (dartRay_lip W d _ (!b) s a).trans_eq (by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsa)]))
        hx hxy hy
  rcases min_choice (vertexDist W.graph W.weight u d.fst + (t : ℝ) * W.weight d.edge)
      (vertexDist W.graph W.weight u d.snd + (1 - (t : ℝ)) * W.weight d.edge) with hmin | hmin
  · exact branch false (by simpa only [Bool.false_eq_true, ↓reduceIte] using hd.trans hmin)
  · exact branch true (by simpa only [↓reduceIte] using hd.trans hmin)

private theorem exists_isGeodesic_via_endpoints [Finite V]
    (d₁ : W.graph.Dart) (t₁ : unitInterval) (d₂ : W.graph.Dart) (t₂ : unitInterval)
    (a b : Bool)
    (hdist : dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) =
      (if a then (1 - (t₁ : ℝ)) * W.weight d₁.edge else (t₁ : ℝ) * W.weight d₁.edge) +
      vertexDist W.graph W.weight (if a then d₁.snd else d₁.fst) (if b then d₂.snd else d₂.fst) +
      (if b then (1 - (t₂ : ℝ)) * W.weight d₂.edge else (t₂ : ℝ) * W.weight d₂.edge)) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) γ := by
  let L₁ : ℝ := if a then (1 - (t₁ : ℝ)) * W.weight d₁.edge else (t₁ : ℝ) * W.weight d₁.edge
  let u₁ : V := if a then d₁.snd else d₁.fst
  let L₂ : ℝ := vertexDist W.graph W.weight u₁ (if b then d₂.snd else d₂.fst)
  let L₃ : ℝ := if b then (1 - (t₂ : ℝ)) * W.weight d₂.edge else (t₂ : ℝ) * W.weight d₂.edge
  have hL₁ : 0 ≤ L₁ := by
    cases a <;> simp only [L₁, Bool.false_eq_true, ↓reduceIte]
    · exact mul_nonneg t₁.2.1 (W.dart_weight_nonneg d₁)
    · exact mul_nonneg (unitInterval.one_sub_nonneg t₁) (W.dart_weight_nonneg d₁)
  have hL₂ : 0 ≤ L₂ := vertexDist_nonneg W.weight_nonneg _ _
  have hL₃ : 0 ≤ L₃ := by
    cases b <;> simp only [L₃, Bool.false_eq_true, ↓reduceIte]
    · exact mul_nonneg t₂.2.1 (W.dart_weight_nonneg d₂)
    · exact mul_nonneg (unitInterval.one_sub_nonneg t₂) (W.dart_weight_nonneg d₂)
  obtain ⟨γ₂, hγ₂⟩ := exists_isGeodesic_vertex_vertex (W := W) u₁ (if b then d₂.snd else d₂.fst)
  have hL₂eq : dist (vertex u₁ : MetricGraph W) (vertex (if b then d₂.snd else d₂.fst)) = L₂ :=
    dist_vertex _ _
  have hjoin23 : γ₂ L₂ = endToDartCurve W d₂ b 0 := by
    rw [← hL₂eq, hγ₂.map_dist, endToDartCurve_zero]
  let γ₂₃ := splice L₂ γ₂ (endToDartCurve W d₂ b)
  have hjoin123 : dartToEndCurve W d₁ t₁ a L₁ = γ₂₃ 0 := by
    dsimp only [γ₂₃]
    rw [splice_zero hL₂, hγ₂.map_zero]
    exact dartToEndCurve_end W d₁ t₁ a
  refine ⟨splice L₁ (dartToEndCurve W d₁ t₁ a) γ₂₃, isGeodesic_of_lip ?_ ?_ ?_⟩
  · rw [splice_zero hL₁, dartToEndCurve_zero]
  · have hsum : dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) = L₁ + (L₂ + L₃) := by
      linarith [hdist]
    rw [hsum, splice_end (add_nonneg hL₂ hL₃) hjoin123]
    exact (splice_end hL₃ hjoin23).trans (endToDartCurve_end W d₂ t₂ b)
  · have hlip23 : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ L₂ + L₃ → dist (γ₂₃ s) (γ₂₃ t) ≤ t - s :=
      splice_lip hL₂ hL₃ hjoin23
        (fun s t hs hst ht => by
          rw [hγ₂.dist_eq ⟨hs, hst.trans (ht.trans_eq hL₂eq.symm)⟩
            ⟨hs.trans hst, ht.trans_eq hL₂eq.symm⟩,
            abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)])
        (fun s t _ hst _ => (dartRay_lip W d₂ _ (!b) s t).trans_eq (by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]))
    intro s t hs hst ht
    have hsum : L₁ + (L₂ + L₃) = dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) := by
      linarith [hdist]
    rw [← hsum] at ht
    exact splice_lip hL₁ (add_nonneg hL₂ hL₃) hjoin123
      (fun u v _ huv _ => (dartRay_lip W d₁ t₁ a u v).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)]))
      hlip23 hs hst ht

private theorem exists_isGeodesic_edgePoint_direct [Finite V] (d : W.graph.Dart)
    (t₁ t₂ : unitInterval)
    (hdist : dist (edgePoint d t₁ : MetricGraph W) (edgePoint d t₂) =
      |(t₁ : ℝ) - t₂| * W.weight d.edge) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic (edgePoint d t₁ : MetricGraph W) (edgePoint d t₂) γ := by
  have hw := W.dart_weight_pos d
  by_cases hle : (t₁ : ℝ) ≤ t₂
  · refine ⟨dartRay W d t₁ true, isGeodesic_of_lip (dartRay_zero W d t₁ true) ?_ ?_⟩
    · have habs : |(t₁ : ℝ) - t₂| = t₂ - t₁ := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [hdist, habs]
      simp only [dartRay, ↓reduceIte, mul_div_cancel_right₀ _ hw.ne', add_sub_cancel,
        Set.projIcc_val]
    · exact fun s t _ hst _ => (dartRay_lip W d t₁ true s t).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)])
  · have hge : (t₂ : ℝ) ≤ t₁ := le_of_not_ge hle
    refine ⟨dartRay W d t₁ false, isGeodesic_of_lip (dartRay_zero W d t₁ false) ?_ ?_⟩
    · have habs : |(t₁ : ℝ) - t₂| = t₁ - t₂ := abs_of_nonneg (sub_nonneg.mpr hge)
      rw [hdist, habs]
      simp only [dartRay, Bool.false_eq_true, ↓reduceIte, mul_div_cancel_right₀ _ hw.ne',
        sub_sub_cancel, Set.projIcc_val]
    · exact fun s t _ hst _ => (dartRay_lip W d t₁ false s t).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)])

private theorem exists_isGeodesic_of_min_four [Finite V]
    (d₁ : W.graph.Dart) (t₁ : unitInterval) (d₂ : W.graph.Dart) (t₂ : unitInterval)
    (hd : dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) =
      min
        (min ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.fst +
                (t₂ : ℝ) * W.weight d₂.edge)
             ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.snd +
                (1 - (t₂ : ℝ)) * W.weight d₂.edge))
        (min ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.fst +
                (t₂ : ℝ) * W.weight d₂.edge)
             ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.snd +
                (1 - (t₂ : ℝ)) * W.weight d₂.edge))) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) γ := by
  rcases min_choice _ (_ : ℝ) with hmin1 | hmin1 <;> rw [hmin1] at hd <;>
    rcases min_choice _ (_ : ℝ) with hmin2 | hmin2 <;> rw [hmin2] at hd
  · exact exists_isGeodesic_via_endpoints d₁ t₁ d₂ t₂ false false hd
  · exact exists_isGeodesic_via_endpoints d₁ t₁ d₂ t₂ false true hd
  · exact exists_isGeodesic_via_endpoints d₁ t₁ d₂ t₂ true false hd
  · exact exists_isGeodesic_via_endpoints d₁ t₁ d₂ t₂ true true hd

/-- Every pair of points in `MetricGraph W` is connected by a unit-speed geodesic. -/
theorem exists_isGeodesic [Finite V] (x y : MetricGraph W) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic x y γ := by
  induction x using ind_simple with
  | vertex u =>
    induction y using ind_simple with
    | vertex v => exact exists_isGeodesic_vertex_vertex u v
    | edgePoint d t => exact exists_isGeodesic_vertex_edgePoint u d t
  | edgePoint d₁ t₁ =>
    induction y using ind_simple with
    | vertex v =>
      obtain ⟨γ, hγ⟩ := exists_isGeodesic_vertex_edgePoint v d₁ t₁
      exact ⟨_, hγ.reverse⟩
    | edgePoint d₂ t₂ =>
      by_cases he : d₁.edge = d₂.edge
      · rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | hsym
        · have hd := dist_edgePoint_edgePoint_same d₁ t₁ t₂ (W := W)
          rcases min_choice (|(t₁ : ℝ) - t₂| * W.weight d₁.edge) (_ : ℝ) with hmin | hmin
          · exact exists_isGeodesic_edgePoint_direct d₁ t₁ t₂ (hd.trans hmin)
          · exact exists_isGeodesic_of_min_four d₁ t₁ d₁ t₂ (hd.trans hmin)
        · subst hsym
          rw [← edgePoint_symm d₂ t₂]
          have hd := dist_edgePoint_edgePoint_same d₂.symm t₁ (unitInterval.symm t₂) (W := W)
          rcases min_choice (|(t₁ : ℝ) - unitInterval.symm t₂| * W.weight d₂.symm.edge)
              (_ : ℝ) with hmin | hmin
          · exact exists_isGeodesic_edgePoint_direct d₂.symm t₁ (unitInterval.symm t₂)
              (hd.trans hmin)
          · exact exists_isGeodesic_of_min_four d₂.symm t₁ d₂.symm (unitInterval.symm t₂)
              (hd.trans hmin)
      · exact exists_isGeodesic_of_min_four d₁ t₁ d₂ t₂
          (dist_edgePoint_edgePoint_of_edge_ne he t₁ t₂)

instance instPathConnectedSpace [Finite V] : PathConnectedSpace (MetricGraph W) where
  nonempty := inferInstance
  joined x y :=
    let ⟨_, hγ⟩ := exists_isGeodesic x y
    ⟨hγ.toPath⟩

/-! ### Shortest paths through a point (metric intervals) -/

/-- The metric interval `{ z | dist x z + dist z y = dist x y }` of points lying on a shortest
path between `x` and `y`. -/
@[expose] def interval [Finite V] (x y : MetricGraph W) : Set (MetricGraph W) :=
  { z | dist x z + dist z y = dist x y }

@[simp]
theorem mem_interval_iff [Finite V] {x y z : MetricGraph W} :
    z ∈ interval x y ↔ dist x z + dist z y = dist x y := Iff.rfl

theorem left_mem_interval [Finite V] (x y : MetricGraph W) : x ∈ interval x y := by
  simp [interval]

theorem right_mem_interval [Finite V] (x y : MetricGraph W) : y ∈ interval x y := by
  simp [interval]

theorem interval_comm [Finite V] (x y : MetricGraph W) : interval x y = interval y x := by
  ext z
  simp only [mem_interval_iff, dist_comm, add_comm]

theorem interval_eq_singleton_self [Finite V] (x : MetricGraph W) : interval x x = {x} := by
  ext z
  simp only [mem_interval_iff, dist_self, Set.mem_singleton_iff]
  constructor
  · intro h
    have hz : dist x z = 0 := by
      linarith [dist_nonneg (x := x) (y := z), dist_nonneg (x := z) (y := x)]
    exact (dist_eq_zero.mp hz).symm
  · rintro rfl
    simp

theorem IsGeodesic.mem_interval [Finite V] {x y : MetricGraph W} {γ : ℝ → MetricGraph W}
    (h : IsGeodesic x y γ) {s : ℝ} (hs : s ∈ Set.Icc 0 (dist x y)) :
    γ s ∈ interval x y := by
  rw [mem_interval_iff]
  have h1 : dist x (γ s) = s := by
    rw [← h.map_zero, h.dist_eq ⟨le_rfl, dist_nonneg⟩ hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  have h2 : dist (γ s) y = dist x y - s := by
    conv_lhs => rw [← h.map_dist (x := x)]
    rw [h.dist_eq hs ⟨dist_nonneg, le_rfl⟩, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
  linarith

/-- A point `z` lies in the metric interval `interval x y` if and only if some unit-speed geodesic
from `x` to `y` passes through `z` at some `s ∈ [0, dist x y]`. -/
theorem mem_interval_iff_exists_isGeodesic [Finite V] {x y z : MetricGraph W} :
    z ∈ interval x y ↔
      ∃ γ : ℝ → MetricGraph W, IsGeodesic x y γ ∧ ∃ s ∈ Set.Icc 0 (dist x y), γ s = z := by
  constructor
  · intro hz
    rw [mem_interval_iff] at hz
    obtain ⟨γ₁, hγ₁⟩ := exists_isGeodesic x z
    obtain ⟨γ₂, hγ₂⟩ := exists_isGeodesic z y
    let γ := splice (dist x z) γ₁ γ₂
    have hjoin : γ₁ (dist x z) = γ₂ 0 := by rw [hγ₁.map_dist, hγ₂.map_zero]
    refine ⟨γ, isGeodesic_of_lip ?_ ?_ ?_, dist x z,
        ⟨dist_nonneg, by linarith [dist_nonneg (x := z) (y := y)]⟩, ?_⟩
    · dsimp only [γ]
      rw [splice_zero dist_nonneg, hγ₁.map_zero]
    · dsimp only [γ]
      rw [← hz]
      exact (splice_end dist_nonneg hjoin).trans hγ₂.map_dist
    · intro s t hs hst ht
      rw [← hz] at ht
      exact splice_lip dist_nonneg dist_nonneg hjoin
        (fun a b ha hab hb => by
          rw [hγ₁.dist_eq ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩,
            abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)])
        (fun a b ha hab hb => by
          rw [hγ₂.dist_eq ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩,
            abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)])
        hs hst ht
    · simp only [γ, splice, le_rfl, ↓reduceIte, hγ₁.map_dist]
  · rintro ⟨γ, hγ, s, hs, rfl⟩
    exact hγ.mem_interval hs

theorem exists_isGeodesic_through_of_mem_interval [Finite V] {x y z : MetricGraph W}
    (hz : z ∈ interval x y) :
    ∃ γ : ℝ → MetricGraph W, IsGeodesic x y γ ∧ γ (dist x z) = z := by
  obtain ⟨γ, hγ, s, hs, rfl⟩ := mem_interval_iff_exists_isGeodesic.mp hz
  have hds : dist x (γ s) = s := by
    rw [← hγ.map_zero, hγ.dist_eq ⟨le_rfl, dist_nonneg⟩ hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  exact ⟨γ, hγ, by rw [hds]⟩

theorem exists_mem_interval_dist_eq [Finite V] (x y : MetricGraph W) {r : ℝ}
    (hr : r ∈ Set.Icc 0 (dist x y)) :
    ∃ z ∈ interval x y, dist x z = r ∧ dist z y = dist x y - r := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic x y
  refine ⟨γ r, hγ.mem_interval hr, ?_, ?_⟩
  · rw [← hγ.map_zero, hγ.dist_eq ⟨le_rfl, dist_nonneg⟩ hr, zero_sub, abs_neg, abs_of_nonneg hr.1]
  · conv_lhs => rw [← hγ.map_dist (x := x)]
    rw [hγ.dist_eq hr ⟨dist_nonneg, le_rfl⟩, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hr.2)]

theorem mem_interval_trans_left [Finite V] {x y z w : MetricGraph W}
    (hz : z ∈ interval x y) (hw : w ∈ interval x z) : w ∈ interval x y := by
  rw [mem_interval_iff] at hz hw ⊢
  linarith [dist_triangle x w z, dist_triangle w z y, dist_triangle x w y]

theorem mem_interval_trans_right [Finite V] {x y z w : MetricGraph W}
    (hz : z ∈ interval x y) (hw : w ∈ interval x z) : z ∈ interval w y := by
  rw [mem_interval_iff] at hz hw ⊢
  linarith [dist_triangle x w z, dist_triangle w z y, dist_triangle x w y]

/-! ### Shortest paths and vertex-factored edge distances -/

theorem dist_edgePoint_eq_min_of_edge_ne [Finite V] {d₀ d : W.graph.Dart}
    (hne : d₀.edge ≠ d.edge) (s t : unitInterval) :
    dist (edgePoint d₀ s : MetricGraph W) (edgePoint d t) =
      min (dist (edgePoint d₀ s : MetricGraph W) (vertex d.fst) + (t : ℝ) * W.weight d.edge)
          (dist (edgePoint d₀ s : MetricGraph W) (vertex d.snd) +
            (1 - (t : ℝ)) * W.weight d.edge) := by
  rw [dist_edgePoint_edgePoint_of_edge_ne hne, dist_edgePoint_vertex, dist_edgePoint_vertex]
  simp only [min_add, add_assoc]
  ac_rfl

theorem dist_edgePoint_eq_min_same [Finite V] (d : W.graph.Dart) (s t : unitInterval) :
    dist (edgePoint d s : MetricGraph W) (edgePoint d t) =
      min (|(s : ℝ) - t| * W.weight d.edge)
        (min (dist (edgePoint d s : MetricGraph W) (vertex d.fst) + (t : ℝ) * W.weight d.edge)
             (dist (edgePoint d s : MetricGraph W) (vertex d.snd) +
               (1 - (t : ℝ)) * W.weight d.edge)) := by
  rw [dist_edgePoint_edgePoint_same, dist_edgePoint_vertex, dist_edgePoint_vertex]
  congr 1
  simp only [min_add, add_assoc]
  ac_rfl

/-- Two points of one dart whose parameters differ by at most `1 / 2` are at distance
`|s - t|` times the dart's weight: no detour through the endpoints is shorter. -/
theorem dist_edgePoint_edgePoint_of_abs_sub_le_half [Finite V] (d : W.graph.Dart)
    {s t : unitInterval} (hst : |(s : ℝ) - t| ≤ 1 / 2) :
    dist (edgePoint d s : MetricGraph W) (edgePoint d t) = |(s : ℝ) - t| * W.weight d.edge := by
  rw [dist_edgePoint_edgePoint_same, vertexDist_self W.weight_nonneg,
    vertexDist_self W.weight_nonneg]
  have hw := W.dart_weight_nonneg d
  have h₁ := vertexDist_nonneg W.weight_nonneg (G := W.graph) d.fst d.snd
  have h₂ := vertexDist_nonneg W.weight_nonneg (G := W.graph) d.snd d.fst
  have hs0 := s.2.1; have hs1 := s.2.2; have ht0 := t.2.1; have ht1 := t.2.2
  obtain ⟨hlo, hhi⟩ := abs_le.mp hst
  have key : ∀ k : ℝ, |(s : ℝ) - t| ≤ k →
      |(s : ℝ) - t| * W.weight d.edge ≤ k * W.weight d.edge :=
    fun k hk => mul_le_mul_of_nonneg_right hk hw
  have e₁ := key ((s : ℝ) + t) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have e₂ := key ((s : ℝ) + (1 - t)) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have e₃ := key ((1 - s : ℝ) + t) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have e₄ := key ((1 - s : ℝ) + (1 - t)) (abs_le.mpr ⟨by linarith, by linarith⟩)
  refine min_eq_left (le_min (le_min ?_ ?_) (le_min ?_ ?_)) <;> linarith

/-- Points on two darts that leave a common vertex along distinct edges, each in the first half of
its dart, are at distance the sum of their offsets from that vertex. -/
theorem dist_edgePoint_edgePoint_of_fst_eq [Finite V] {d₁ d₂ : W.graph.Dart}
    (hne : d₁.edge ≠ d₂.edge) (hfst : d₁.fst = d₂.fst) {t₁ t₂ : unitInterval}
    (ht₁ : (t₁ : ℝ) ≤ 1 / 2) (ht₂ : (t₂ : ℝ) ≤ 1 / 2) :
    dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) =
      t₁ * W.weight d₁.edge + t₂ * W.weight d₂.edge := by
  rw [dist_edgePoint_edgePoint_of_edge_ne hne, hfst, vertexDist_self W.weight_nonneg, add_zero]
  have hw₁ := W.dart_weight_nonneg d₁
  have hw₂ := W.dart_weight_nonneg d₂
  have h₁ := vertexDist_nonneg W.weight_nonneg (G := W.graph) d₂.fst d₂.snd
  have h₂ := vertexDist_nonneg W.weight_nonneg (G := W.graph) d₁.snd d₂.fst
  have h₃ := vertexDist_nonneg W.weight_nonneg (G := W.graph) d₁.snd d₂.snd
  have e₁ := mul_le_mul_of_nonneg_right (show (t₁ : ℝ) ≤ 1 - t₁ by linarith) hw₁
  have e₂ := mul_le_mul_of_nonneg_right (show (t₂ : ℝ) ≤ 1 - t₂ by linarith) hw₂
  exact le_antisymm ((min_le_left _ _).trans (min_le_left _ _))
    (le_min (le_min le_rfl (by linarith)) (le_min (by linarith) (by linarith)))

theorem edgePoint_mem_interval_of_fst [Finite V] {x : MetricGraph W} {d : W.graph.Dart}
    {s t : unitInterval} (hst : (s : ℝ) ≤ t)
    (hx : dist x (edgePoint d t) = dist x (vertex d.fst) + (t : ℝ) * W.weight d.edge) :
    edgePoint d s ∈ interval x (edgePoint d t) := by
  rw [mem_interval_iff]
  have h1 : dist x (edgePoint d s) ≤ dist x (vertex d.fst) + (s : ℝ) * W.weight d.edge := by
    refine (dist_triangle x (vertex d.fst) (edgePoint d s)).trans ?_
    gcongr
    rw [← edgePoint_zero d]
    refine (dist_edgePoint_self_le d 0 s).trans_eq ?_
    rw [Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg s.2.1, mul_comm]
  have h2 : dist (edgePoint d s) (edgePoint d t) ≤ ((t : ℝ) - s) * W.weight d.edge := by
    refine (dist_edgePoint_self_le d s t).trans_eq ?_
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst), mul_comm]
  have htri :
      dist x (edgePoint d t) ≤ dist x (edgePoint d s) + dist (edgePoint d s) (edgePoint d t) :=
    dist_triangle _ _ _
  linarith

theorem edgePoint_mem_interval_of_snd [Finite V] {x : MetricGraph W} {d : W.graph.Dart}
    {s t : unitInterval} (hst : (t : ℝ) ≤ s)
    (hx : dist x (edgePoint d t) = dist x (vertex d.snd) + (1 - (t : ℝ)) * W.weight d.edge) :
    edgePoint d s ∈ interval x (edgePoint d t) := by
  rw [← edgePoint_symm d s, ← edgePoint_symm d t]
  refine edgePoint_mem_interval_of_fst (by change 1 - (s : ℝ) ≤ 1 - t; linarith) ?_
  simpa only [edgePoint_symm, Dart.fst_symm, Dart.edge_symm, unitInterval.coe_symm_eq] using hx

theorem edgePoint_mem_interval_edgePoint_of_direct [Finite V] {d : W.graph.Dart}
    {a b t : unitInterval}
    (hd : dist (edgePoint d a : MetricGraph W) (edgePoint d b) =
      |(a : ℝ) - b| * W.weight d.edge)
    (ht : ((a : ℝ) ≤ t ∧ (t : ℝ) ≤ b) ∨ ((b : ℝ) ≤ t ∧ (t : ℝ) ≤ a)) :
    edgePoint d t ∈ interval (edgePoint d a) (edgePoint d b) := by
  rw [mem_interval_iff, hd]
  have hw := W.dart_weight_nonneg d
  have h1 := (dist_edgePoint_self_le d a t).trans_eq (mul_comm _ _)
  have h2 := (dist_edgePoint_self_le d t b).trans_eq (mul_comm _ _)
  have htri := dist_triangle (edgePoint d a : MetricGraph W) (edgePoint d t) (edgePoint d b)
  rw [hd] at htri
  rcases ht with ⟨hat, htb⟩ | ⟨hbt, hta⟩
  · have hsum : |(a : ℝ) - t| + |(t : ℝ) - b| = |(a : ℝ) - b| := by
      rw [abs_sub_comm (a : ℝ) t, abs_of_nonneg (sub_nonneg.mpr hat),
        abs_sub_comm (t : ℝ) b, abs_of_nonneg (sub_nonneg.mpr htb),
        abs_sub_comm (a : ℝ) b, abs_of_nonneg (sub_nonneg.mpr (hat.trans htb))]
      ring
    have hmul : |(a : ℝ) - t| * W.weight d.edge + |(t : ℝ) - b| * W.weight d.edge =
        |(a : ℝ) - b| * W.weight d.edge := by rw [← add_mul, hsum]
    linarith [add_le_add h1 h2]
  · have hsum : |(a : ℝ) - t| + |(t : ℝ) - b| = |(a : ℝ) - b| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hta), abs_of_nonneg (sub_nonneg.mpr hbt),
        abs_of_nonneg (sub_nonneg.mpr (hbt.trans hta))]
      ring
    have hmul : |(a : ℝ) - t| * W.weight d.edge + |(t : ℝ) - b| * W.weight d.edge =
        |(a : ℝ) - b| * W.weight d.edge := by rw [← add_mul, hsum]
    linarith [add_le_add h1 h2]

end MetricGraph

end SimpleGraph
