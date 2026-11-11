/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Bipartite.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Subdivision
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith

/-!
# Bipartite equal-length metric graphs

This module specializes metric graphs to connected graphs whose edges all have equal positive
weight `ℓ`, and especially bipartite equal-length graphs.
In a connected bipartite graph with uniform edge length `ℓ`, vertex distances equal `ℓ * G.dist`,
distances from any vertex differ by exactly `ℓ` across every edge, and hence the distance from any
vertex is affine on every edge without requiring subdivision. Moreover, bisecting every edge of an
arbitrary equal-length graph at its midpoint produces a bipartite equal-length subdivision with edge
length `ℓ / 2`.

## Main definitions

* `SimpleGraph.MetricGraph.equalLength`: a finite/connected simple graph equipped with constant
  positive edge length `ℓ`.
* `SimpleGraph.MetricGraph.midpointPoints`: vertices together with edge midpoints `1 / 2`.
* `SimpleGraph.MetricGraph.midpointSubdivision`: the midpoint subdivision of a weighted graph.

## Main results

* `SimpleGraph.MetricGraph.dist_vertex_eq_of_const_weight`: vertex distance equals `ℓ * G.dist`
  when all edges have weight `ℓ`.
* `SimpleGraph.MetricGraph.bipartite_dist_vertex_adj_diff`: in a bipartite equal-length graph,
  `|dist (vertex t) (vertex u) - dist (vertex t) (vertex v)| = ℓ` for every edge `u ~ v`.
* `SimpleGraph.MetricGraph.bipartite_const_weight_dist_edgePoint_affine`: in a bipartite
  equal-length graph, `s ↦ dist (vertex t) (edgePoint d s)` is affine on every edge without
  subdivision.
* `SimpleGraph.MetricGraph.midpointSubdivision_isBipartite`: the midpoint subdivision is
  bipartite.
* `SimpleGraph.MetricGraph.midpointSubdivision_weight_eq`: when `W` has constant edge length `ℓ`,
  every edge of `midpointSubdivision W` has length `ℓ / 2`.

## References

* STOC 2027 submission 1056, Appendix M / Corollary 5.3 (locator from Issue #4324 context; primary
  manuscript not inspected here).
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u}

/-! ### Constant edge weights and graph distance -/

/-- Equip a connected simple graph `G` with constant positive edge length `ℓ`. -/
@[expose] def equalLength (G : SimpleGraph V) (hconn : G.Connected) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    WeightedGraph V where
  graph := G
  weight _ := ℓ
  weight_pos := fun {_ _} _ => hℓ
  connected := hconn

private theorem walkLength_eq_of_const_weight {G : SimpleGraph V} {w : Sym2 V → ℝ}
    {ℓ : ℝ} (hconst : ∀ e ∈ G.edgeSet, w e = ℓ) {u v : V} (p : G.Walk u v) :
    walkLength w p = (p.length : ℝ) * ℓ := by
  induction p with
  | nil => simp
  | cons h _ ih =>
    rw [walkLength_cons, Walk.length_cons, ih, hconst _ (G.mem_edgeSet.mpr h)]
    push_cast
    ring

theorem vertexDist_eq_of_const_weight [Finite V] {W : WeightedGraph V} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ) (u v : V) :
    vertexDist W.graph W.weight u v = ℓ * (W.graph.dist u v : ℝ) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨p, hp⟩ := W.connected.exists_walk_length_eq_dist u v
    refine (vertexDist_le W.weight_nonneg p).trans_eq ?_
    rw [walkLength_eq_of_const_weight hconst p, hp, mul_comm]
  · obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
    rw [← hp, walkLength_eq_of_const_weight hconst p, mul_comm ℓ]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (W.graph.dist_le p)) hℓ.le

theorem dist_vertex_eq_of_const_weight [Finite V] {W : WeightedGraph V} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ) (u v : V) :
    Dist.dist (vertex u : MetricGraph W) (vertex v) = ℓ * (W.graph.dist u v : ℝ) := by
  rw [dist_vertex]
  exact vertexDist_eq_of_const_weight hℓ hconst u v

/-! ### Bipartite parity and affine vertex distances -/

private theorem isBipartiteWith_walk_parity {G : SimpleGraph V} {s t : Set V}
    (hbip : G.IsBipartiteWith s t) {u v : V} (p : G.Walk u v) :
    (p.length % 2 = 0 → (u ∈ s ↔ v ∈ s) ∧ (u ∈ t ↔ v ∈ t)) ∧
    (p.length % 2 = 1 → u ∈ s ∧ v ∈ t ∨ u ∈ t ∧ v ∈ s) := by
  induction p with
  | nil => simp
  | cons hadj q ih =>
    rename_i a c z
    rw [Walk.length_cons]
    constructor
    · intro heven
      have hqodd : q.length % 2 = 1 := by omega
      rcases ih.2 hqodd with ⟨hcs, hzt⟩ | ⟨hct, hzs⟩
      · have hat : a ∈ t := hbip.mem_of_mem_adj hcs hadj.symm
        have hnas : a ∉ s := Set.disjoint_right.mp hbip.disjoint hat
        have hnzs : z ∉ s := Set.disjoint_right.mp hbip.disjoint hzt
        exact ⟨⟨fun h => absurd h hnas, fun h => absurd h hnzs⟩,
          ⟨fun _ => hzt, fun _ => hat⟩⟩
      · have has : a ∈ s := hbip.mem_of_mem_adj' hct hadj
        have hnat : a ∉ t := Set.disjoint_left.mp hbip.disjoint has
        have hnzt : z ∉ t := Set.disjoint_left.mp hbip.disjoint hzs
        exact ⟨⟨fun _ => hzs, fun _ => has⟩,
          ⟨fun h => absurd h hnat, fun h => absurd h hnzt⟩⟩
    · intro hodd
      have hqeven : q.length % 2 = 0 := by omega
      rcases ih.1 hqeven with ⟨hcs, hct⟩
      rcases hbip.mem_of_adj hadj with ⟨has, hct'⟩ | ⟨hat, hcs'⟩
      · exact Or.inl ⟨has, hct.mp hct'⟩
      · exact Or.inr ⟨hat, hcs.mp hcs'⟩

theorem bipartite_graph_dist_adj_ne {G : SimpleGraph V} (hbip : G.IsBipartite)
    (hconn : G.Connected) (t₀ : V) {u v : V} (hadj : G.Adj u v) :
    G.dist t₀ u ≠ G.dist t₀ v := by
  intro heq
  obtain ⟨s, t, hbw⟩ := hbip.exists_isBipartiteWith
  obtain ⟨pu, hpu⟩ := hconn.exists_walk_length_eq_dist t₀ u
  obtain ⟨pv, hpv⟩ := hconn.exists_walk_length_eq_dist t₀ v
  have hmod : pu.length % 2 = pv.length % 2 := by rw [hpu, hpv, heq]
  rcases Nat.mod_two_eq_zero_or_one pu.length with h0 | h1
  · have hu := (isBipartiteWith_walk_parity hbw pu).1 h0
    have hv := (isBipartiteWith_walk_parity hbw pv).1 (hmod ▸ h0)
    rcases hbw.mem_of_adj hadj with ⟨hus, hvt⟩ | ⟨hut, hvs⟩
    · have hts : t₀ ∈ s := hu.1.mpr hus
      have hvs' : v ∈ s := hv.1.mp hts
      exact Set.disjoint_left.mp hbw.disjoint hvs' hvt
    · have htt : t₀ ∈ t := hu.2.mpr hut
      have hvt' : v ∈ t := hv.2.mp htt
      exact Set.disjoint_left.mp hbw.disjoint hvs hvt'
  · have hu := (isBipartiteWith_walk_parity hbw pu).2 h1
    have hv := (isBipartiteWith_walk_parity hbw pv).2 (hmod ▸ h1)
    rcases hbw.mem_of_adj hadj with ⟨hus, hvt⟩ | ⟨hut, hvs⟩
    · rcases hu with ⟨hts, hut⟩ | ⟨htt, _⟩
      · exact Set.disjoint_left.mp hbw.disjoint hus hut
      · rcases hv with ⟨hts, _⟩ | ⟨_, hvs'⟩
        · exact Set.disjoint_left.mp hbw.disjoint hts htt
        · exact Set.disjoint_left.mp hbw.disjoint hvs' hvt
    · rcases hu with ⟨hts, hut'⟩ | ⟨htt, hus⟩
      · rcases hv with ⟨_, hvt'⟩ | ⟨htt', _⟩
        · exact Set.disjoint_left.mp hbw.disjoint hvs hvt'
        · exact Set.disjoint_left.mp hbw.disjoint hts htt'
      · exact Set.disjoint_left.mp hbw.disjoint hus hut

theorem bipartite_graph_dist_adj_succ {G : SimpleGraph V} (hbip : G.IsBipartite)
    (hconn : G.Connected) (t₀ : V) {u v : V} (hadj : G.Adj u v) :
    G.dist t₀ v = G.dist t₀ u + 1 ∨ G.dist t₀ u = G.dist t₀ v + 1 := by
  have hne := bipartite_graph_dist_adj_ne hbip hconn t₀ hadj
  have hdiff := hadj.diff_dist_adj (u := t₀)
  omega

theorem bipartite_dist_vertex_adj_diff [Finite V] {W : WeightedGraph V} (hbip : W.graph.IsBipartite)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ)
    (t₀ : V) {u v : V} (hadj : W.graph.Adj u v) :
    |Dist.dist (vertex t₀ : MetricGraph W) (vertex u) -
      Dist.dist (vertex t₀ : MetricGraph W) (vertex v)| = ℓ := by
  rw [dist_vertex_eq_of_const_weight hℓ hconst, dist_vertex_eq_of_const_weight hℓ hconst]
  rcases bipartite_graph_dist_adj_succ hbip W.connected t₀ hadj with h | h
  · rw [h, Nat.cast_add, Nat.cast_one]
    have hdiff : ℓ * (W.graph.dist t₀ u : ℝ) - ℓ * ((W.graph.dist t₀ u : ℝ) + 1) = -ℓ := by ring
    rw [hdiff, abs_neg, abs_of_pos hℓ]
  · rw [h, Nat.cast_add, Nat.cast_one]
    have hdiff : ℓ * ((W.graph.dist t₀ v : ℝ) + 1) - ℓ * (W.graph.dist t₀ v : ℝ) = ℓ := by ring
    rw [hdiff, abs_of_pos hℓ]

theorem bipartite_const_weight_dist_edgePoint_affine [Finite V] {W : WeightedGraph V}
    (hbip : W.graph.IsBipartite) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ)
    (t₀ : V) (d : W.graph.Dart) (s : unitInterval) :
    Dist.dist (vertex t₀ : MetricGraph W) (edgePoint d s) =
      (1 - (s : ℝ)) * Dist.dist (vertex t₀ : MetricGraph W) (vertex d.fst) +
        (s : ℝ) * Dist.dist (vertex t₀ : MetricGraph W) (vertex d.snd) := by
  have hw : W.weight d.edge = ℓ := hconst d.edge d.edge_mem
  rw [dist_vertex_edgePoint, hw,
    vertexDist_eq_of_const_weight hℓ hconst, vertexDist_eq_of_const_weight hℓ hconst,
    dist_vertex_eq_of_const_weight hℓ hconst, dist_vertex_eq_of_const_weight hℓ hconst]
  rcases bipartite_graph_dist_adj_succ hbip W.connected t₀ d.adj with h | h
  · rw [h, Nat.cast_add, Nat.cast_one]
    rw [min_eq_left (by nlinarith [hℓ, s.2.1, s.2.2])]
    ring
  · rw [h, Nat.cast_add, Nat.cast_one]
    rw [min_eq_right (by nlinarith [hℓ, s.2.1, s.2.2])]
    ring

theorem bipartite_equalLength_dist_edgePoint_affine [Finite V] {G : SimpleGraph V}
    (hbip : G.IsBipartite) (hconn : G.Connected) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (t₀ : V) (d : G.Dart) (s : unitInterval) :
    Dist.dist (vertex t₀ : MetricGraph (equalLength G hconn ℓ hℓ)) (edgePoint d s) =
      (1 - (s : ℝ)) *
          Dist.dist (vertex t₀ : MetricGraph (equalLength G hconn ℓ hℓ)) (vertex d.fst) +
        (s : ℝ) *
          Dist.dist (vertex t₀ : MetricGraph (equalLength G hconn ℓ hℓ)) (vertex d.snd) :=
  bipartite_const_weight_dist_edgePoint_affine
    (W := equalLength G hconn ℓ hℓ) hbip hℓ (fun _ _ => rfl) t₀ d s

/-! ### Midpoint subdivision of an equal-length graph -/

private noncomputable def halfUnit : unitInterval :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private theorem halfUnit_pos : (0 : ℝ) < halfUnit := by
  change (0 : ℝ) < 1 / 2; norm_num

private theorem halfUnit_lt_one : (halfUnit : ℝ) < 1 := by
  change (1 / 2 : ℝ) < 1; norm_num

open Classical in
/-- Finite set of all vertices together with the midpoint `edgePoint _ (1 / 2)` of each edge. -/
noncomputable def midpointPoints [Finite V] (W : WeightedGraph V) : Finset (MetricGraph W) :=
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  Finset.univ.image vertex ∪
    Finset.univ.image (fun e : W.graph.edgeSet => edgePoint (edgeDartOfSym2 e) halfUnit)

theorem vertex_mem_midpointPoints [Finite V] (W : WeightedGraph V) (v : V) :
    vertex v ∈ midpointPoints W := by
  classical
  simp only [midpointPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨v, rfl⟩

/-- The subdivision of `W` obtained by inserting the midpoint of every edge. -/
@[expose] noncomputable def midpointSubdivision [Finite V] (W : WeightedGraph V) :
    WeightedGraph { z : MetricGraph W // z ∈ midpointPoints W } :=
  subdivide W (midpointPoints W) (vertex_mem_midpointPoints W)

private theorem midpoint_ne_vertex (W : WeightedGraph V)
    (e : W.graph.edgeSet) (v : V) :
    edgePoint (edgeDartOfSym2 e) halfUnit ≠ vertex v := by
  intro h
  rcases edgePoint_eq_vertex_iff.mp h with ⟨h0, _⟩ | ⟨h1, _⟩
  · exact halfUnit_pos.ne' (congrArg Subtype.val h0)
  · exact halfUnit_lt_one.ne (congrArg Subtype.val h1)

private theorem mem_midpointPoints_on_dart_iff [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (u : unitInterval) :
    edgePoint (edgeDartOfSym2 e) u ∈ midpointPoints W ↔
      u = 0 ∨ u = halfUnit ∨ u = 1 := by
  constructor
  · intro hu
    classical
    simp only [midpointPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hu
    rcases hu with ⟨v, hv⟩ | ⟨e', he'⟩
    · rcases edgePoint_eq_vertex_iff.mp hv.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · obtain ⟨rfl, rfl⟩ :=
        (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo halfUnit_pos halfUnit_lt_one).mp he'.symm
      exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | rfl)
    · rw [edgePoint_zero]
      exact vertex_mem_midpointPoints W _
    · classical
      simp only [midpointPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨e, rfl⟩
    · rw [edgePoint_one]
      exact vertex_mem_midpointPoints W _

private theorem midpoint_forward_cases [Finite V] (W : WeightedGraph V)
    {e : W.graph.edgeSet} {s t : unitInterval} (hst : (s : ℝ) < t)
    (hs : edgePoint (edgeDartOfSym2 e) s ∈ midpointPoints W)
    (ht : edgePoint (edgeDartOfSym2 e) t ∈ midpointPoints W)
    (hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
      edgePoint (edgeDartOfSym2 e) r ∉ midpointPoints W) :
    (s = 0 ∧ t = halfUnit) ∨ (s = halfUnit ∧ t = 1) := by
  have hs' := (mem_midpointPoints_on_dart_iff W e s).mp hs
  have ht' := (mem_midpointPoints_on_dart_iff W e t).mp ht
  have hmid : edgePoint (edgeDartOfSym2 e) halfUnit ∈ midpointPoints W :=
    (mem_midpointPoints_on_dart_iff W e halfUnit).mpr (Or.inr (Or.inl rfl))
  rcases hs' with rfl | rfl | rfl
  · rcases ht' with rfl | rfl | rfl
    · exact absurd hst (lt_irrefl _)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd hmid (hno halfUnit halfUnit_pos halfUnit_lt_one)
  · rcases ht' with rfl | rfl | rfl
    · exact absurd (halfUnit_pos.trans hst) (lt_irrefl _)
    · exact absurd hst (lt_irrefl _)
    · exact Or.inr ⟨rfl, rfl⟩
  · rcases ht' with rfl | rfl | rfl
    · exact absurd ((halfUnit_pos.trans halfUnit_lt_one).trans hst) (lt_irrefl _)
    · exact absurd (halfUnit_lt_one.trans hst) (lt_irrefl _)
    · exact absurd hst (lt_irrefl _)

private theorem midpoint_witness_diff [Finite V] (W : WeightedGraph V)
    {x y : { z : MetricGraph W // z ∈ midpointPoints W }}
    {d : W.graph.Dart} {s t : unitInterval} (hst : (s : ℝ) < t)
    (hs : edgePoint d s = x.1) (ht : edgePoint d t = y.1)
    (hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
      edgePoint d r ∉ midpointPoints W) :
    ((t : ℝ) - s = 1 / 2) ∧
      (((∃ v : V, x.1 = vertex v) ∧ (∃ e : W.graph.edgeSet,
          y.1 = edgePoint (edgeDartOfSym2 e) halfUnit)) ∨
       ((∃ e : W.graph.edgeSet, x.1 = edgePoint (edgeDartOfSym2 e) halfUnit) ∧
          (∃ v : V, y.1 = vertex v))) := by
  let e : W.graph.edgeSet := ⟨d.edge, d.edge_mem⟩
  have he : d.edge = (edgeDartOfSym2 e).edge := (edgeDartOfSym2_edge e).symm
  rcases (dart_edge_eq_iff d (edgeDartOfSym2 e)).mp he with hd | hsym
  · have hsB : edgePoint (edgeDartOfSym2 e) s ∈ midpointPoints W := by rw [← hd, hs]; exact x.2
    have htB : edgePoint (edgeDartOfSym2 e) t ∈ midpointPoints W := by rw [← hd, ht]; exact y.2
    have hno' : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
        edgePoint (edgeDartOfSym2 e) r ∉ midpointPoints W := by
      intro r hr1 hr2; rw [← hd]; exact hno r hr1 hr2
    rcases midpoint_forward_cases W hst hsB htB hno' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by change (1 / 2 : ℝ) - 0 = 1 / 2; norm_num, Or.inl ⟨?_, ?_⟩⟩
      · exact ⟨(edgeDartOfSym2 e).fst, by rw [← hs, hd, edgePoint_zero]⟩
      · exact ⟨e, by rw [← ht, hd]⟩
    · refine ⟨by change 1 - (1 / 2 : ℝ) = 1 / 2; norm_num, Or.inr ⟨?_, ?_⟩⟩
      · exact ⟨e, by rw [← hs, hd]⟩
      · exact ⟨(edgeDartOfSym2 e).snd, by rw [← ht, hd, edgePoint_one]⟩
  · let s' := unitInterval.symm t
    let t' := unitInterval.symm s
    have hst' : (s' : ℝ) < t' := by change 1 - (t : ℝ) < 1 - s; linarith
    have hsB : edgePoint (edgeDartOfSym2 e) s' ∈ midpointPoints W := by
      rw [edgePoint_symm', ← hsym, ht]; exact y.2
    have htB : edgePoint (edgeDartOfSym2 e) t' ∈ midpointPoints W := by
      rw [edgePoint_symm', ← hsym, hs]; exact x.2
    have hno' : ∀ r : unitInterval, (s' : ℝ) < r → (r : ℝ) < t' →
        edgePoint (edgeDartOfSym2 e) r ∉ midpointPoints W := by
      intro r hr1 hr2
      change 1 - (t : ℝ) < r at hr1
      change (r : ℝ) < 1 - s at hr2
      have hsr : (s : ℝ) < (unitInterval.symm r : ℝ) := by change (s : ℝ) < 1 - r; linarith
      have hrt : (unitInterval.symm r : ℝ) < t := by change 1 - (r : ℝ) < t; linarith
      have h := hno (unitInterval.symm r) hsr hrt
      rwa [hsym, edgePoint_symm] at h
    have hdiff : (t : ℝ) - s = (t' : ℝ) - s' := by
      change (t : ℝ) - s = (1 - (s : ℝ)) - (1 - t); ring
    rcases midpoint_forward_cases W hst' hsB htB hno' with ⟨hs'0, ht'h⟩ | ⟨hs'h, ht'1⟩
    · have ht1 : t = 1 := by
        ext
        have hval : (s' : ℝ) = 1 - (t : ℝ) := rfl
        rw [hs'0] at hval
        change (0 : ℝ) = 1 - (t : ℝ) at hval
        change (t : ℝ) = 1
        linarith
      refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hdiff, hs'0, ht'h]; change (1 / 2 : ℝ) - 0 = 1 / 2; norm_num
      · refine ⟨e, ?_⟩
        rw [← hs, hsym, ← edgePoint_symm']
        change edgePoint (edgeDartOfSym2 e) t' = edgePoint (edgeDartOfSym2 e) halfUnit
        rw [ht'h]
      · refine ⟨(edgeDartOfSym2 e).fst, ?_⟩
        rw [← ht, ht1, hsym, edgePoint_one]
        rfl
    · have hs0 : s = 0 := by
        ext
        have hval : (t' : ℝ) = 1 - (s : ℝ) := rfl
        rw [ht'1] at hval
        change (1 : ℝ) = 1 - (s : ℝ) at hval
        change (s : ℝ) = 0
        linarith
      refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
      · rw [hdiff, hs'h, ht'1]; change 1 - (1 / 2 : ℝ) = 1 / 2; norm_num
      · refine ⟨(edgeDartOfSym2 e).snd, ?_⟩
        rw [← hs, hs0, hsym, edgePoint_zero]
        rfl
      · refine ⟨e, ?_⟩
        rw [← ht, hsym, ← edgePoint_symm']
        change edgePoint (edgeDartOfSym2 e) s' = edgePoint (edgeDartOfSym2 e) halfUnit
        rw [hs'h]

theorem midpointSubdivision_isBipartite [Finite V] (W : WeightedGraph V) :
    (midpointSubdivision W).graph.IsBipartite := by
  let S : Set { z : MetricGraph W // z ∈ midpointPoints W } := { x | ∃ v : V, x.1 = vertex v }
  let T : Set { z : MetricGraph W // z ∈ midpointPoints W } :=
    { x | ∃ e : W.graph.edgeSet, x.1 = edgePoint (edgeDartOfSym2 e) halfUnit }
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro x ⟨v, hv⟩ ⟨e, he⟩
    exact midpoint_ne_vertex W e v (he.symm.trans hv)
  have hbw : (midpointSubdivision W).graph.IsBipartiteWith S T :=
    { disjoint := hdisj
      mem_of_adj := fun _ _ hadj => by
        dsimp only [midpointSubdivision] at hadj
        rw [subdivide_adj_iff] at hadj
        dsimp only [SubAdj] at hadj
        rcases hadj with ⟨_, d, s, t, hst, hs, ht, hno⟩
        exact (midpoint_witness_diff W hst hs ht hno).2 }
  exact hbw.isBipartite

theorem midpointSubdivision_weight_eq [Finite V] {W : WeightedGraph V} {ℓ : ℝ}
    (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ)
    {e' : Sym2 { z : MetricGraph W // z ∈ midpointPoints W }}
    (he' : e' ∈ (midpointSubdivision W).graph.edgeSet) :
    (midpointSubdivision W).weight e' = ℓ / 2 := by
  let d' : (subdivide W (midpointPoints W) (vertex_mem_midpointPoints W)).graph.Dart :=
    edgeDartOfSym2 ⟨e', he'⟩
  have he_eq : d'.edge = e' := edgeDartOfSym2_edge ⟨e', he'⟩
  obtain ⟨d, s, t, hst, hs, ht, hno, hw, _⟩ :=
    subdivideEquiv_edgePoint (vertex_mem_midpointPoints W) d' 0
  obtain ⟨hdiff, _⟩ := midpoint_witness_diff W hst hs ht hno
  dsimp only [midpointSubdivision]
  rw [← he_eq, hw, hdiff, hconst d.edge d.edge_mem]
  ring

theorem midpointSubdivision_dist_edgePoint_affine [Finite V] {W : WeightedGraph V} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hconst : ∀ e ∈ W.graph.edgeSet, W.weight e = ℓ)
    (t₀ : { z : MetricGraph W // z ∈ midpointPoints W })
    (d' : (midpointSubdivision W).graph.Dart) (s : unitInterval) :
    Dist.dist (vertex t₀ : MetricGraph (midpointSubdivision W)) (edgePoint d' s) =
      (1 - (s : ℝ)) *
          Dist.dist (vertex t₀ : MetricGraph (midpointSubdivision W)) (vertex d'.fst) +
        (s : ℝ) *
          Dist.dist (vertex t₀ : MetricGraph (midpointSubdivision W)) (vertex d'.snd) :=
  bipartite_const_weight_dist_edgePoint_affine
    (midpointSubdivision_isBipartite W) (half_pos hℓ)
    (fun _ he => midpointSubdivision_weight_eq hconst he) t₀ d' s

end MetricGraph

end SimpleGraph
