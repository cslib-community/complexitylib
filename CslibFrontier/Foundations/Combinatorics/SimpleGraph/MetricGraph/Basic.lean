/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UnitInterval
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Continuous metric graphs

Given a finite connected simple graph `G` on `V` with positive edge weights `w : Sym2 V → ℝ`,
`SimpleGraph.MetricGraph` turns `(G, w)` into a compact geodesic `MetricSpace` by gluing an edge
segment isometric to `[0, w e]` for each edge `e` of `G` at its endpoint vertices.

The discrete shortest-path distance `SimpleGraph.vertexDist G w u v` is the minimum of
`SimpleGraph.walkLength w p` over all walks `p : G.Walk u v` (attained by a simple path when `V`
is finite and edge weights are nonnegative). The distance on `SimpleGraph.MetricGraph W` is given
in closed form from `vertexDist` and the local edge coordinates, yielding `MetricSpace` and
`CompactSpace` instances directly.

## Main definitions

* `SimpleGraph.walkLength`: the sum of edge weights along a walk.
* `SimpleGraph.vertexDist`: the shortest-path distance between vertices under real edge weights.
* `SimpleGraph.WeightedGraph`: a connected simple graph equipped with positive edge weights.
* `SimpleGraph.MetricGraph`: the continuous metric space realization of a `WeightedGraph`.
* `SimpleGraph.MetricGraph.vertex`: the embedding of vertices into `MetricGraph`.
* `SimpleGraph.MetricGraph.edgePoint`: the point along a dart at parameter `t : unitInterval`.
* `SimpleGraph.MetricGraph.lift`: universal property for defining functions out of `MetricGraph`.

## Main results

* `SimpleGraph.exists_isPath_walkLength_eq_vertexDist`: shortest walks between reachable vertices
  are attained by simple paths on finite graphs with nonnegative weights.
* `SimpleGraph.MetricGraph.instMetricSpace`: `MetricGraph W` is a `MetricSpace`.
* `SimpleGraph.MetricGraph.instCompactSpace`: `MetricGraph W` is a `CompactSpace`.
* `SimpleGraph.MetricGraph.dist_vertex`: distances between vertices equal `vertexDist`.
* `SimpleGraph.MetricGraph.dist_vertex_edgePoint`: closed-form distance from a vertex to an edge
  point.
* `SimpleGraph.MetricGraph.dist_edgePoint_edgePoint_of_edge_ne`,
  `SimpleGraph.MetricGraph.dist_edgePoint_edgePoint_same`: closed-form distances between edge
  points.
-/

public section

open scoped unitInterval

namespace SimpleGraph

universe u

section WalkLength

variable {V : Type u} {G : SimpleGraph V}

/-- The total weight of a walk, summing edge weights with multiplicity. -/
@[expose] def walkLength (w : Sym2 V → ℝ) {u v : V} (p : G.Walk u v) : ℝ :=
  (p.edges.map w).sum

variable (w : Sym2 V → ℝ)

@[simp]
theorem walkLength_nil {u : V} : walkLength w (Walk.nil : G.Walk u u) = 0 := rfl

@[simp]
theorem walkLength_cons {u v x : V} (h : G.Adj u v) (p : G.Walk v x) :
    walkLength w (Walk.cons h p) = w s(u, v) + walkLength w p := by
  simp [walkLength]

theorem walkLength_toWalk {u v : V} (h : G.Adj u v) : walkLength w h.toWalk = w s(u, v) := by
  simp [walkLength]

theorem walkLength_append {u v x : V} (p : G.Walk u v) (q : G.Walk v x) :
    walkLength w (p.append q) = walkLength w p + walkLength w q := by
  simp [walkLength, Walk.edges_append]

theorem walkLength_reverse {u v : V} (p : G.Walk u v) :
    walkLength w p.reverse = walkLength w p := by
  simp [walkLength, Walk.edges_reverse]

theorem walkLength_nonneg {u v : V} (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b))
    (p : G.Walk u v) : 0 ≤ walkLength w p := by
  induction p with
  | nil => simp
  | cons h _ ih => exact add_nonneg (hw h) ih

theorem walkLength_bypass_le {u v : V} [DecidableEq V]
    (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b)) (p : G.Walk u v) :
    walkLength w p.bypass ≤ walkLength w p := by
  unfold walkLength
  refine List.Sublist.sum_le_sum (p.edges_bypass_sublist_edges.map w) fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  induction e using Sym2.ind with
  | _ a b => exact hw (p.edges_subset_edgeSet he)

end WalkLength

section VertexDist

variable {V : Type u} (G : SimpleGraph V) (w : Sym2 V → ℝ)

/-- The shortest-path distance between two vertices in `G` under edge weights `w` (`0` if
unreachable). -/
noncomputable def vertexDist (u v : V) : ℝ :=
  sInf { c : ℝ | ∃ p : G.Walk u v, walkLength w p = c }

variable {G w}

theorem vertexDist_le (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b))
    {u v : V} (p : G.Walk u v) : vertexDist G w u v ≤ walkLength w p := by
  refine csInf_le ⟨0, ?_⟩ ⟨p, rfl⟩
  rintro _ ⟨q, rfl⟩
  exact walkLength_nonneg w hw q

theorem vertexDist_nonneg (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b)) (u v : V) :
    0 ≤ vertexDist G w u v := by
  by_cases hne : (Set.Nonempty { c : ℝ | ∃ p : G.Walk u v, walkLength w p = c })
  · exact le_csInf hne fun _ ⟨p, hp⟩ => hp ▸ walkLength_nonneg w hw p
  · rw [vertexDist, Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

@[simp]
theorem vertexDist_self (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b)) (u : V) :
    vertexDist G w u u = 0 :=
  le_antisymm ((vertexDist_le hw Walk.nil).trans_eq (walkLength_nil w))
    (vertexDist_nonneg hw u u)

theorem vertexDist_adj_le (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b))
    {u v : V} (h : G.Adj u v) : vertexDist G w u v ≤ w s(u, v) :=
  (vertexDist_le hw h.toWalk).trans_eq (walkLength_toWalk w h)

theorem vertexDist_comm (u v : V) : vertexDist G w u v = vertexDist G w v u := by
  have heq : { c : ℝ | ∃ p : G.Walk u v, walkLength w p = c } =
      { c : ℝ | ∃ p : G.Walk v u, walkLength w p = c } := by
    ext c
    exact ⟨fun ⟨p, hp⟩ => ⟨p.reverse, (walkLength_reverse w p).trans hp⟩,
      fun ⟨p, hp⟩ => ⟨p.reverse, (walkLength_reverse w p).trans hp⟩⟩
  simp only [vertexDist, heq]

theorem vertexDist_triangle {u v x : V} (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b))
    (h1 : G.Reachable u v) (h2 : G.Reachable v x) :
    vertexDist G w u x ≤ vertexDist G w u v + vertexDist G w v x := by
  have hS1 : { c : ℝ | ∃ p : G.Walk u v, walkLength w p = c }.Nonempty :=
    let ⟨p⟩ := h1; ⟨_, p, rfl⟩
  have hS2 : { c : ℝ | ∃ q : G.Walk v x, walkLength w q = c }.Nonempty :=
    let ⟨q⟩ := h2; ⟨_, q, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨c₁, ⟨p, rfl⟩, hc₁⟩ := exists_lt_of_csInf_lt hS1 (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨c₂, ⟨q, rfl⟩, hc₂⟩ := exists_lt_of_csInf_lt hS2 (lt_add_of_pos_right _ (half_pos hε))
  change walkLength w p < vertexDist G w u v + ε / 2 at hc₁
  change walkLength w q < vertexDist G w v x + ε / 2 at hc₂
  have htri : vertexDist G w u x ≤ walkLength w p + walkLength w q :=
    (vertexDist_le hw (p.append q)).trans_eq (walkLength_append w p q)
  linarith

/-- On a finite graph with nonnegative edge weights, every reachable pair of vertices has a
simple path achieving `vertexDist`. -/
theorem exists_isPath_walkLength_eq_vertexDist [Finite V]
    (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 ≤ w s(a, b)) {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ walkLength w p = vertexDist G w u v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let f : { p : G.Walk u v // p.IsPath } →
      Fin (Fintype.card V) × (Fin (Fintype.card V) → V) :=
    fun p => (⟨p.1.length, p.2.length_lt⟩, fun i => p.1.getVert i)
  have hf : Function.Injective f := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    have hlen : p.length = q.length := by simpa [f] using Fin.ext_iff.mp hfst
    refine Subtype.ext (Walk.ext_support (List.ext_getElem (by simp [hlen]) fun i hi1 _ => ?_))
    have hi : i < Fintype.card V := by
      simp only [Walk.length_support] at hi1
      exact lt_of_lt_of_le hi1 hp.length_lt
    have hget := congrFun hsnd ⟨i, hi⟩
    simpa only [f, Walk.support_getElem_eq_getVert] using hget
  have hfinType : Finite { p : G.Walk u v // p.IsPath } := Finite.of_injective f hf
  obtain ⟨p₀⟩ := hr
  let S := Set.range fun p : { p : G.Walk u v // p.IsPath } => walkLength w p.1
  have hne : S.Nonempty := ⟨_, ⟨p₀.bypass, p₀.bypass_isPath⟩, rfl⟩
  have hfin : S.Finite := Set.finite_range _
  have hmem : sInf S ∈ S := hfin.isClosed.csInf_mem hne hfin.bddBelow
  obtain ⟨⟨p, hp⟩, hpeq⟩ := hmem
  refine ⟨p, hp, hpeq.trans (le_antisymm ?_ ?_)⟩
  · refine le_csInf ⟨_, p₀, rfl⟩ ?_
    rintro _ ⟨q, rfl⟩
    exact (csInf_le hfin.bddBelow ⟨⟨q.bypass, q.bypass_isPath⟩, rfl⟩).trans
      (walkLength_bypass_le w hw q)
  · refine le_csInf hne ?_
    rintro _ ⟨⟨q, _⟩, rfl⟩
    exact vertexDist_le hw q

theorem vertexDist_pos_of_ne [Finite V] (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 < w s(a, b))
    {u v : V} (hr : G.Reachable u v) (hne : u ≠ v) : 0 < vertexDist G w u v := by
  obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist (fun a b h => (hw h).le) hr
  rw [← hp]
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    rw [walkLength_cons]
    have hq := walkLength_nonneg w (fun a b h => (hw h).le) q
    linarith [hw hadj]

theorem vertexDist_eq_zero_iff [Finite V] (hw : ∀ ⦃a b : V⦄, G.Adj a b → 0 < w s(a, b))
    {u v : V} (hr : G.Reachable u v) : vertexDist G w u v = 0 ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ vertexDist_self (fun a b hab => (hw hab).le) u⟩
  by_contra hne
  exact (vertexDist_pos_of_ne hw hr hne).ne' h

end VertexDist

/-- A connected simple graph equipped with positive real edge weights. -/
structure WeightedGraph (V : Type u) where
  /-- The underlying simple graph. -/
  graph : SimpleGraph V
  /-- Positive real edge lengths on `Sym2 V`. -/
  weight : Sym2 V → ℝ
  /-- Every edge has strictly positive length. -/
  weight_pos : ∀ ⦃u v : V⦄, graph.Adj u v → 0 < weight s(u, v)
  /-- The underlying graph is connected. -/
  connected : graph.Connected

namespace WeightedGraph

variable {V : Type u} (W : WeightedGraph V)

theorem weight_nonneg ⦃u v : V⦄ (h : W.graph.Adj u v) : 0 ≤ W.weight s(u, v) :=
  (W.weight_pos h).le

theorem dart_weight_pos (d : W.graph.Dart) : 0 < W.weight d.edge :=
  W.weight_pos d.adj

theorem dart_weight_nonneg (d : W.graph.Dart) : 0 ≤ W.weight d.edge :=
  (W.dart_weight_pos d).le

end WeightedGraph

/-! ### Raw points and equivalence relation -/

private inductive RawPoint {V : Type u} (G : SimpleGraph V) : Type u
  | vertex : V → RawPoint G
  | edge : G.Dart → unitInterval → RawPoint G

private noncomputable def RawPoint.toVertex? {V : Type u} {G : SimpleGraph V} :
    RawPoint G → Option V
  | .vertex v => some v
  | .edge d t => if t = 0 then some d.fst else if t = 1 then some d.snd else none

private def rawRel {V : Type u} {G : SimpleGraph V} (p q : RawPoint G) : Prop :=
  match p.toVertex?, q.toVertex? with
  | some u, some v => u = v
  | none, none =>
    ∃ d₁ t₁ d₂ t₂, p = .edge d₁ t₁ ∧ q = .edge d₂ t₂ ∧
      ((d₁ = d₂ ∧ t₁ = t₂) ∨ (d₁ = d₂.symm ∧ t₁ = unitInterval.symm t₂))
  | _, _ => False

private theorem rawRel_equivalence {V : Type u} (G : SimpleGraph V) :
    Equivalence (rawRel (G := G)) where
  refl p := by
    unfold rawRel
    cases hp : p.toVertex? with
    | some u => rfl
    | none =>
      cases p with
      | vertex v => simp [RawPoint.toVertex?] at hp
      | edge d t => exact ⟨d, t, d, t, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  symm {p q} h := by
    unfold rawRel at h ⊢
    cases hp : p.toVertex? <;> cases hq : q.toVertex? <;> simp only [hp, hq] at h ⊢
    · obtain ⟨d₁, t₁, d₂, t₂, rfl, rfl, hpair⟩ := h
      refine ⟨d₂, t₂, d₁, t₁, rfl, rfl, ?_⟩
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨(Dart.symm_symm _).symm, (unitInterval.symm_symm _).symm⟩
    · exact h.symm
  trans {p q r} hpq hqr := by
    unfold rawRel at hpq hqr ⊢
    cases hp : p.toVertex? <;> cases hq : q.toVertex? <;> cases hr : r.toVertex? <;>
      simp only [hp, hq, hr] at hpq hqr ⊢
    · obtain ⟨d₁, t₁, d₂, t₂, rfl, hq1, h12⟩ := hpq
      obtain ⟨d₂', t₂', d₃, t₃, hq2, rfl, h23⟩ := hqr
      have hqt := hq1.symm.trans hq2
      injection hqt with hd ht
      subst hd ht
      refine ⟨d₁, t₁, d₃, t₃, rfl, rfl, ?_⟩
      rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨Dart.symm_symm _, unitInterval.symm_symm _⟩
    · exact hpq.trans hqr

private def rawSetoid {V : Type u} (G : SimpleGraph V) : Setoid (RawPoint G) :=
  ⟨rawRel, rawRel_equivalence G⟩

private def RawPoint.endV {V : Type u} {G : SimpleGraph V} : Bool → RawPoint G → V
  | false, .vertex v => v
  | true, .vertex v => v
  | false, .edge d _ => d.fst
  | true, .edge d _ => d.snd

private def RawPoint.endOff {V : Type u} (W : WeightedGraph V) : Bool → RawPoint W.graph → ℝ
  | false, .vertex _ => 0
  | true, .vertex _ => 0
  | false, .edge d t => (t : ℝ) * W.weight d.edge
  | true, .edge d t => (1 - (t : ℝ)) * W.weight d.edge

private theorem RawPoint.endOff_nonneg {V : Type u} (W : WeightedGraph V) (b : Bool)
    (p : RawPoint W.graph) : 0 ≤ p.endOff W b := by
  cases p with
  | vertex _ => cases b <;> exact le_rfl
  | edge d t =>
    cases b
    · exact mul_nonneg t.2.1 (W.dart_weight_nonneg d)
    · exact mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d)

private theorem RawPoint.vertexDist_endV_le {V : Type u} (W : WeightedGraph V) (a b : Bool)
    (p : RawPoint W.graph) :
    vertexDist W.graph W.weight (p.endV a) (p.endV b) ≤ p.endOff W a + p.endOff W b := by
  cases p with
  | vertex v =>
    cases a <;> cases b <;>
      simp only [RawPoint.endV, RawPoint.endOff, vertexDist_self W.weight_nonneg, add_zero, le_refl]
  | edge d t =>
    have hsum : (t : ℝ) * W.weight d.edge + (1 - (t : ℝ)) * W.weight d.edge = W.weight d.edge := by
      ring
    cases a <;> cases b <;> simp only [RawPoint.endV, RawPoint.endOff]
    · simp only [vertexDist_self W.weight_nonneg]
      exact add_nonneg (mul_nonneg t.2.1 (W.dart_weight_nonneg d))
        (mul_nonneg t.2.1 (W.dart_weight_nonneg d))
    · rw [hsum]
      exact vertexDist_adj_le W.weight_nonneg d.adj
    · rw [add_comm, hsum]
      exact (vertexDist_adj_le W.weight_nonneg d.adj.symm).trans_eq (congrArg W.weight Sym2.eq_swap)
    · simp only [vertexDist_self W.weight_nonneg]
      exact add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d))
        (mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d))

/-- The continuous metric graph associated with a finite connected edge-weighted simple graph `W`.
Points are vertices `MetricGraph.vertex v` and points along edges `MetricGraph.edgePoint d t`,
glued at shared endpoints and under dart reversal `d.symm` with `t ↦ 1 - t`. -/
def MetricGraph {V : Type u} (W : WeightedGraph V) : Type u :=
  Quotient (rawSetoid W.graph)

namespace MetricGraph

variable {V : Type u} {W : WeightedGraph V}

/-- Embed a vertex of `W` into `MetricGraph W`. -/
def vertex (v : V) : MetricGraph W :=
  Quotient.mk (rawSetoid W.graph) (.vertex v)

/-- The point on dart `d` at parameter `t : unitInterval` (`0` is `d.fst`, `1` is `d.snd`). -/
def edgePoint (d : W.graph.Dart) (t : unitInterval) : MetricGraph W :=
  Quotient.mk (rawSetoid W.graph) (.edge d t)

/-- Convenience constructor for a point on the edge `s(u, v)` at parameter `t : unitInterval`. -/
def point {u v : V} (hadj : W.graph.Adj u v) (t : unitInterval) : MetricGraph W :=
  edgePoint ⟨(u, v), hadj⟩ t

/-- Universal property of `MetricGraph W`: a map out of vertices and darts that agrees at
endpoints and under dart reversal descends to `MetricGraph W`. -/
def lift {α : Sort*} (fV : V → α) (fE : W.graph.Dart → unitInterval → α)
    (h0 : ∀ d, fE d 0 = fV d.fst) (h1 : ∀ d, fE d 1 = fV d.snd)
    (hsymm : ∀ d t, fE d.symm (unitInterval.symm t) = fE d t) :
    MetricGraph W → α :=
  Quotient.lift (fun p => match p with | .vertex v => fV v | .edge d t => fE d t) (by
    intro p q hpq
    change rawRel p q at hpq
    unfold rawRel at hpq
    cases hp : p.toVertex? with
    | some u =>
      cases hq : q.toVertex? with
      | none => simp [hp, hq] at hpq
      | some v =>
        simp only [hp, hq] at hpq
        subst hpq
        have eval_some : ∀ r : RawPoint W.graph, r.toVertex? = some u →
            (match r with | .vertex v => fV v | .edge d t => fE d t) = fV u := by
          intro r hr
          cases r with
          | vertex w => simp only [RawPoint.toVertex?, Option.some.injEq] at hr; subst hr; rfl
          | edge d t =>
            simp only [RawPoint.toVertex?] at hr
            split_ifs at hr with ht0 ht1
            · subst ht0; simp only [Option.some.injEq] at hr; subst hr; exact h0 d
            · subst ht1; simp only [Option.some.injEq] at hr; subst hr; exact h1 d
        exact (eval_some p hp).trans (eval_some q hq).symm
    | none =>
      cases hq : q.toVertex? with
      | some v => simp [hp, hq] at hpq
      | none =>
        simp only [hp, hq] at hpq
        obtain ⟨d₁, t₁, d₂, t₂, rfl, rfl, hpair⟩ := hpq
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact hsymm d₂ t₂)

@[simp]
theorem lift_vertex {α : Sort*} (fV : V → α) (fE : W.graph.Dart → unitInterval → α)
    (h0 : ∀ d, fE d 0 = fV d.fst) (h1 : ∀ d, fE d 1 = fV d.snd)
    (hsymm : ∀ d t, fE d.symm (unitInterval.symm t) = fE d t) (v : V) :
    lift fV fE h0 h1 hsymm (vertex v) = fV v := by
  unfold lift vertex
  rfl

@[simp]
theorem lift_edgePoint {α : Sort*} (fV : V → α) (fE : W.graph.Dart → unitInterval → α)
    (h0 : ∀ d, fE d 0 = fV d.fst) (h1 : ∀ d, fE d 1 = fV d.snd)
    (hsymm : ∀ d t, fE d.symm (unitInterval.symm t) = fE d t)
    (d : W.graph.Dart) (t : unitInterval) :
    lift fV fE h0 h1 hsymm (edgePoint d t) = fE d t := by
  unfold lift edgePoint
  rfl

@[simp]
theorem edgePoint_zero (d : W.graph.Dart) : edgePoint d 0 = (vertex d.fst : MetricGraph W) :=
  Quotient.sound (show rawRel _ _ by simp [rawRel, RawPoint.toVertex?])

@[simp]
theorem edgePoint_one (d : W.graph.Dart) : edgePoint d 1 = (vertex d.snd : MetricGraph W) :=
  Quotient.sound (show rawRel _ _ by simp [rawRel, RawPoint.toVertex?])

theorem edgePoint_symm (d : W.graph.Dart) (t : unitInterval) :
    edgePoint d.symm (unitInterval.symm t) = (edgePoint d t : MetricGraph W) := by
  refine Quotient.sound (show rawRel _ _ from ?_)
  by_cases ht0 : t = 0
  · subst ht0
    simp [rawRel, RawPoint.toVertex?]
  · by_cases ht1 : t = 1
    · subst ht1
      simp [rawRel, RawPoint.toVertex?]
    · have hs0 : unitInterval.symm t ≠ 0 := by simp [ht1]
      have hs1 : unitInterval.symm t ≠ 1 := by simp [ht0]
      simp only [rawRel, RawPoint.toVertex?, ht0, ht1, hs0, hs1, ↓reduceIte]
      exact ⟨d.symm, unitInterval.symm t, d, t, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem edgePoint_symm' (d : W.graph.Dart) (t : unitInterval) :
    edgePoint d (unitInterval.symm t) = (edgePoint d.symm t : MetricGraph W) := by
  rw [← edgePoint_symm d.symm t, Dart.symm_symm]

@[elab_as_elim]
theorem ind {motive : MetricGraph W → Prop}
    (vertex : ∀ v, motive (vertex v))
    (edgePoint : ∀ d (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → motive (edgePoint d t))
    (x : MetricGraph W) : motive x := by
  refine Quotient.ind (fun p => ?_) x
  cases p with
  | vertex v => exact vertex v
  | edge d t =>
    by_cases ht0 : t = 0
    · subst ht0
      change motive (MetricGraph.edgePoint d 0)
      simpa only [edgePoint_zero] using vertex d.fst
    · by_cases ht1 : t = 1
      · subst ht1
        change motive (MetricGraph.edgePoint d 1)
        simpa only [edgePoint_one] using vertex d.snd
      · have h0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm))
        have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht1 (Subtype.ext h))
        exact edgePoint d t h0 h1

theorem ind_simple {motive : MetricGraph W → Prop}
    (vertex : ∀ v, motive (vertex v))
    (edgePoint : ∀ d (t : unitInterval), motive (edgePoint d t))
    (x : MetricGraph W) : motive x :=
  ind vertex (fun d t _ _ => edgePoint d t) x

instance : Nonempty (MetricGraph W) :=
  ⟨vertex W.connected.nonempty.some⟩

theorem vertex_injective : Function.Injective (vertex (W := W)) := by
  intro u v h
  have hrel : rawRel (.vertex u : RawPoint W.graph) (.vertex v) := Quotient.exact h
  simpa [rawRel, RawPoint.toVertex?] using hrel

@[simp]
theorem vertex_inj {u v : V} : (vertex u : MetricGraph W) = vertex v ↔ u = v :=
  vertex_injective.eq_iff

theorem edgePoint_eq_vertex_iff {d : W.graph.Dart} {t : unitInterval} {v : V} :
    (edgePoint d t : MetricGraph W) = vertex v ↔ (t = 0 ∧ v = d.fst) ∨ (t = 1 ∧ v = d.snd) := by
  constructor
  · intro h
    have hrel : rawRel (.edge d t) (.vertex v) := Quotient.exact h
    simp only [rawRel, RawPoint.toVertex?] at hrel
    split_ifs at hrel with ht0 ht1
    · exact Or.inl ⟨ht0, hrel.symm⟩
    · exact Or.inr ⟨ht1, hrel.symm⟩
    · exact False.elim hrel
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact edgePoint_zero d
    · exact edgePoint_one d

theorem edgePoint_eq_edgePoint_iff {d₁ d₂ : W.graph.Dart} {t₁ t₂ : unitInterval} :
    (edgePoint d₁ t₁ : MetricGraph W) = edgePoint d₂ t₂ ↔
      (t₁ = 0 ∧ (t₂ = 0 ∧ d₁.fst = d₂.fst ∨ t₂ = 1 ∧ d₁.fst = d₂.snd)) ∨
      (t₁ = 1 ∧ (t₂ = 0 ∧ d₁.snd = d₂.fst ∨ t₂ = 1 ∧ d₁.snd = d₂.snd)) ∨
      (0 < (t₁ : ℝ) ∧ (t₁ : ℝ) < 1 ∧ 0 < (t₂ : ℝ) ∧ (t₂ : ℝ) < 1 ∧
        ((d₁ = d₂ ∧ t₁ = t₂) ∨ (d₁ = d₂.symm ∧ t₁ = unitInterval.symm t₂))) := by
  constructor
  · intro h
    have hrel : rawRel (.edge d₁ t₁) (.edge d₂ t₂) := Quotient.exact h
    by_cases ht10 : t₁ = 0
    · subst ht10
      rw [edgePoint_zero, eq_comm, edgePoint_eq_vertex_iff] at h
      exact Or.inl ⟨rfl, h⟩
    · by_cases ht11 : t₁ = 1
      · subst ht11
        rw [edgePoint_one, eq_comm, edgePoint_eq_vertex_iff] at h
        exact Or.inr (Or.inl ⟨rfl, h⟩)
      · have h01 : 0 < (t₁ : ℝ) ∧ (t₁ : ℝ) < 1 :=
          ⟨lt_of_le_of_ne t₁.2.1 (fun h => ht10 (Subtype.ext h.symm)),
           lt_of_le_of_ne t₁.2.2 (fun h => ht11 (Subtype.ext h))⟩
        simp only [rawRel, RawPoint.toVertex?, ht10, ht11, ↓reduceIte] at hrel
        by_cases ht20 : t₂ = 0
        · subst ht20; simp at hrel
        · by_cases ht21 : t₂ = 1
          · subst ht21; simp [ht20] at hrel
          · simp only [ht20, ht21, ↓reduceIte] at hrel
            obtain ⟨a, s, b, r, ha, hb, hpair⟩ := hrel
            injection ha with ha1 ha2
            injection hb with hb1 hb2
            subst ha1 ha2 hb1 hb2
            refine Or.inr (Or.inr ⟨h01.1, h01.2,
              lt_of_le_of_ne t₂.2.1 (fun h => ht20 (Subtype.ext h.symm)),
              lt_of_le_of_ne t₂.2.2 (fun h => ht21 (Subtype.ext h)), hpair⟩)
  · rintro (⟨rfl, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ | ⟨rfl, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ |
      ⟨_, _, _, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
    · rfl
    · exact edgePoint_symm d₂ t₂

theorem edgePoint_injective (d : W.graph.Dart) :
    Function.Injective (edgePoint d : unitInterval → MetricGraph W) := by
  intro t₁ t₂ h
  rcases edgePoint_eq_edgePoint_iff.mp h with ⟨rfl, ⟨rfl, _⟩ | ⟨rfl, hd⟩⟩ |
      ⟨rfl, ⟨rfl, hd⟩ | ⟨rfl, _⟩⟩ | ⟨_, _, _, _, ⟨_, rfl⟩ | ⟨hsym, _⟩⟩
  · rfl
  · exact absurd hd d.fst_ne_snd
  · exact absurd hd d.snd_ne_fst
  · rfl
  · rfl
  · exact absurd hsym.symm d.symm_ne

/-! ### Geodesic distance on raw points -/

private noncomputable def viaEndpoints (W : WeightedGraph V) (p q : RawPoint W.graph) : ℝ :=
  let vd := vertexDist W.graph W.weight
  min
    (min (p.endOff W false + vd (p.endV false) (q.endV false) + q.endOff W false)
         (p.endOff W false + vd (p.endV false) (q.endV true) + q.endOff W true))
    (min (p.endOff W true + vd (p.endV true) (q.endV false) + q.endOff W false)
         (p.endOff W true + vd (p.endV true) (q.endV true) + q.endOff W true))

private theorem viaEndpoints_le (W : WeightedGraph V) (p q : RawPoint W.graph) (a b : Bool) :
    viaEndpoints W p q ≤
      p.endOff W a + vertexDist W.graph W.weight (p.endV a) (q.endV b) + q.endOff W b := by
  cases a <;> cases b <;> simp only [viaEndpoints]
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private theorem viaEndpoints_nonneg (W : WeightedGraph V) (p q : RawPoint W.graph) :
    0 ≤ viaEndpoints W p q := by
  simp only [viaEndpoints, le_min_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    exact add_nonneg (add_nonneg (RawPoint.endOff_nonneg W _ p)
      (vertexDist_nonneg W.weight_nonneg _ _)) (RawPoint.endOff_nonneg W _ q)

private theorem viaEndpoints_comm (W : WeightedGraph V) (p q : RawPoint W.graph) :
    viaEndpoints W p q = viaEndpoints W q p := by
  have swap : ∀ a b : Bool,
      p.endOff W a + vertexDist W.graph W.weight (p.endV a) (q.endV b) + q.endOff W b =
      q.endOff W b + vertexDist W.graph W.weight (q.endV b) (p.endV a) + p.endOff W a := by
    intro a b
    rw [vertexDist_comm]
    ring
  simp only [viaEndpoints, swap]
  rw [min_comm (min _ _) (min _ _)]
  simp only [min_assoc, min_left_comm]
  ac_rfl

private theorem viaEndpoints_le_branch_add_branch (W : WeightedGraph V)
    (p q r : RawPoint W.graph) (a b c e : Bool) :
    viaEndpoints W p r ≤
      (p.endOff W a + vertexDist W.graph W.weight (p.endV a) (q.endV b) + q.endOff W b) +
      (q.endOff W c + vertexDist W.graph W.weight (q.endV c) (r.endV e) + r.endOff W e) := by
  refine (viaEndpoints_le W p r a e).trans ?_
  have h1 := vertexDist_triangle W.weight_nonneg
    (W.connected (p.endV a) (q.endV b)) (W.connected (q.endV b) (r.endV e))
  have h2 := vertexDist_triangle W.weight_nonneg
    (W.connected (q.endV b) (q.endV c)) (W.connected (q.endV c) (r.endV e))
  have h3 := RawPoint.vertexDist_endV_le W b c q
  linarith

open Classical in
private noncomputable def directDist (W : WeightedGraph V)
    (d₁ d₂ : W.graph.Dart) (t₁ t₂ : unitInterval) : ℝ :=
  if d₁ = d₂ then |(t₁ : ℝ) - t₂| * W.weight d₁.edge
  else |(t₁ : ℝ) - (1 - t₂)| * W.weight d₁.edge

private theorem directDist_self (W : WeightedGraph V) (d : W.graph.Dart) (t : unitInterval) :
    directDist W d d t t = 0 := by
  simp [directDist]

private theorem directDist_nonneg (W : WeightedGraph V) (d₁ d₂ : W.graph.Dart)
    (t₁ t₂ : unitInterval) : 0 ≤ directDist W d₁ d₂ t₁ t₂ := by
  unfold directDist
  split_ifs <;> exact mul_nonneg (abs_nonneg _) (W.dart_weight_nonneg d₁)

private theorem directDist_comm (W : WeightedGraph V) {d₁ d₂ : W.graph.Dart}
    (he : d₁.edge = d₂.edge) (t₁ t₂ : unitInterval) :
    directDist W d₁ d₂ t₁ t₂ = directDist W d₂ d₁ t₂ t₁ := by
  classical
  rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
  · simp [directDist, abs_sub_comm]
  · have hne : d₂.symm ≠ d₂ := d₂.symm_ne
    have hne' : d₂ ≠ d₂.symm := hne.symm
    simp only [directDist, hne, hne', ↓reduceIte, Dart.edge_symm]
    congr 1
    congr 1
    ring

private theorem directDist_triangle (W : WeightedGraph V) {d₁ d₂ d₃ : W.graph.Dart}
    (h12 : d₁.edge = d₂.edge) (h23 : d₂.edge = d₃.edge) (t₁ t₂ t₃ : unitInterval) :
    directDist W d₁ d₃ t₁ t₃ ≤ directDist W d₁ d₂ t₁ t₂ + directDist W d₂ d₃ t₂ t₃ := by
  classical
  rcases (dart_edge_eq_iff d₁ d₂).mp h12 with h12eq | h12eq
  · subst h12eq
    rcases (dart_edge_eq_iff d₁ d₃).mp h23 with h23eq | h23eq
    · subst h23eq
      simp only [directDist, ↓reduceIte, ← add_mul]
      exact mul_le_mul_of_nonneg_right (abs_sub_le _ _ _) (W.dart_weight_nonneg _)
    · subst h23eq
      have hne : d₃.symm ≠ d₃ := d₃.symm_ne
      simp only [directDist, hne, ↓reduceIte, Dart.edge_symm, ← add_mul]
      exact mul_le_mul_of_nonneg_right (abs_sub_le (t₁ : ℝ) t₂ (1 - t₃))
        (W.dart_weight_nonneg _)
  · subst h12eq
    rcases (dart_edge_eq_iff d₂ d₃).mp h23 with h23eq | h23eq
    · subst h23eq
      have hne : d₂.symm ≠ d₂ := d₂.symm_ne
      simp only [directDist, hne, ↓reduceIte, Dart.edge_symm, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (W.dart_weight_nonneg _)
      calc |(t₁ : ℝ) - (1 - (t₃ : ℝ))|
          = |((t₁ : ℝ) - (1 - (t₂ : ℝ))) + ((t₃ : ℝ) - (t₂ : ℝ))| := by ring_nf
        _ ≤ |(t₁ : ℝ) - (1 - (t₂ : ℝ))| + |(t₃ : ℝ) - (t₂ : ℝ)| := abs_add_le _ _
        _ = |(t₁ : ℝ) - (1 - (t₂ : ℝ))| + |(t₂ : ℝ) - (t₃ : ℝ)| := by
          rw [abs_sub_comm (t₃ : ℝ) (t₂ : ℝ)]
    · subst h23eq
      have hne1 : d₃.symm ≠ d₃ := d₃.symm_ne
      have hne2 : d₃ ≠ d₃.symm := hne1.symm
      simp only [directDist, Dart.symm_symm, ↓reduceIte, hne1, hne2, Dart.edge_symm, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (W.dart_weight_nonneg _)
      calc |(t₁ : ℝ) - (t₃ : ℝ)|
          = |((t₁ : ℝ) - (1 - (t₂ : ℝ))) + ((1 - (t₂ : ℝ)) - (t₃ : ℝ))| := by ring_nf
        _ ≤ |(t₁ : ℝ) - (1 - (t₂ : ℝ))| + |(1 - (t₂ : ℝ)) - (t₃ : ℝ)| := abs_add_le _ _
        _ = |(t₁ : ℝ) - (1 - (t₂ : ℝ))| + |(t₂ : ℝ) - (1 - (t₃ : ℝ))| := by
          congr 1
          rw [abs_sub_comm]
          congr 1
          ring

open Classical in
private theorem endOff_le_directDist_add_endOff (W : WeightedGraph V)
    {d₁ d₂ : W.graph.Dart} (he : d₁.edge = d₂.edge) (t₁ t₂ : unitInterval) (b : Bool) :
    (RawPoint.edge d₁ t₁).endOff W (if d₁ = d₂ then b else !b) ≤
      directDist W d₁ d₂ t₁ t₂ + (RawPoint.edge d₂ t₂).endOff W b ∧
    (RawPoint.edge d₁ t₁).endV (if d₁ = d₂ then b else !b) = (RawPoint.edge d₂ t₂).endV b := by
  classical
  rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
  · simp only [↓reduceIte, directDist]
    cases b <;> refine ⟨?_, rfl⟩
    · simp only [RawPoint.endOff, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self ((t₁ : ℝ) - t₂)])
        (W.dart_weight_nonneg d₁)
    · simp only [RawPoint.endOff, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [neg_le_abs ((t₁ : ℝ) - t₂)])
        (W.dart_weight_nonneg d₁)
  · have hne : d₂.symm ≠ d₂ := d₂.symm_ne
    simp only [hne, ↓reduceIte, directDist, Dart.edge_symm]
    cases b <;> refine ⟨?_, rfl⟩
    · simp only [Bool.not_false, RawPoint.endOff, Dart.edge_symm, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [neg_le_abs ((t₁ : ℝ) - (1 - t₂))])
        (W.dart_weight_nonneg d₂)
    · simp only [Bool.not_true, RawPoint.endOff, Dart.edge_symm, ← add_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self ((t₁ : ℝ) - (1 - t₂))])
        (W.dart_weight_nonneg d₂)

open Classical in
private noncomputable def rawDist (W : WeightedGraph V) :
    RawPoint W.graph → RawPoint W.graph → ℝ
  | .edge d₁ t₁, .edge d₂ t₂ =>
    if d₁.edge = d₂.edge then
      min (directDist W d₁ d₂ t₁ t₂) (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂))
    else
      viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)
  | p, q => viaEndpoints W p q

private theorem rawDist_le_viaEndpoints (W : WeightedGraph V) (p q : RawPoint W.graph) :
    rawDist W p q ≤ viaEndpoints W p q := by
  cases p <;> cases q <;> simp only [rawDist]
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · split_ifs
    · exact min_le_right _ _
    · exact le_rfl

private theorem rawDist_self (W : WeightedGraph V) (p : RawPoint W.graph) :
    rawDist W p p = 0 := by
  classical
  cases p with
  | vertex v =>
    simp only [rawDist, viaEndpoints, RawPoint.endOff, RawPoint.endV,
      vertexDist_self W.weight_nonneg, add_zero, min_self]
  | edge d t =>
    simp only [rawDist, ↓reduceIte, directDist_self]
    exact min_eq_left (viaEndpoints_nonneg W _ _)

private theorem rawDist_comm (W : WeightedGraph V) (p q : RawPoint W.graph) :
    rawDist W p q = rawDist W q p := by
  classical
  cases p with
  | vertex u => cases q <;> exact viaEndpoints_comm W _ _
  | edge d₁ t₁ =>
    cases q with
    | vertex v => exact viaEndpoints_comm W _ _
    | edge d₂ t₂ =>
      simp only [rawDist]
      by_cases he : d₁.edge = d₂.edge
      · have he' : d₂.edge = d₁.edge := he.symm
        rw [ite_eq_left he, ite_eq_left he', directDist_comm W he, viaEndpoints_comm W]
      · have he' : d₂.edge ≠ d₁.edge := fun h => he h.symm
        rw [ite_eq_right he, ite_eq_right he', viaEndpoints_comm W]

private theorem rawDist_nonneg (W : WeightedGraph V) (p q : RawPoint W.graph) :
    0 ≤ rawDist W p q := by
  classical
  cases p <;> cases q <;> simp only [rawDist]
  · exact viaEndpoints_nonneg W _ _
  · exact viaEndpoints_nonneg W _ _
  · exact viaEndpoints_nonneg W _ _
  · split_ifs
    · exact le_min (directDist_nonneg W _ _ _ _) (viaEndpoints_nonneg W _ _)
    · exact viaEndpoints_nonneg W _ _

private theorem viaEndpoints_case (W : WeightedGraph V) (p q : RawPoint W.graph) :
    ∃ a b : Bool, viaEndpoints W p q =
      p.endOff W a + vertexDist W.graph W.weight (p.endV a) (q.endV b) + q.endOff W b := by
  unfold viaEndpoints
  rcases min_choice
      (min (p.endOff W false + vertexDist W.graph W.weight (p.endV false) (q.endV false) +
          q.endOff W false)
        (p.endOff W false + vertexDist W.graph W.weight (p.endV false) (q.endV true) +
          q.endOff W true))
      (min (p.endOff W true + vertexDist W.graph W.weight (p.endV true) (q.endV false) +
          q.endOff W false)
        (p.endOff W true + vertexDist W.graph W.weight (p.endV true) (q.endV true) +
          q.endOff W true)) with h | h <;> rw [h]
  · rcases min_choice
        (p.endOff W false + vertexDist W.graph W.weight (p.endV false) (q.endV false) +
          q.endOff W false)
        (p.endOff W false + vertexDist W.graph W.weight (p.endV false) (q.endV true) +
          q.endOff W true) with h' | h' <;> rw [h']
    · exact ⟨false, false, rfl⟩
    · exact ⟨false, true, rfl⟩
  · rcases min_choice
        (p.endOff W true + vertexDist W.graph W.weight (p.endV true) (q.endV false) +
          q.endOff W false)
        (p.endOff W true + vertexDist W.graph W.weight (p.endV true) (q.endV true) +
          q.endOff W true) with h' | h' <;> rw [h']
    · exact ⟨true, false, rfl⟩
    · exact ⟨true, true, rfl⟩

private theorem rawDist_triangle (W : WeightedGraph V) (p q r : RawPoint W.graph) :
    rawDist W p r ≤ rawDist W p q + rawDist W q r := by
  classical
  have hvv : viaEndpoints W p r ≤ viaEndpoints W p q + viaEndpoints W q r := by
    obtain ⟨a, b, hab⟩ := viaEndpoints_case W p q
    obtain ⟨c, e, hce⟩ := viaEndpoints_case W q r
    rw [hab, hce]
    exact viaEndpoints_le_branch_add_branch W p q r a b c e
  have hdv : ∀ d₁ t₁ d₂ t₂, d₁.edge = d₂.edge →
      viaEndpoints W (.edge d₁ t₁) r ≤
        directDist W d₁ d₂ t₁ t₂ + viaEndpoints W (.edge d₂ t₂) r := by
    intro d₁ t₁ d₂ t₂ he
    obtain ⟨c, e, hce⟩ := viaEndpoints_case W (.edge d₂ t₂) r
    rw [hce]
    obtain ⟨hoff, hv⟩ := endOff_le_directDist_add_endOff W he t₁ t₂ c
    have hle := viaEndpoints_le W (.edge d₁ t₁) r (if d₁ = d₂ then c else !c) e
    rw [hv] at hle
    linarith
  have hvd : ∀ (p r : RawPoint W.graph) d₂ t₂ d₃ t₃, d₂.edge = d₃.edge →
      viaEndpoints W p (.edge d₃ t₃) ≤
        viaEndpoints W p (.edge d₂ t₂) + directDist W d₂ d₃ t₂ t₃ := by
    intro p r d₂ t₂ d₃ t₃ he
    rw [viaEndpoints_comm W p (.edge d₃ t₃), viaEndpoints_comm W p (.edge d₂ t₂), add_comm,
      directDist_comm W he]
    obtain ⟨c, e, hce⟩ := viaEndpoints_case W (.edge d₂ t₂) p
    rw [hce]
    obtain ⟨hoff, hv⟩ := endOff_le_directDist_add_endOff W he.symm t₃ t₂ c
    have hle := viaEndpoints_le W (.edge d₃ t₃) p (if d₃ = d₂ then c else !c) e
    rw [hv] at hle
    linarith
  cases p with
  | vertex u =>
    cases q with
    | vertex v => exact (rawDist_le_viaEndpoints W _ _).trans hvv
    | edge d₂ t₂ =>
      cases r with
      | vertex w => exact (rawDist_le_viaEndpoints W _ _).trans hvv
      | edge d₃ t₃ =>
        simp only [rawDist] at hvv ⊢
        split_ifs with he23
        · rcases min_choice (directDist W d₂ d₃ t₂ t₃)
              (viaEndpoints W (.edge d₂ t₂) (.edge d₃ t₃)) with h | h <;> rw [h]
          · exact hvd (.vertex u) (.vertex u) d₂ t₂ d₃ t₃ he23
          · exact hvv
        · exact hvv
  | edge d₁ t₁ =>
    cases q with
    | vertex v => exact (rawDist_le_viaEndpoints W _ _).trans hvv
    | edge d₂ t₂ =>
      cases r with
      | vertex w =>
        simp only [rawDist] at hvv ⊢
        split_ifs with he12
        · rcases min_choice (directDist W d₁ d₂ t₁ t₂)
              (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)) with h | h <;> rw [h]
          · exact hdv d₁ t₁ d₂ t₂ he12
          · exact hvv
        · exact hvv
      | edge d₃ t₃ =>
        simp only [rawDist]
        by_cases he12 : d₁.edge = d₂.edge <;>
          by_cases he23 : d₂.edge = d₃.edge <;>
          by_cases he13 : d₁.edge = d₃.edge
        · rw [ite_eq_left he13, ite_eq_left he12, ite_eq_left he23]
          rcases min_choice (directDist W d₁ d₂ t₁ t₂)
              (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)) with h1 | h1 <;>
            rcases min_choice (directDist W d₂ d₃ t₂ t₃)
              (viaEndpoints W (.edge d₂ t₂) (.edge d₃ t₃)) with h2 | h2 <;> rw [h1, h2]
          · exact (min_le_left _ _).trans (directDist_triangle W he12 he23 t₁ t₂ t₃)
          · exact (min_le_right _ _).trans (hdv d₁ t₁ d₂ t₂ he12)
          · exact (min_le_right _ _).trans (hvd (.edge d₁ t₁) (.edge d₁ t₁) d₂ t₂ d₃ t₃ he23)
          · exact (min_le_right _ _).trans hvv
        · exact absurd (he12.trans he23) he13
        · rw [ite_eq_left he13, ite_eq_left he12, ite_eq_right he23]
          rcases min_choice (directDist W d₁ d₂ t₁ t₂)
              (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)) with h1 | h1 <;> rw [h1]
          · exact (min_le_right _ _).trans (hdv d₁ t₁ d₂ t₂ he12)
          · exact (min_le_right _ _).trans hvv
        · rw [ite_eq_right he13, ite_eq_left he12, ite_eq_right he23]
          rcases min_choice (directDist W d₁ d₂ t₁ t₂)
              (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)) with h1 | h1 <;> rw [h1]
          · exact hdv d₁ t₁ d₂ t₂ he12
          · exact hvv
        · rw [ite_eq_left he13, ite_eq_right he12, ite_eq_left he23]
          rcases min_choice (directDist W d₂ d₃ t₂ t₃)
              (viaEndpoints W (.edge d₂ t₂) (.edge d₃ t₃)) with h2 | h2 <;> rw [h2]
          · exact (min_le_right _ _).trans (hvd (.edge d₁ t₁) (.edge d₁ t₁) d₂ t₂ d₃ t₃ he23)
          · exact (min_le_right _ _).trans hvv
        · rw [ite_eq_right he13, ite_eq_right he12, ite_eq_left he23]
          rcases min_choice (directDist W d₂ d₃ t₂ t₃)
              (viaEndpoints W (.edge d₂ t₂) (.edge d₃ t₃)) with h2 | h2 <;> rw [h2]
          · exact hvd (.edge d₁ t₁) (.edge d₁ t₁) d₂ t₂ d₃ t₃ he23
          · exact hvv
        · rw [ite_eq_left he13, ite_eq_right he12, ite_eq_right he23]
          exact (min_le_right _ _).trans hvv
        · rw [ite_eq_right he13, ite_eq_right he12, ite_eq_right he23]
          exact hvv

private theorem rawDist_eq_zero_of_rel (W : WeightedGraph V) {p q : RawPoint W.graph}
    (h : rawRel p q) : rawDist W p q = 0 := by
  classical
  unfold rawRel at h
  cases hp : p.toVertex? with
  | some u =>
    cases hq : q.toVertex? with
    | none => simp [hp, hq] at h
    | some v =>
      simp only [hp, hq] at h
      subst h
      have end_of_some : ∀ r : RawPoint W.graph, r.toVertex? = some u →
          ∃ b : Bool, r.endV b = u ∧ r.endOff W b = 0 := by
        intro r hr
        cases r with
        | vertex w =>
          simp only [RawPoint.toVertex?, Option.some.injEq] at hr
          subst hr
          exact ⟨false, rfl, rfl⟩
        | edge d t =>
          simp only [RawPoint.toVertex?] at hr
          split_ifs at hr with ht0 ht1
          · subst ht0; simp only [Option.some.injEq] at hr; subst hr
            exact ⟨false, rfl, by simp [RawPoint.endOff]⟩
          · subst ht1; simp only [Option.some.injEq] at hr; subst hr
            exact ⟨true, rfl, by simp [RawPoint.endOff]⟩
      obtain ⟨bp, hvp, hop⟩ := end_of_some p hp
      obtain ⟨bq, hvq, hoq⟩ := end_of_some q hq
      refine le_antisymm ?_ (rawDist_nonneg W p q)
      refine (rawDist_le_viaEndpoints W p q).trans ?_
      refine (viaEndpoints_le W p q bp bq).trans ?_
      rw [hvp, hvq, hop, hoq, vertexDist_self W.weight_nonneg]
      linarith
  | none =>
    cases hq : q.toVertex? with
    | some v => simp [hp, hq] at h
    | none =>
      simp only [hp, hq] at h
      obtain ⟨d₁, t₁, d₂, t₂, rfl, rfl, hpair⟩ := h
      refine le_antisymm ?_ (rawDist_nonneg W _ _)
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (rawDist_self W _).le
      · simp only [rawDist, Dart.edge_symm, ↓reduceIte]
        refine (min_le_left _ _).trans ?_
        have hne : d₂.symm ≠ d₂ := d₂.symm_ne
        simp [directDist, hne]

private theorem rawDist_well_defined (W : WeightedGraph V) {p₁ p₂ q₁ q₂ : RawPoint W.graph}
    (hp : rawRel p₁ p₂) (hq : rawRel q₁ q₂) : rawDist W p₁ q₁ = rawDist W p₂ q₂ := by
  have d12 := rawDist_eq_zero_of_rel W hp
  have d21 := rawDist_eq_zero_of_rel W ((rawRel_equivalence W.graph).symm hp)
  have d34 := rawDist_eq_zero_of_rel W hq
  have d43 := rawDist_eq_zero_of_rel W ((rawRel_equivalence W.graph).symm hq)
  have h1 := rawDist_triangle W p₁ p₂ q₁
  have h2 := rawDist_triangle W p₂ q₁ q₂
  have h2' := rawDist_triangle W p₂ q₂ q₁
  have h3 := rawDist_triangle W p₂ p₁ q₂
  have h4 := rawDist_triangle W p₁ q₂ q₁
  have h4' := rawDist_triangle W p₁ q₁ q₂
  linarith

private theorem rel_of_rawDist_eq_zero [Finite V] (W : WeightedGraph V)
    {p q : RawPoint W.graph} (h : rawDist W p q = 0) : rawRel p q := by
  classical
  have hvia_zero : ∀ a b : RawPoint W.graph, viaEndpoints W a b = 0 → rawRel a b := by
    intro a b hvia
    obtain ⟨ba, bb, hba⟩ := viaEndpoints_case W a b
    rw [hba] at hvia
    have hoa := RawPoint.endOff_nonneg W ba a
    have hob := RawPoint.endOff_nonneg W bb b
    have hvd := vertexDist_nonneg W.weight_nonneg (a.endV ba) (b.endV bb)
    have h1 : a.endOff W ba = 0 := by linarith
    have h2 : vertexDist W.graph W.weight (a.endV ba) (b.endV bb) = 0 := by linarith
    have h3 : b.endOff W bb = 0 := by linarith
    have heqV : a.endV ba = b.endV bb :=
      (vertexDist_eq_zero_iff W.weight_pos (W.connected _ _)).mp h2
    have toVertex_of_endOff : ∀ (r : RawPoint W.graph) (br : Bool), r.endOff W br = 0 →
        r.toVertex? = some (r.endV br) := by
      intro r br hbr
      cases r with
      | vertex v => cases br <;> rfl
      | edge d t =>
        have hpos := W.dart_weight_pos d
        cases br
        · simp only [RawPoint.endOff, mul_eq_zero] at hbr
          have ht : t = 0 := Subtype.ext (hbr.resolve_right hpos.ne')
          simp [RawPoint.toVertex?, RawPoint.endV, ht]
        · simp only [RawPoint.endOff, mul_eq_zero] at hbr
          have ht : (1 : ℝ) - t = 0 := hbr.resolve_right hpos.ne'
          have ht1 : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith)
          simp [RawPoint.toVertex?, RawPoint.endV, ht1]
    have haV := toVertex_of_endOff a ba h1
    have hbV := toVertex_of_endOff b bb h3
    simp only [rawRel, haV, hbV, heqV]
  cases p with
  | vertex u => exact hvia_zero _ _ h
  | edge d₁ t₁ =>
    cases q with
    | vertex v => exact hvia_zero _ _ h
    | edge d₂ t₂ =>
      simp only [rawDist] at h
      split_ifs at h with he
      · rcases min_choice (directDist W d₁ d₂ t₁ t₂)
            (viaEndpoints W (.edge d₁ t₁) (.edge d₂ t₂)) with hmin | hmin
        · rw [hmin] at h
          have hpos := W.dart_weight_pos d₁
          have ht : (d₁ = d₂ ∧ t₁ = t₂) ∨ (d₁ = d₂.symm ∧ t₁ = unitInterval.symm t₂) := by
            rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
            · simp only [directDist, ↓reduceIte, mul_eq_zero] at h
              have ht' : |(t₁ : ℝ) - t₂| = 0 := h.resolve_right hpos.ne'
              exact Or.inl ⟨rfl, Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp ht'))⟩
            · have hne : d₂.symm ≠ d₂ := d₂.symm_ne
              have hpos' : 0 < W.weight d₂.edge := W.dart_weight_pos d₂
              simp only [directDist, hne, ↓reduceIte, Dart.edge_symm, mul_eq_zero] at h
              have ht' : |(t₁ : ℝ) - (1 - t₂)| = 0 := h.resolve_right hpos'.ne'
              exact Or.inr ⟨rfl, Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp ht'))⟩
          rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (rawRel_equivalence W.graph).refl _
          · by_cases ht0 : t₂ = 0
            · subst ht0; simp [rawRel, RawPoint.toVertex?]
            · by_cases ht1 : t₂ = 1
              · subst ht1; simp [rawRel, RawPoint.toVertex?]
              · have hs0 : unitInterval.symm t₂ ≠ 0 := by simp [ht1]
                have hs1 : unitInterval.symm t₂ ≠ 1 := by simp [ht0]
                simp only [rawRel, RawPoint.toVertex?, ht0, ht1, hs0, hs1, ↓reduceIte]
                exact ⟨d₂.symm, unitInterval.symm t₂, d₂, t₂, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
        · rw [hmin] at h
          exact hvia_zero _ _ h
      · exact hvia_zero _ _ h

/-- Geodesic distance on `MetricGraph W`. -/
noncomputable def metricDist (W : WeightedGraph V) : MetricGraph W → MetricGraph W → ℝ :=
  Quotient.lift₂ (rawDist W) fun _ _ _ _ hp hq => rawDist_well_defined W hp hq

noncomputable instance instMetricSpace [Finite V] : MetricSpace (MetricGraph W) where
  dist := metricDist W
  dist_self := by exact Quotient.ind (rawDist_self W)
  dist_comm := by exact Quotient.ind₂ (rawDist_comm W)
  dist_triangle := by exact Quotient.ind₂ fun p q => Quotient.ind (rawDist_triangle W p q)
  eq_of_dist_eq_zero {x y} := by
    refine Quotient.inductionOn₂ x y fun p q h => Quotient.sound ?_
    exact rel_of_rawDist_eq_zero W h

/-! ### Closed-form distance formulas -/

@[simp]
theorem dist_vertex [Finite V] (u v : V) :
    dist (vertex u : MetricGraph W) (vertex v) = vertexDist W.graph W.weight u v := by
  change metricDist W _ _ = _
  dsimp only [vertex, metricDist]
  rw [Quotient.lift₂_mk]
  simp [rawDist, viaEndpoints, RawPoint.endOff, RawPoint.endV]

theorem dist_vertex_edgePoint [Finite V] (u : V) (d : W.graph.Dart) (t : unitInterval) :
    dist (vertex u : MetricGraph W) (edgePoint d t) =
      min (vertexDist W.graph W.weight u d.fst + (t : ℝ) * W.weight d.edge)
          (vertexDist W.graph W.weight u d.snd + (1 - (t : ℝ)) * W.weight d.edge) := by
  change metricDist W _ _ = _
  dsimp only [vertex, edgePoint, metricDist]
  rw [Quotient.lift₂_mk]
  simp [rawDist, viaEndpoints, RawPoint.endOff, RawPoint.endV, min_self]

theorem dist_edgePoint_vertex [Finite V] (d : W.graph.Dart) (t : unitInterval) (u : V) :
    dist (edgePoint d t : MetricGraph W) (vertex u) =
      min ((t : ℝ) * W.weight d.edge + vertexDist W.graph W.weight d.fst u)
          ((1 - (t : ℝ)) * W.weight d.edge + vertexDist W.graph W.weight d.snd u) := by
  rw [dist_comm, dist_vertex_edgePoint]
  simp [vertexDist_comm, add_comm]

theorem dist_edgePoint_self_le [Finite V] (d : W.graph.Dart) (s t : unitInterval) :
    dist (edgePoint d s : MetricGraph W) (edgePoint d t) ≤ W.weight d.edge * |(s : ℝ) - t| := by
  classical
  change metricDist W _ _ ≤ _
  dsimp only [edgePoint, metricDist]
  rw [Quotient.lift₂_mk]
  simp only [rawDist, ↓reduceIte, directDist]
  refine (min_le_left _ _).trans ?_
  rw [mul_comm]

theorem dist_edgePoint_edgePoint_of_edge_ne [Finite V] {d₁ d₂ : W.graph.Dart}
    (hne : d₁.edge ≠ d₂.edge) (t₁ t₂ : unitInterval) :
    dist (edgePoint d₁ t₁ : MetricGraph W) (edgePoint d₂ t₂) =
      min
        (min ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.fst +
                (t₂ : ℝ) * W.weight d₂.edge)
             ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.snd +
                (1 - (t₂ : ℝ)) * W.weight d₂.edge))
        (min ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.fst +
                (t₂ : ℝ) * W.weight d₂.edge)
             ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.snd +
                (1 - (t₂ : ℝ)) * W.weight d₂.edge)) := by
  classical
  change metricDist W _ _ = _
  dsimp only [edgePoint, metricDist]
  rw [Quotient.lift₂_mk]
  simp [rawDist, hne, viaEndpoints, RawPoint.endOff, RawPoint.endV]

theorem dist_edgePoint_edgePoint_same [Finite V] (d : W.graph.Dart) (s t : unitInterval) :
    dist (edgePoint d s : MetricGraph W) (edgePoint d t) =
      min (|(s : ℝ) - t| * W.weight d.edge)
        (min
          (min ((s : ℝ) * W.weight d.edge + vertexDist W.graph W.weight d.fst d.fst +
                  (t : ℝ) * W.weight d.edge)
               ((s : ℝ) * W.weight d.edge + vertexDist W.graph W.weight d.fst d.snd +
                  (1 - (t : ℝ)) * W.weight d.edge))
          (min ((1 - (s : ℝ)) * W.weight d.edge + vertexDist W.graph W.weight d.snd d.fst +
                  (t : ℝ) * W.weight d.edge)
               ((1 - (s : ℝ)) * W.weight d.edge + vertexDist W.graph W.weight d.snd d.snd +
                  (1 - (t : ℝ)) * W.weight d.edge))) := by
  classical
  change metricDist W _ _ = _
  dsimp only [edgePoint, metricDist]
  rw [Quotient.lift₂_mk]
  simp [rawDist, directDist, viaEndpoints, RawPoint.endOff, RawPoint.endV]

theorem dist_edgePoint_eq_direct_of_vertexDist_eq [Finite V] {d : W.graph.Dart}
    (hd : vertexDist W.graph W.weight d.fst d.snd = W.weight d.edge) (s t : unitInterval) :
    dist (edgePoint d s : MetricGraph W) (edgePoint d t) = W.weight d.edge * |(s : ℝ) - t| := by
  rw [dist_edgePoint_edgePoint_same, vertexDist_self W.weight_nonneg,
    vertexDist_self W.weight_nonneg, hd, vertexDist_comm, hd]
  have hw := W.dart_weight_nonneg d
  have hs0 := s.2.1; have hs1 := s.2.2; have ht0 := t.2.1; have ht1 := t.2.2
  rw [mul_comm (W.weight d.edge), min_eq_left]
  have hle1 : |(s : ℝ) - t| ≤ (s : ℝ) + t := abs_le.mpr ⟨by linarith, by linarith⟩
  have hle2 : |(s : ℝ) - t| ≤ (s : ℝ) + 1 + (1 - t) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hle3 : |(s : ℝ) - t| ≤ (1 - (s : ℝ)) + 1 + t :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hle4 : |(s : ℝ) - t| ≤ (1 - (s : ℝ)) + (1 - t) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
  · simpa only [add_zero] using (mul_le_mul_of_nonneg_right hle1 hw).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_right hle2 hw).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_right hle3 hw).trans_eq (by ring)
  · simpa only [add_zero] using (mul_le_mul_of_nonneg_right hle4 hw).trans_eq (by ring)

/-! ### Continuity and compactness -/

theorem continuous_edgePoint [Finite V] (d : W.graph.Dart) :
    Continuous (edgePoint d : unitInterval → MetricGraph W) := by
  refine Metric.continuous_iff.mpr fun s ε hε => ?_
  have hw := W.dart_weight_pos d
  refine ⟨ε / W.weight d.edge, div_pos hε hw, fun t ht => ?_⟩
  refine (dist_edgePoint_self_le d t s).trans_lt ?_
  rw [Subtype.dist_eq, Real.dist_eq] at ht
  calc W.weight d.edge * |(t : ℝ) - s|
      < W.weight d.edge * (ε / W.weight d.edge) := mul_lt_mul_of_pos_left ht hw
    _ = ε := mul_div_cancel₀ ε hw.ne'

noncomputable instance instCompactSpace [Finite V] : CompactSpace (MetricGraph W) := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  let : TopologicalSpace W.graph.Dart := ⊥
  let : DiscreteTopology W.graph.Dart := ⟨rfl⟩
  have hfinDart : Finite W.graph.Dart :=
    Finite.of_injective Dart.toProd Dart.toProd_injective
  have hcV : CompactSpace V := Finite.compactSpace
  have hcD : CompactSpace W.graph.Dart := Finite.compactSpace
  let f : V ⊕ (Σ _ : W.graph.Dart, unitInterval) → MetricGraph W :=
    Sum.elim vertex (fun p => edgePoint p.1 p.2)
  have hf_cont : Continuous f :=
    Continuous.sumElim continuous_of_discreteTopology
      (continuous_sigma fun d => continuous_edgePoint d)
  have hf_surj : Function.Surjective f := fun x =>
    ind_simple (motive := fun y => ∃ a, f a = y)
      (fun v => ⟨.inl v, rfl⟩) (fun d t => ⟨.inr ⟨d, t⟩, rfl⟩) x
  rw [← isCompact_univ_iff, ← hf_surj.range_eq]
  exact isCompact_range hf_cont

/-- Minimum weight among all darts in a nonempty finite weighted graph. -/
theorem exists_min_dart_weight [Finite V] (d₀ : W.graph.Dart) :
    ∃ wmin : ℝ, 0 < wmin ∧ ∀ d : W.graph.Dart, wmin ≤ W.weight d.edge := by
  classical
  have : Finite W.graph.Dart := Finite.of_injective Dart.toProd Dart.toProd_injective
  have hfin : (Set.univ : Set W.graph.Dart).Finite := Set.finite_univ
  obtain ⟨d₁, _, hd₁⟩ := hfin.toFinset.exists_min_image (fun d : W.graph.Dart => W.weight d.edge)
    ⟨d₀, hfin.mem_toFinset.mpr (Set.mem_univ d₀)⟩
  exact ⟨W.weight d₁.edge, W.dart_weight_pos d₁, fun d =>
    hd₁ d (hfin.mem_toFinset.mpr (Set.mem_univ d))⟩

end MetricGraph

end SimpleGraph
