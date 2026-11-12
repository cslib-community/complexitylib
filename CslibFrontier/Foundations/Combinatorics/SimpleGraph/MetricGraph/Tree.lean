/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Tree.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
import Mathlib.Tactic.Linarith

/-!
# Tree metric graphs

When `W.graph.IsTree`, the continuous metric graph `MetricGraph W` is a metric tree (an `ℝ`-tree):
geodesics are uniquely determined, every metric interval `interval x y` is isometric to
`Set.Icc 0 (Dist.dist x y)`, every triple `x, y, z` has a unique metric median `treeMedian x y z`,
and branches at any base point `p` partition `{ q | q ≠ p }`.

## Main definitions

* `SimpleGraph.MetricGraph.edgeProj`: the `1`-Lipschitz projection of `MetricGraph W` onto the
  segment `[0, W.weight d.edge]` along a bridge dart `d`.
* `SimpleGraph.MetricGraph.treeMedian`: the unique point in
  `interval x y ∩ interval y z ∩ interval z x` for a tree metric graph.
* `SimpleGraph.MetricGraph.branch`: the branch `{ w | p ∉ interval q w }` of `MetricGraph W`
  pointing from `p` toward `q`.

## Main results

* `SimpleGraph.MetricGraph.vertexDist_adj`: adjacent vertices in a tree have `vertexDist` equal
  to their edge weight.
* `SimpleGraph.MetricGraph.eq_of_mem_interval_dist_eq`,
  `SimpleGraph.MetricGraph.IsGeodesic.eq_on`: uniqueness of shortest paths and geodesics in tree
  metric graphs.
* `SimpleGraph.MetricGraph.exists_treeMedian`, `SimpleGraph.MetricGraph.eq_treeMedian_of_mem`,
  `SimpleGraph.MetricGraph.dist_add_dist_eq_treeMedian`: existence, uniqueness, and shortest-path
  projection property of `treeMedian`.
* `SimpleGraph.MetricGraph.exists_isometry_interval`,
  `SimpleGraph.MetricGraph.interval_subset_union`: intervals are isometric to real segments, and
  `interval x z ⊆ interval x y ∪ interval y z`.
* `SimpleGraph.MetricGraph.mem_branch_iff_of_mem_interval`,
  `SimpleGraph.MetricGraph.mem_branch_vertex_iff_edgeProj_pos`: branch membership through a point
  between `z` and the base points, and branches at a vertex through bridge projections.
* `SimpleGraph.MetricGraph.branch_eq_of_mem`,
  `SimpleGraph.MetricGraph.branch_disjoint_of_mem_interval`,
  `SimpleGraph.MetricGraph.exists_stem_segment`: branch equivalence and unbranched stem geometry
  needed for strategyproof facility location on trees.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Bridge projections in tree metric graphs -/

section TreeProjection

private lemma bridge_deleteEdges (hT : W.graph.IsTree) (d : W.graph.Dart) :
    ¬ (W.graph.deleteEdges {d.edge}).Reachable d.fst d.snd := by
  have hb : W.graph.IsBridge d.edge :=
    isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj
  change ¬ (W.graph.deleteEdges {s(d.fst, d.snd)}).Reachable d.fst d.snd
  exact isBridge_iff.mp hb

private lemma walk_reachable_deleteEdges_or {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) :
    (G.deleteEdges {s(a, b)}).Reachable u v ∨
      ((G.deleteEdges {s(a, b)}).Reachable u a ∨ (G.deleteEdges {s(a, b)}).Reachable u b) := by
  induction p with
  | nil => exact Or.inl .rfl
  | @cons x y z hxy _ ih =>
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl .rfl)
      · exact Or.inr (Or.inr .rfl)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj x y := ⟨hxy, by simp [he]⟩
      rcases ih with h | h | h
      · exact Or.inl (hadj.reachable.trans h)
      · exact Or.inr (Or.inl (hadj.reachable.trans h))
      · exact Or.inr (Or.inr (hadj.reachable.trans h))

private lemma reachable_deleteEdges_iff_not_reachable_snd (hT : W.graph.IsTree)
    (d : W.graph.Dart) (u : V) :
    (W.graph.deleteEdges {d.edge}).Reachable u d.fst ↔
      ¬ (W.graph.deleteEdges {d.edge}).Reachable u d.snd := by
  have hnot := bridge_deleteEdges hT d
  refine ⟨fun h1 h2 => hnot (h1.symm.trans h2), fun h => ?_⟩
  obtain ⟨p⟩ := W.connected u d.fst
  rcases walk_reachable_deleteEdges_or (a := d.fst) (b := d.snd) p with h1 | h1 | h2
  · exact h1
  · exact h1
  · exact False.elim (h h2)

private lemma reachable_deleteEdges_adj_iff (d d' : W.graph.Dart) (hne : d'.edge ≠ d.edge) :
    (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst ↔
      (W.graph.deleteEdges {d.edge}).Reachable d'.snd d.fst := by
  have hadj : (W.graph.deleteEdges {d.edge}).Adj d'.fst d'.snd := ⟨d'.adj, by simp [hne]⟩
  exact ⟨fun h => hadj.symm.reachable.trans h, fun h => hadj.reachable.trans h⟩

private noncomputable def edgeProjVert (W : WeightedGraph V) (d : W.graph.Dart) (v : V) : ℝ :=
  @ite ℝ ((W.graph.deleteEdges {d.edge}).Reachable v d.fst) (Classical.propDecidable _)
    0 (W.weight d.edge)

private noncomputable def edgeProjEdge (W : WeightedGraph V) (d d' : W.graph.Dart)
    (t : unitInterval) : ℝ :=
  @ite ℝ (d' = d) (Classical.propDecidable _) ((t : ℝ) * W.weight d.edge)
    (@ite ℝ (d' = d.symm) (Classical.propDecidable _) ((1 - (t : ℝ)) * W.weight d.edge)
      (edgeProjVert W d d'.fst))

private lemma edgeProjVert_fst (W : WeightedGraph V) (d : W.graph.Dart) :
    edgeProjVert W d d.fst = 0 := by
  classical
  dsimp only [edgeProjVert]
  simp only [Reachable.refl, ↓reduceIte]

private lemma edgeProjVert_snd (hT : W.graph.IsTree) (d : W.graph.Dart) :
    edgeProjVert W d d.snd = W.weight d.edge := by
  classical
  have hns : ¬ (W.graph.deleteEdges {d.edge}).Reachable d.snd d.fst :=
    fun h => bridge_deleteEdges hT d h.symm
  dsimp only [edgeProjVert]
  simp only [hns, ↓reduceIte]

private lemma edgeProjEdge_eq_fst (W : WeightedGraph V) (d d' : W.graph.Dart)
    (h1 : d' = d) (t : unitInterval) :
    edgeProjEdge W d d' t = (t : ℝ) * W.weight d.edge := by
  classical
  dsimp only [edgeProjEdge]
  simp only [h1, ↓reduceIte]

private lemma edgeProjEdge_eq_symm (W : WeightedGraph V) (d d' : W.graph.Dart)
    (h2 : d' = d.symm) (t : unitInterval) :
    edgeProjEdge W d d' t = (1 - (t : ℝ)) * W.weight d.edge := by
  classical
  dsimp only [edgeProjEdge]
  rw [h2]
  simp only [d.symm_ne, ↓reduceIte]

private lemma edgeProjEdge_of_edge_ne (W : WeightedGraph V) {d d' : W.graph.Dart}
    (hne : d'.edge ≠ d.edge) (t : unitInterval) :
    edgeProjEdge W d d' t = edgeProjVert W d d'.fst := by
  classical
  have h1 : d' ≠ d := fun h => hne (h ▸ rfl)
  have h2 : d' ≠ d.symm := fun h => hne (by rw [h, Dart.edge_symm])
  dsimp only [edgeProjEdge]
  simp only [h1, h2, ↓reduceIte]

/-- The `1`-Lipschitz projection of a tree metric graph onto `[0, W.weight d.edge]` along dart `d`,
sending the `d.fst`-component of `G \ {d.edge}` to `0`, the `d.snd`-component to `W.weight d.edge`,
and mapping edge `d` affinely. -/
noncomputable def edgeProj (hT : W.graph.IsTree) (d : W.graph.Dart) : MetricGraph W → ℝ :=
  MetricGraph.lift (edgeProjVert W d) (edgeProjEdge W d)
    (fun d' => by
      by_cases h1 : d' = d
      · rw [edgeProjEdge_eq_fst W d d' h1 0, h1, edgeProjVert_fst]
        simp
      · by_cases h2 : d' = d.symm
        · rw [edgeProjEdge_eq_symm W d d' h2 0, h2, Dart.fst_symm, edgeProjVert_snd hT]
          simp
        · have hne : d'.edge ≠ d.edge := fun he => by
            rcases (dart_edge_eq_iff d' d).mp he with heq | heq
            · exact h1 heq
            · exact h2 heq
          exact edgeProjEdge_of_edge_ne W hne 0)
    (fun d' => by
      by_cases h1 : d' = d
      · rw [edgeProjEdge_eq_fst W d d' h1 1, h1, edgeProjVert_snd hT]
        simp
      · by_cases h2 : d' = d.symm
        · rw [edgeProjEdge_eq_symm W d d' h2 1, h2]
          have hsnd : d.symm.snd = d.fst := rfl
          rw [hsnd, edgeProjVert_fst]
          simp
        · have hne : d'.edge ≠ d.edge := fun he => by
            rcases (dart_edge_eq_iff d' d).mp he with heq | heq
            · exact h1 heq
            · exact h2 heq
          rw [edgeProjEdge_of_edge_ne W hne 1]
          classical
          dsimp only [edgeProjVert]
          have hiff := reachable_deleteEdges_adj_iff d d' hne
          simp only [hiff])
    (fun d' t => by
      by_cases h1 : d' = d
      · have hs : d'.symm = d.symm := by rw [h1]
        rw [edgeProjEdge_eq_symm W d d'.symm hs, edgeProjEdge_eq_fst W d d' h1,
          unitInterval.coe_symm_eq]
        ring
      · by_cases h2 : d' = d.symm
        · have hs : d'.symm = d := by rw [h2, Dart.symm_symm]
          rw [edgeProjEdge_eq_fst W d d'.symm hs, edgeProjEdge_eq_symm W d d' h2,
            unitInterval.coe_symm_eq]
        · have hne : d'.edge ≠ d.edge := fun he => by
            rcases (dart_edge_eq_iff d' d).mp he with heq | heq
            · exact h1 heq
            · exact h2 heq
          have hne_s : d'.symm.edge ≠ d.edge := by simpa only [Dart.edge_symm] using hne
          rw [edgeProjEdge_of_edge_ne W hne_s, edgeProjEdge_of_edge_ne W hne]
          classical
          dsimp only [edgeProjVert]
          rw [Dart.fst_symm]
          have hiff := reachable_deleteEdges_adj_iff d d' hne
          simp only [hiff])

private theorem edgeProj_vertex_priv (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = edgeProjVert W d v :=
  lift_vertex _ _ _ _ _ v

theorem edgeProj_vertex_eq_zero_iff (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = 0 ↔ (W.graph.deleteEdges {d.edge}).Reachable v d.fst := by
  classical
  rw [edgeProj_vertex_priv]
  dsimp only [edgeProjVert]
  split_ifs with h
  · simp [h]
  · simp [h, (W.dart_weight_pos d).ne']

theorem edgeProj_vertex_eq_weight_iff (hT : W.graph.IsTree) (d : W.graph.Dart) (v : V) :
    edgeProj hT d (vertex v) = W.weight d.edge ↔
      ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst := by
  classical
  rw [edgeProj_vertex_priv]
  dsimp only [edgeProjVert]
  split_ifs with h
  · simp [h, (W.dart_weight_pos d).ne]
  · simp [h]

theorem edgeProj_edgePoint_self (hT : W.graph.IsTree) (d : W.graph.Dart) (t : unitInterval) :
    edgeProj hT d (edgePoint d t) = (t : ℝ) * W.weight d.edge := by
  rw [edgeProj, lift_edgePoint]
  exact edgeProjEdge_eq_fst W d d rfl t

theorem edgeProj_edgePoint_symm (hT : W.graph.IsTree) (d : W.graph.Dart) (t : unitInterval) :
    edgeProj hT d (edgePoint d.symm t) = (1 - (t : ℝ)) * W.weight d.edge := by
  rw [edgeProj, lift_edgePoint]
  exact edgeProjEdge_eq_symm W d d.symm rfl t

theorem edgeProj_edgePoint_of_edge_ne (hT : W.graph.IsTree) {d d' : W.graph.Dart}
    (hne : d'.edge ≠ d.edge) (t : unitInterval) :
    edgeProj hT d (edgePoint d' t) = edgeProj hT d (vertex d'.fst) := by
  rw [edgeProj, lift_edgePoint, edgeProjEdge_of_edge_ne W hne, lift_vertex]

theorem edgeProj_nonneg (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    0 ≤ edgeProj hT d x := by
  classical
  induction x using ind_simple with
  | vertex v =>
    rw [edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    split_ifs
    · exact le_rfl
    · exact W.dart_weight_nonneg d
  | edgePoint d' t =>
    by_cases hne : d'.edge = d.edge
    · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
      · subst d'
        rw [edgeProj_edgePoint_self]
        exact mul_nonneg t.2.1 (W.dart_weight_nonneg d)
      · subst d'
        rw [edgeProj_edgePoint_symm]
        exact mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d)
    · rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_priv]
      dsimp only [edgeProjVert]
      split_ifs
      · exact le_rfl
      · exact W.dart_weight_nonneg d

theorem edgeProj_le_weight (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d x ≤ W.weight d.edge := by
  classical
  induction x using ind_simple with
  | vertex v =>
    rw [edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    split_ifs
    · exact W.dart_weight_nonneg d
    · exact le_rfl
  | edgePoint d' t =>
    by_cases hne : d'.edge = d.edge
    · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
      · subst d'
        rw [edgeProj_edgePoint_self]
        exact mul_le_of_le_one_left (W.dart_weight_nonneg d) t.2.2
      · subst d'
        rw [edgeProj_edgePoint_symm]
        exact mul_le_of_le_one_left (W.dart_weight_nonneg d) (sub_le_self 1 t.2.1)
    · rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_priv]
      dsimp only [edgeProjVert]
      split_ifs
      · exact W.dart_weight_nonneg d
      · exact le_rfl

theorem edgeProj_symm (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d.symm x = W.weight d.edge - edgeProj hT d x := by
  classical
  induction x using ind_simple with
  | vertex v =>
    rw [edgeProj_vertex_priv, edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    rw [Dart.edge_symm, Dart.fst_symm]
    have hiff := reachable_deleteEdges_iff_not_reachable_snd hT d v
    simp only [hiff]
    split_ifs <;> ring
  | edgePoint d' t =>
    by_cases hne : d'.edge = d.edge
    · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
      · subst d'
        conv_lhs => rw [← edgePoint_symm d t]
        rw [edgeProj_edgePoint_self, Dart.edge_symm, edgeProj_edgePoint_self,
          unitInterval.coe_symm_eq]
        ring
      · subst d'
        rw [edgeProj_edgePoint_symm, edgeProj_edgePoint_self, Dart.edge_symm]
        ring
    · rw [edgeProj_edgePoint_of_edge_ne hT (by simpa only [Dart.edge_symm] using hne),
        edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_priv, edgeProj_vertex_priv]
      dsimp only [edgeProjVert]
      rw [Dart.edge_symm, Dart.fst_symm]
      have hiff := reachable_deleteEdges_iff_not_reachable_snd hT d d'.fst
      simp only [hiff]
      split_ifs <;> ring

theorem abs_sub_edgeProj_le_dist [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (x y : MetricGraph W) :
    |edgeProj hT d x - edgeProj hT d y| ≤ Dist.dist x y := by
  refine dist_map_le_of_edgePoint_dist_le (edgeProj hT d) (fun d' s t => ?_) x y
  rw [Real.dist_eq]
  by_cases hne : d'.edge = d.edge
  · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
    · subst d'
      rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_nonneg d)]
    · subst d'
      rw [edgeProj_edgePoint_symm, edgeProj_edgePoint_symm, Dart.edge_symm, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_nonneg d)]
      have heq : (1 - (s : ℝ)) - (1 - (t : ℝ)) = -((s : ℝ) - t) := by ring
      rw [heq, abs_neg]
  · rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_edgePoint_of_edge_ne hT hne,
      sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg _) (W.dart_weight_nonneg d')

private lemma walkLength_split_cut {G : SimpleGraph V} (w : Sym2 V → ℝ)
    (S : Set V) {u v : V} (hu : u ∈ S) (hv : v ∉ S) (p : G.Walk u v) :
    ∃ a b : V, ∃ _ : G.Adj a b, a ∈ S ∧ b ∉ S ∧
      ∃ (p₁ : G.Walk u a) (p₂ : G.Walk b v),
        walkLength w p₁ + w s(a, b) + walkLength w p₂ = walkLength w p := by
  induction p with
  | nil => exact absurd hu hv
  | @cons x y z hadj q ih =>
    by_cases hy : y ∈ S
    · obtain ⟨a, b, hab, ha, hb, p₁, p₂, hsum⟩ := ih hy hv
      refine ⟨a, b, hab, ha, hb, Walk.cons hadj p₁, p₂, ?_⟩
      rw [walkLength_cons, walkLength_cons, ← hsum]
      ring
    · exact ⟨x, y, hadj, hu, hy, Walk.nil, q, by simp [walkLength_cons]⟩

theorem vertexDist_eq_of_deleteEdges_cut [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {u v : V} (hu : (W.graph.deleteEdges {d.edge}).Reachable u d.fst)
    (hv : ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst) :
    vertexDist W.graph W.weight u v =
      vertexDist W.graph W.weight u d.fst + W.weight d.edge +
        vertexDist W.graph W.weight d.snd v := by
  have _ := hT
  refine le_antisymm ?_ ?_
  · have h1 := vertexDist_triangle W.weight_nonneg (W.connected u d.fst) (W.connected d.fst v)
    have h2 := vertexDist_triangle W.weight_nonneg (W.connected d.fst d.snd) (W.connected d.snd v)
    have h3 : vertexDist W.graph W.weight d.fst d.snd ≤ W.weight d.edge :=
      vertexDist_adj_le W.weight_nonneg d.adj
    linarith
  · obtain ⟨q, -, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
    obtain ⟨a, b, hab, ha, hb, p₁, p₂, hsum⟩ :=
      walkLength_split_cut W.weight
        {x | (W.graph.deleteEdges {d.edge}).Reachable x d.fst} hu hv q
    have he : s(a, b) = d.edge := by
      by_contra hne
      have hadj' : (W.graph.deleteEdges {d.edge}).Adj a b := ⟨hab, by simp [hne]⟩
      exact hb (hadj'.symm.reachable.trans ha)
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h1 := vertexDist_le W.weight_nonneg p₁
      have h2 := vertexDist_le W.weight_nonneg p₂
      change walkLength W.weight p₁ + W.weight d.edge + walkLength W.weight p₂ =
        walkLength W.weight q at hsum
      linarith
    · exact absurd (Reachable.refl d.fst) hb

theorem vertexDist_adj [Finite V] (hT : W.graph.IsTree) {u v : V} (h : W.graph.Adj u v) :
    vertexDist W.graph W.weight u v = W.weight s(u, v) := by
  let d : W.graph.Dart := ⟨(u, v), h⟩
  have hcut := vertexDist_eq_of_deleteEdges_cut hT d (.refl u)
    (fun hrev => bridge_deleteEdges hT d hrev.symm)
  simpa [d, vertexDist_self W.weight_nonneg] using hcut

/-- In a tree, every path between two vertices is a shortest path. -/
theorem walkLength_eq_vertexDist_of_isPath [Finite V] (hT : W.graph.IsTree) {a b : V}
    (p : W.graph.Walk a b) (hp : p.IsPath) :
    walkLength W.weight p = vertexDist W.graph W.weight a b := by
  obtain ⟨q, hqp, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected a b)
  have heq : (⟨p, hp⟩ : W.graph.Path a b) = ⟨q, hqp⟩ :=
    (hT.isAcyclic.subsingleton_path a b).elim _ _
  exact (congrArg (fun x => walkLength W.weight x.1) heq).trans hq

/-- In a tree, the vertices of a path from `a` to `b` lie on the interval between `a` and `b`. -/
theorem vertex_mem_interval_of_mem_support [Finite V] (hT : W.graph.IsTree) {a b w : V}
    {p : W.graph.Walk a b} (hp : p.IsPath) (hw : w ∈ p.support) :
    (vertex w : MetricGraph W) ∈ interval (vertex a) (vertex b) := by
  classical
  have hlen : walkLength W.weight (p.takeUntil w hw) + walkLength W.weight (p.dropUntil w hw) =
      walkLength W.weight p := by
    rw [← walkLength_append, Walk.take_spec p hw]
  rw [mem_interval_iff, dist_vertex, dist_vertex, dist_vertex,
    ← walkLength_eq_vertexDist_of_isPath hT _ (hp.takeUntil hw),
    ← walkLength_eq_vertexDist_of_isPath hT _ (hp.dropUntil hw),
    ← walkLength_eq_vertexDist_of_isPath hT p hp, hlen]

theorem dist_edgePoint_edgePoint_same_eq [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (s t : unitInterval) :
    Dist.dist (edgePoint d s : MetricGraph W) (edgePoint d t) =
      |(s : ℝ) - t| * W.weight d.edge := by
  rw [dist_edgePoint_eq_direct_of_vertexDist_eq (vertexDist_adj hT d.adj), mul_comm]

/-- Every point's projection onto dart `d` is `0`, `W.weight d.edge`, or realized by a strictly
interior point along `d`. -/
lemma edgeProj_cases (hT : W.graph.IsTree) (d : W.graph.Dart) (x : MetricGraph W) :
    edgeProj hT d x = 0 ∨ edgeProj hT d x = W.weight d.edge ∨
      ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ x = edgePoint d t := by
  classical
  induction x using ind with
  | vertex v =>
    rw [edgeProj_vertex_priv]
    dsimp only [edgeProjVert]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | edgePoint d' t ht0 ht1 =>
    by_cases hne : d'.edge = d.edge
    · rcases (dart_edge_eq_iff d' d).mp hne with hdd | hdd
      · subst d'
        exact Or.inr (Or.inr ⟨t, ht0, ht1, rfl⟩)
      · subst d'
        exact Or.inr (Or.inr ⟨unitInterval.symm t,
          by simp only [unitInterval.coe_symm_eq]; linarith,
          by simp only [unitInterval.coe_symm_eq]; linarith,
          (edgePoint_symm' d t).symm⟩)
    · rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_priv]
      dsimp only [edgeProjVert]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

private lemma edgePoint_edgeProj_zero_decomp (hT : W.graph.IsTree) (d d' : W.graph.Dart)
    {s : unitInterval} (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1)
    (hx : edgeProj hT d (edgePoint d' s) = 0) :
    d'.edge ≠ d.edge ∧
      (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst ∧
      (W.graph.deleteEdges {d.edge}).Reachable d'.snd d.fst := by
  have hne : d'.edge ≠ d.edge := by
    intro he
    rcases (dart_edge_eq_iff d' d).mp he with rfl | rfl
    · rw [edgeProj_edgePoint_self] at hx
      exact absurd ((mul_eq_zero.mp hx).resolve_right (W.dart_weight_pos d').ne') hs0.ne'
    · rw [edgeProj_edgePoint_symm] at hx
      have : 1 - (s : ℝ) = 0 := (mul_eq_zero.mp hx).resolve_right (W.dart_weight_pos d).ne'
      linarith
  have hf : (W.graph.deleteEdges {d.edge}).Reachable d'.fst d.fst := by
    rw [edgeProj_edgePoint_of_edge_ne hT hne, edgeProj_vertex_eq_zero_iff] at hx
    exact hx
  exact ⟨hne, hf, (reachable_deleteEdges_adj_iff d d' hne).mp hf⟩

theorem dist_edgePoint_of_edgeProj_zero [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x : MetricGraph W} (hx : edgeProj hT d x = 0) (t : unitInterval) :
    Dist.dist x (edgePoint d t) = Dist.dist x (vertex d.fst) + (t : ℝ) * W.weight d.edge := by
  induction x using ind with
  | vertex u =>
    have hu : (W.graph.deleteEdges {d.edge}).Reachable u d.fst :=
      (edgeProj_vertex_eq_zero_iff hT d u).mp hx
    have hcut := vertexDist_eq_of_deleteEdges_cut hT d hu
      (fun h => bridge_deleteEdges hT d h.symm)
    simp only [vertexDist_self W.weight_nonneg, add_zero] at hcut
    rw [dist_vertex_edgePoint, dist_vertex, hcut]
    have ht1 : (t : ℝ) * W.weight d.edge ≤ W.weight d.edge + (1 - t) * W.weight d.edge := by
      have hw := W.dart_weight_nonneg d
      have := t.2.2
      nlinarith
    exact min_eq_left (by linarith)
  | edgePoint d' s hs0 hs1 =>
    obtain ⟨hne, hf, hs⟩ := edgePoint_edgeProj_zero_decomp hT d d' hs0 hs1 hx
    have hns : ¬ (W.graph.deleteEdges {d.edge}).Reachable d.snd d.fst :=
      fun h => bridge_deleteEdges hT d h.symm
    have h1 := vertexDist_eq_of_deleteEdges_cut hT d hf hns
    have h2 := vertexDist_eq_of_deleteEdges_cut hT d hs hns
    simp only [vertexDist_self W.weight_nonneg, add_zero] at h1 h2
    rw [dist_edgePoint_edgePoint_of_edge_ne hne, dist_edgePoint_vertex, h1, h2]
    have ht1 : (t : ℝ) * W.weight d.edge ≤ W.weight d.edge + (1 - t) * W.weight d.edge := by
      have hw := W.dart_weight_nonneg d
      have := t.2.2
      nlinarith
    simp only [add_assoc]
    simp only [← add_min, min_eq_left ht1]
    simp only [← add_assoc]
    rw [← min_add, vertexDist_comm d'.fst d.fst, vertexDist_comm d'.snd d.fst]

private lemma vertex_snd_dist_of_edgeProj_zero [Finite V] (hT : W.graph.IsTree)
    (d : W.graph.Dart) {x : MetricGraph W} (hx : edgeProj hT d x = 0) :
    Dist.dist x (vertex d.snd) = Dist.dist x (vertex d.fst) + W.weight d.edge := by
  have h := dist_edgePoint_of_edgeProj_zero hT d hx 1
  simpa only [edgePoint_one, Set.Icc.coe_one, one_mul] using h

theorem dist_of_edgeProj_zero_eq_weight [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y : MetricGraph W} (hx : edgeProj hT d x = 0) (hy : edgeProj hT d y = W.weight d.edge) :
    Dist.dist x y =
      Dist.dist x (vertex d.fst) + W.weight d.edge + Dist.dist (vertex d.snd) y := by
  have hy_symm : edgeProj hT d.symm y = 0 := by
    rw [edgeProj_symm, hy, sub_self]
  induction x using ind with
  | vertex u =>
    have hu : (W.graph.deleteEdges {d.edge}).Reachable u d.fst :=
      (edgeProj_vertex_eq_zero_iff hT d u).mp hx
    induction y using ind with
    | vertex v =>
      have hv : ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst :=
        (edgeProj_vertex_eq_weight_iff hT d v).mp hy
      simpa only [dist_vertex] using vertexDist_eq_of_deleteEdges_cut hT d hu hv
    | edgePoint d₂ t ht0 ht1 =>
      obtain ⟨hne', hf_sym, _⟩ := edgePoint_edgeProj_zero_decomp hT d.symm d₂ ht0 ht1 hy_symm
      rw [Dart.edge_symm] at hne' hf_sym
      have hf : ¬ (W.graph.deleteEdges {d.edge}).Reachable d₂.fst d.fst := fun hr =>
        bridge_deleteEdges hT d (hr.symm.trans hf_sym)
      have hs : ¬ (W.graph.deleteEdges {d.edge}).Reachable d₂.snd d.fst := fun hr =>
        hf ((reachable_deleteEdges_adj_iff d d₂ hne').mpr hr)
      have h1 := vertexDist_eq_of_deleteEdges_cut hT d hu hf
      have h2 := vertexDist_eq_of_deleteEdges_cut hT d hu hs
      rw [dist_vertex_edgePoint, dist_vertex, dist_vertex_edgePoint, h1, h2]
      simp only [add_assoc, ← add_min]
  | edgePoint d₁ s hs0 hs1 =>
    obtain ⟨hne₁, hf₁, hs₁⟩ := edgePoint_edgeProj_zero_decomp hT d d₁ hs0 hs1 hx
    induction y using ind with
    | vertex v =>
      have hv : ¬ (W.graph.deleteEdges {d.edge}).Reachable v d.fst :=
        (edgeProj_vertex_eq_weight_iff hT d v).mp hy
      have h1 := vertexDist_eq_of_deleteEdges_cut hT d hf₁ hv
      have h2 := vertexDist_eq_of_deleteEdges_cut hT d hs₁ hv
      rw [dist_edgePoint_vertex, dist_edgePoint_vertex, dist_vertex, h1, h2,
        vertexDist_comm d₁.fst d.fst, vertexDist_comm d₁.snd d.fst]
      simp only [← add_assoc, ← min_add]
    | edgePoint d₂ t ht0 ht1 =>
      obtain ⟨hne₂, hf₂_sym, _⟩ := edgePoint_edgeProj_zero_decomp hT d.symm d₂ ht0 ht1 hy_symm
      rw [Dart.edge_symm] at hne₂ hf₂_sym
      have hf₂ : ¬ (W.graph.deleteEdges {d.edge}).Reachable d₂.fst d.fst := fun hr =>
        bridge_deleteEdges hT d (hr.symm.trans hf₂_sym)
      have hs₂ : ¬ (W.graph.deleteEdges {d.edge}).Reachable d₂.snd d.fst := fun hr =>
        hf₂ ((reachable_deleteEdges_adj_iff d d₂ hne₂).mpr hr)
      have hne₁₂ : d₁.edge ≠ d₂.edge := by
        intro he
        rcases (dart_edge_eq_iff d₁ d₂).mp he with h | h
        · exact hf₂ (h ▸ hf₁)
        · have hf_snd : d₁.fst = d₂.snd := by rw [h]; rfl
          exact hs₂ (hf_snd ▸ hf₁)
      have hff := vertexDist_eq_of_deleteEdges_cut hT d hf₁ hf₂
      have hfs := vertexDist_eq_of_deleteEdges_cut hT d hf₁ hs₂
      have hsf := vertexDist_eq_of_deleteEdges_cut hT d hs₁ hf₂
      have hss := vertexDist_eq_of_deleteEdges_cut hT d hs₁ hs₂
      rw [dist_edgePoint_edgePoint_of_edge_ne hne₁₂, dist_edgePoint_vertex, dist_vertex_edgePoint,
        hff, hfs, hsf, hss, vertexDist_comm d₁.fst d.fst, vertexDist_comm d₁.snd d.fst]
      simp only [add_assoc]
      simp only [← add_min]
      simp only [← add_assoc]
      rw [← min_add, ← min_add]

theorem dist_edgePoint_of_edgeProj_weight [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x : MetricGraph W} (hx : edgeProj hT d x = W.weight d.edge) (t : unitInterval) :
    Dist.dist x (edgePoint d t) =
      Dist.dist x (vertex d.snd) + (1 - (t : ℝ)) * W.weight d.edge := by
  have hx' : edgeProj hT d.symm x = 0 := by rw [edgeProj_symm, hx, sub_self]
  rw [← edgePoint_symm d t]
  simpa only [Dart.fst_symm, Dart.edge_symm, unitInterval.coe_symm_eq] using
    dist_edgePoint_of_edgeProj_zero hT d.symm hx' (unitInterval.symm t)

theorem vertex_fst_mem_interval_of_edgeProj [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {y z : MetricGraph W} (hy : edgeProj hT d y = 0) (hz : 0 < edgeProj hT d z) :
    vertex d.fst ∈ interval y z := by
  rw [mem_interval_iff]
  rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
  · linarith
  · have h1 := dist_of_edgeProj_zero_eq_weight hT d hy hzw
    have h2 := dist_edgePoint_of_edgeProj_weight hT d hzw 0
    simp only [edgePoint_zero, Set.Icc.coe_zero, sub_zero, one_mul] at h2
    rw [_root_.dist_comm (vertex d.fst) z, h2, h1, _root_.dist_comm z (vertex d.snd)]
    ring
  · have h1 := dist_edgePoint_of_edgeProj_zero hT d hy sz
    have h2 := dist_edgePoint_edgePoint_same_eq hT d 0 sz
    simp only [edgePoint_zero, Set.Icc.coe_zero, zero_sub, abs_neg,
      abs_of_nonneg sz.2.1] at h2
    rw [h1, h2]

theorem edgePoint_mem_interval_of_edgeProj_le [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {y z : MetricGraph W} {t : unitInterval} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (hy : edgeProj hT d y ≤ (t : ℝ) * W.weight d.edge)
    (hz : (t : ℝ) * W.weight d.edge ≤ edgeProj hT d z) :
    edgePoint d t ∈ interval y z := by
  rw [mem_interval_iff]
  have hwpos := W.dart_weight_pos d
  rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
  · rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
    · have : (t : ℝ) * W.weight d.edge ≤ 0 := hz0 ▸ hz
      nlinarith
    · have hxy := dist_of_edgeProj_zero_eq_weight hT d hy0 hzw
      have hy1 := dist_edgePoint_of_edgeProj_zero hT d hy0 t
      have hz1 := dist_edgePoint_of_edgeProj_weight hT d hzw t
      rw [_root_.dist_comm (edgePoint d t) z, hz1, hy1, hxy, _root_.dist_comm z (vertex d.snd)]
      ring
    · rw [edgeProj_edgePoint_self] at hz
      have htz : (t : ℝ) ≤ sz := (mul_le_mul_iff_left₀ hwpos).mp hz
      have hxy := dist_edgePoint_of_edgeProj_zero hT d hy0 sz
      have hym := dist_edgePoint_of_edgeProj_zero hT d hy0 t
      have hmz := dist_edgePoint_edgePoint_same_eq hT d t sz
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htz)] at hmz
      rw [hxy, hym, hmz]
      ring
  · have : W.weight d.edge ≤ (t : ℝ) * W.weight d.edge := hyw ▸ hy
    nlinarith
  · rw [edgeProj_edgePoint_self] at hy
    have hsy_le : (sy : ℝ) ≤ t := (mul_le_mul_iff_left₀ hwpos).mp hy
    rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
    · have : (t : ℝ) * W.weight d.edge ≤ 0 := hz0 ▸ hz
      nlinarith
    · have hyz := dist_edgePoint_of_edgeProj_weight hT d hzw sy
      have hmz := dist_edgePoint_of_edgeProj_weight hT d hzw t
      have hym := dist_edgePoint_edgePoint_same_eq hT d sy t
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsy_le)] at hym
      rw [_root_.dist_comm (edgePoint d sy) z, _root_.dist_comm (edgePoint d t) z, hyz, hmz, hym]
      ring
    · rw [edgeProj_edgePoint_self] at hz
      have htz : (t : ℝ) ≤ sz := (mul_le_mul_iff_left₀ hwpos).mp hz
      have h1 := dist_edgePoint_edgePoint_same_eq hT d sy t
      have h2 := dist_edgePoint_edgePoint_same_eq hT d t sz
      have h3 := dist_edgePoint_edgePoint_same_eq hT d sy sz
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsy_le)] at h1
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htz)] at h2
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hsy_le.trans htz))] at h3
      rw [h1, h2, h3]
      ring

/-- In a tree, the zero set of a bridge projection is convex: it contains the interval between any
two of its points. -/
theorem edgeProj_eq_zero_of_mem_interval [Finite V] (hT : W.graph.IsTree) {d : W.graph.Dart}
    {p q z : MetricGraph W} (hp : edgeProj hT d p = 0) (hq : edgeProj hT d q = 0)
    (hz : z ∈ interval p q) : edgeProj hT d z = 0 := by
  by_contra hne
  have hpos : 0 < edgeProj hT d z := lt_of_le_of_ne (edgeProj_nonneg hT d z) (Ne.symm hne)
  have hm₁ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hp hpos)
  have hm₂ := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hq hpos)
  have hz_mem := mem_interval_iff.mp hz
  have hd_pos : 0 < Dist.dist (vertex d.fst : MetricGraph W) z := by
    refine _root_.dist_pos.mpr fun heq => ?_
    have h0 : edgeProj hT d (vertex d.fst) = 0 :=
      (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)
    rw [heq] at h0
    exact hne h0
  linarith [_root_.dist_triangle p (vertex d.fst) q,
    _root_.dist_comm (vertex d.fst : MetricGraph W) z, _root_.dist_comm q z,
    _root_.dist_comm q (vertex d.fst)]

/-- In a tree, every point of an edge lies on the interval between the edge's endpoints. -/
theorem edgePoint_mem_interval_vertex [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    (t : unitInterval) : edgePoint d t ∈ interval (vertex d.fst) (vertex d.snd) := by
  rw [mem_interval_iff, ← edgePoint_zero d, ← edgePoint_one d,
    dist_edgePoint_edgePoint_same_eq hT d 0 t, dist_edgePoint_edgePoint_same_eq hT d t 1,
    dist_edgePoint_edgePoint_same_eq hT d 0 1, Set.Icc.coe_zero, Set.Icc.coe_one,
    abs_of_nonpos (by linarith [t.2.1] : (0 : ℝ) - t ≤ 0),
    abs_of_nonpos (by linarith [t.2.2] : (t : ℝ) - 1 ≤ 0),
    abs_of_nonpos (by norm_num : (0 : ℝ) - 1 ≤ 0)]
  ring

end TreeProjection

/-! ### Uniqueness of geodesics and metric intervals -/

section TreeGeodesic

private lemma dist_add_dist_gt_of_edgeProj_lt [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z : MetricGraph W} (hzx : edgeProj hT d z < edgeProj hT d x)
    (hzy : edgeProj hT d z < edgeProj hT d y) :
    Dist.dist x y < Dist.dist x z + Dist.dist z y := by
  have hwpos := W.dart_weight_pos d
  rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, _, rfl⟩
  · rw [hz0] at hzx hzy
    have hzx' := vertex_fst_mem_interval_of_edgeProj hT d hz0 hzx
    have hzy' := vertex_fst_mem_interval_of_edgeProj hT d hz0 hzy
    rw [mem_interval_iff, _root_.dist_comm z x, _root_.dist_comm (vertex d.fst) x] at hzx'
    rw [mem_interval_iff] at hzy'
    have hge : Dist.dist x z + Dist.dist z y ≥
        Dist.dist x (vertex d.fst) + Dist.dist (vertex d.fst) y := by
      linarith [_root_.dist_nonneg (x := z) (y := vertex d.fst)]
    rcases edgeProj_cases hT d x with hx0 | hxw | ⟨sx, _, _, rfl⟩
    · linarith
    · rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
      · linarith
      · have hx_d := dist_edgePoint_of_edgeProj_weight hT d hxw 0
        have hy_d := dist_edgePoint_of_edgeProj_weight hT d hyw 0
        simp only [edgePoint_zero, Set.Icc.coe_zero, sub_zero, one_mul] at hx_d hy_d
        have htri := _root_.dist_triangle x (vertex d.snd) y
        rw [_root_.dist_comm x (vertex d.snd)] at htri
        linarith [_root_.dist_comm x (vertex d.fst), _root_.dist_comm y (vertex d.fst),
          _root_.dist_comm x (vertex d.snd), _root_.dist_comm y (vertex d.snd), hwpos]
      · have hx_d := dist_edgePoint_of_edgeProj_weight hT d hxw 0
        have hy_d := dist_edgePoint_edgePoint_same_eq hT d 0 sy
        have hxy := dist_edgePoint_of_edgeProj_weight hT d hxw sy
        simp only [edgePoint_zero, Set.Icc.coe_zero, sub_zero, one_mul, zero_sub, abs_neg,
          abs_of_nonneg sy.2.1] at hx_d hy_d
        have : (1 - (sy : ℝ)) * W.weight d.edge < W.weight d.edge + (sy : ℝ) * W.weight d.edge := by
          nlinarith
        linarith
    · rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
      · linarith
      · have hx_d := dist_edgePoint_edgePoint_same_eq hT d 0 sx
        have hy_d := dist_edgePoint_of_edgeProj_weight hT d hyw 0
        have hxy := dist_edgePoint_of_edgeProj_weight hT d hyw sx
        simp only [edgePoint_zero, Set.Icc.coe_zero, sub_zero, one_mul, zero_sub, abs_neg,
          abs_of_nonneg sx.2.1] at hx_d hy_d
        have : (1 - (sx : ℝ)) * W.weight d.edge < (sx : ℝ) * W.weight d.edge + W.weight d.edge := by
          nlinarith
        linarith [_root_.dist_comm (edgePoint d sx) y,
          _root_.dist_comm (edgePoint d sx) (vertex d.fst), _root_.dist_comm y (vertex d.fst)]
      · have hx_d := dist_edgePoint_edgePoint_same_eq hT d 0 sx
        have hy_d := dist_edgePoint_edgePoint_same_eq hT d 0 sy
        have hxy := dist_edgePoint_edgePoint_same_eq hT d sx sy
        simp only [edgePoint_zero, Set.Icc.coe_zero, zero_sub, abs_neg,
          abs_of_nonneg sx.2.1, abs_of_nonneg sy.2.1] at hx_d hy_d
        rw [hxy]
        rcases le_total (sx : ℝ) sy with hle | hle
        · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
          have : ((sy : ℝ) - sx) * W.weight d.edge < (sx : ℝ) * W.weight d.edge +
              (sy : ℝ) * W.weight d.edge := by nlinarith
          linarith [_root_.dist_comm (edgePoint d sx) (vertex d.fst)]
        · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
          have : ((sx : ℝ) - sy) * W.weight d.edge < (sx : ℝ) * W.weight d.edge +
              (sy : ℝ) * W.weight d.edge := by nlinarith
          linarith [_root_.dist_comm (edgePoint d sx) (vertex d.fst)]
  · linarith [edgeProj_le_weight hT d x]
  · rw [edgeProj_edgePoint_self] at hzx hzy
    rcases edgeProj_cases hT d x with hx0 | hxw | ⟨sx, _, _, rfl⟩
    · linarith [mul_nonneg sz.2.1 hwpos.le]
    · rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
      · linarith [mul_nonneg sz.2.1 hwpos.le]
      · have h1 := dist_edgePoint_of_edgeProj_weight hT d hxw sz
        have h2 := dist_edgePoint_of_edgeProj_weight hT d hyw sz
        have htri := _root_.dist_triangle x (vertex d.snd) y
        rw [_root_.dist_comm (edgePoint d sz) y, h1, h2]
        have : 0 < (1 - (sz : ℝ)) * W.weight d.edge := mul_pos (by linarith) hwpos
        linarith [_root_.dist_comm x (vertex d.snd), _root_.dist_comm y (vertex d.snd)]
      · rw [edgeProj_edgePoint_self] at hzy
        have hszy : (sz : ℝ) < sy := (mul_lt_mul_iff_left₀ hwpos).mp hzy
        have h1 := dist_edgePoint_of_edgeProj_weight hT d hxw sz
        have h2 := dist_edgePoint_edgePoint_same_eq hT d sz sy
        have hxy := dist_edgePoint_of_edgeProj_weight hT d hxw sy
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hszy.le)] at h2
        rw [h1, h2, hxy]
        nlinarith
    · rw [edgeProj_edgePoint_self] at hzx
      have hszx : (sz : ℝ) < sx := (mul_lt_mul_iff_left₀ hwpos).mp hzx
      rcases edgeProj_cases hT d y with hy0 | hyw | ⟨sy, _, _, rfl⟩
      · linarith [mul_nonneg sz.2.1 hwpos.le]
      · have h1 := dist_edgePoint_edgePoint_same_eq hT d sx sz
        have h2 := dist_edgePoint_of_edgeProj_weight hT d hyw sz
        have hxy := dist_edgePoint_of_edgeProj_weight hT d hyw sx
        rw [abs_of_nonneg (sub_nonneg.mpr hszx.le)] at h1
        rw [_root_.dist_comm (edgePoint d sx) y, _root_.dist_comm (edgePoint d sz) y, h1, h2, hxy]
        nlinarith
      · rw [edgeProj_edgePoint_self] at hzy
        have hszy : (sz : ℝ) < sy := (mul_lt_mul_iff_left₀ hwpos).mp hzy
        have h1 := dist_edgePoint_edgePoint_same_eq hT d sx sz
        have h2 := dist_edgePoint_edgePoint_same_eq hT d sz sy
        have hxy := dist_edgePoint_edgePoint_same_eq hT d sx sy
        rw [abs_of_nonneg (sub_nonneg.mpr hszx.le)] at h1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hszy.le)] at h2
        rw [h1, h2, hxy]
        rcases le_total (sx : ℝ) sy with hle | hle
        · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
          nlinarith
        · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
          nlinarith

private lemma mem_interval_edgeProj_bounds [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z : MetricGraph W} (hz : z ∈ interval x y)
    (hxy : edgeProj hT d x ≤ edgeProj hT d y) :
    edgeProj hT d x ≤ edgeProj hT d z ∧ edgeProj hT d z ≤ edgeProj hT d y := by
  have hxzy := mem_interval_iff.mp hz
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    exact (dist_add_dist_gt_of_edgeProj_lt hT d hlt (hlt.trans_le hxy)).ne hxzy.symm
  · by_contra hlt
    push Not at hlt
    have hzx : edgeProj hT d.symm z < edgeProj hT d.symm x := by
      rw [edgeProj_symm, edgeProj_symm]
      linarith
    have hzy : edgeProj hT d.symm z < edgeProj hT d.symm y := by
      rw [edgeProj_symm, edgeProj_symm]
      linarith
    exact (dist_add_dist_gt_of_edgeProj_lt hT d.symm hzx hzy).ne hxzy.symm

private lemma dist_lt_of_edgeProj_lt [Finite V] (hT : W.graph.IsTree) (d : W.graph.Dart)
    {x y z₁ z₂ : MetricGraph W} (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y)
    (hxy : edgeProj hT d x ≤ edgeProj hT d y) (hlt : edgeProj hT d z₁ < edgeProj hT d z₂) :
    Dist.dist x z₁ < Dist.dist x z₂ := by
  have hb₁ := mem_interval_edgeProj_bounds hT d hz₁ hxy
  have hb₂ := mem_interval_edgeProj_bounds hT d hz₂ hxy
  have hwpos := W.dart_weight_pos d
  rcases edgeProj_cases hT d z₁ with h10 | h1w | ⟨s₁, _, hs11, rfl⟩
  · have hx0 : edgeProj hT d x = 0 :=
      le_antisymm (h10 ▸ hb₁.1) (edgeProj_nonneg hT d x)
    have hypos : 0 < edgeProj hT d y := by linarith
    have hz₂pos : 0 < edgeProj hT d z₂ := by linarith
    have hxy_f := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hx0 hypos)
    have hzy_f := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d h10 hypos)
    have hxz₁_eq := mem_interval_iff.mp hz₁
    have hxz₁_le : Dist.dist x z₁ ≤ Dist.dist x (vertex d.fst) := by
      linarith [_root_.dist_nonneg (x := z₁) (y := vertex d.fst)]
    have hxz₂_f := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hx0 hz₂pos)
    have h2 : edgeProj hT d z₂ ≤ Dist.dist (vertex d.fst) z₂ := by
      have := abs_sub_edgeProj_le_dist hT d z₂ (vertex d.fst)
      have hv0 : edgeProj hT d (vertex d.fst) = 0 :=
        (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)
      rw [hv0, sub_zero, abs_of_nonneg (edgeProj_nonneg hT d z₂), _root_.dist_comm] at this
      exact this
    linarith
  · linarith [edgeProj_le_weight hT d z₂]
  · have hs₁_eq : edgeProj hT d (edgePoint d s₁) = (s₁ : ℝ) * W.weight d.edge :=
      edgeProj_edgePoint_self hT d s₁
    have h2 : edgeProj hT d z₂ - edgeProj hT d x ≤ Dist.dist x z₂ := by
      have := abs_sub_edgeProj_le_dist hT d z₂ x
      rw [_root_.dist_comm] at this
      exact (le_abs_self _).trans this
    rcases edgeProj_cases hT d x with hx0 | hxw | ⟨sx, _, _, rfl⟩
    · have hxz₁ := dist_edgePoint_of_edgeProj_zero hT d hx0 s₁
      have hx_le : Dist.dist x (vertex d.fst) + edgeProj hT d z₂ ≤ Dist.dist x z₂ := by
        rcases edgeProj_cases hT d z₂ with hz20 | hz2w | ⟨s₂, _, _, rfl⟩
        · linarith [mul_nonneg s₁.2.1 hwpos.le]
        · rw [dist_of_edgeProj_zero_eq_weight hT d hx0 hz2w, hz2w]
          linarith [_root_.dist_nonneg (x := vertex d.snd) (y := z₂)]
        · rw [dist_edgePoint_of_edgeProj_zero hT d hx0 s₂, edgeProj_edgePoint_self]
      linarith [hs₁_eq ▸ hlt]
    · have hle : edgeProj hT d x ≤ (s₁ : ℝ) * W.weight d.edge := hs₁_eq ▸ hb₁.1
      rw [hxw] at hle
      nlinarith
    · have hsx_le : (sx : ℝ) ≤ s₁ := by
        rw [edgeProj_edgePoint_self, hs₁_eq] at hb₁
        exact (mul_le_mul_iff_left₀ hwpos).mp hb₁.1
      have hxz₁ := dist_edgePoint_edgePoint_same_eq hT d sx s₁
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hsx_le)] at hxz₁
      rw [edgeProj_edgePoint_self] at h2
      rw [hxz₁]
      linarith [hs₁_eq ▸ hlt]

private lemma eq_of_forall_edgeProj_eq (hT : W.graph.IsTree) {z₁ z₂ : MetricGraph W}
    (h : ∀ d : W.graph.Dart, edgeProj hT d z₁ = edgeProj hT d z₂) : z₁ = z₂ := by
  induction z₁ using ind with
  | vertex u =>
    induction z₂ using ind with
    | vertex v =>
      by_contra hne
      have huv : u ≠ v := fun huv => hne (huv ▸ rfl)
      obtain ⟨p, hp⟩ := (W.connected u v).exists_isPath
      have hnn : ¬ p.Nil := Walk.not_nil_of_ne huv
      let d : W.graph.Dart := p.firstDart hnn
      have h0 : edgeProj hT d (vertex u) = 0 :=
        (edgeProj_vertex_eq_zero_iff hT d u).mpr (.refl _)
      have hw : edgeProj hT d (vertex v) = W.weight d.edge := by
        rw [edgeProj_vertex_eq_weight_iff]
        intro hreach
        have htail_avoid : d.fst ∉ p.tail.support := by
          have hnodup := hp.support_nodup
          rw [← p.cons_tail_eq hnn, Walk.support_cons, List.nodup_cons] at hnodup
          exact hnodup.1
        have htail_edges : d.edge ∉ p.tail.edges := by
          intro hmem
          have hmem' : s(d.fst, d.snd) ∈ p.tail.edges := hmem
          exact htail_avoid (p.tail.fst_mem_support_of_mem_edges hmem')
        have hdsnd : (W.graph.deleteEdges {d.edge}).Reachable d.snd v :=
          ⟨p.tail.toDeleteEdges {d.edge} (fun e he hmem => by
            rw [Set.mem_singleton_iff] at hmem
            exact htail_edges (hmem ▸ he))⟩
        exact bridge_deleteEdges hT d (hdsnd.trans hreach).symm
      have := h d
      linarith [W.dart_weight_pos d]
    | edgePoint d₂ t₂ ht0 ht1 =>
      have h1 := h d₂
      rw [edgeProj_edgePoint_self] at h1
      rcases edgeProj_cases hT d₂ (vertex u) with h0 | hw | ⟨s, hs0, hs1, heq⟩
      · have : (t₂ : ℝ) * W.weight d₂.edge = 0 := h1 ▸ h0
        have := (mul_eq_zero.mp this).resolve_right (W.dart_weight_pos d₂).ne'
        linarith
      · have : (t₂ : ℝ) * W.weight d₂.edge = W.weight d₂.edge := h1 ▸ hw
        have : (t₂ : ℝ) = 1 :=
          mul_right_cancel₀ (W.dart_weight_pos d₂).ne' (by simpa only [one_mul] using this)
        linarith
      · exact absurd heq.symm (fun he => by
          rcases (edgePoint_eq_vertex_iff (d := d₂) (t := s) (v := u)).mp he with
            ⟨hs, _⟩ | ⟨hs, _⟩
          · rw [hs, Set.Icc.coe_zero] at hs0
            exact lt_irrefl 0 hs0
          · rw [hs, Set.Icc.coe_one] at hs1
            exact lt_irrefl 1 hs1)
  | edgePoint d₁ t₁ ht10 ht11 =>
    have h1 := h d₁
    rw [edgeProj_edgePoint_self] at h1
    rcases edgeProj_cases hT d₁ z₂ with h0 | hw | ⟨t₂, _, _, rfl⟩
    · have : (t₁ : ℝ) * W.weight d₁.edge = 0 := h1.trans h0
      have := (mul_eq_zero.mp this).resolve_right (W.dart_weight_pos d₁).ne'
      linarith
    · have : (t₁ : ℝ) * W.weight d₁.edge = W.weight d₁.edge := h1.trans hw
      have : (t₁ : ℝ) = 1 :=
        mul_right_cancel₀ (W.dart_weight_pos d₁).ne' (by simpa only [one_mul] using this)
      linarith
    · rw [edgeProj_edgePoint_self] at h1
      have : t₁ = t₂ := Subtype.ext (mul_right_cancel₀ (W.dart_weight_pos d₁).ne' h1)
      rw [this]

/-- In a tree metric graph, two points on `interval x y` at equal distance from `x` are equal. -/
theorem eq_of_mem_interval_dist_eq [Finite V] (hT : W.graph.IsTree) {x y z₁ z₂ : MetricGraph W}
    (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y) (hd : Dist.dist x z₁ = Dist.dist x z₂) :
    z₁ = z₂ := by
  refine eq_of_forall_edgeProj_eq hT fun d => ?_
  by_contra hne
  rcases le_total (edgeProj hT d x) (edgeProj hT d y) with hxy | hyx
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (dist_lt_of_edgeProj_lt hT d hz₁ hz₂ hxy hlt).ne hd
    · exact (dist_lt_of_edgeProj_lt hT d hz₂ hz₁ hxy hgt).ne hd.symm
  · have hz₁' : z₁ ∈ interval y x := interval_comm x y ▸ hz₁
    have hz₂' : z₂ ∈ interval y x := interval_comm x y ▸ hz₂
    have hdy : Dist.dist y z₁ = Dist.dist y z₂ := by
      have e1 := mem_interval_iff.mp hz₁
      have e2 := mem_interval_iff.mp hz₂
      rw [_root_.dist_comm y z₁, _root_.dist_comm y z₂]
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (dist_lt_of_edgeProj_lt hT d hz₁' hz₂' hyx hlt).ne hdy
    · exact (dist_lt_of_edgeProj_lt hT d hz₂' hz₁' hyx hgt).ne hdy.symm

/-- Geodesics between two points in a tree metric graph are unique on `[0, dist x y]`. -/
theorem IsGeodesic.eq_on [Finite V] (hT : W.graph.IsTree) {x y : MetricGraph W}
    {γ₁ γ₂ : ℝ → MetricGraph W} (h₁ : IsGeodesic x y γ₁) (h₂ : IsGeodesic x y γ₂)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (Dist.dist x y)) : γ₁ t = γ₂ t := by
  refine eq_of_mem_interval_dist_eq hT (h₁.mem_interval ht) (h₂.mem_interval ht) ?_
  calc Dist.dist x (γ₁ t) = Dist.dist (γ₁ 0) (γ₁ t) := by rw [h₁.map_zero]
    _ = |0 - t| := h₁.dist_eq ⟨le_rfl, _root_.dist_nonneg⟩ ht
    _ = Dist.dist (γ₂ 0) (γ₂ t) := (h₂.dist_eq ⟨le_rfl, _root_.dist_nonneg⟩ ht).symm
    _ = Dist.dist x (γ₂ t) := by rw [h₂.map_zero]

theorem interval_dist_eq_abs [Finite V] (hT : W.graph.IsTree) {x y z₁ z₂ : MetricGraph W}
    (hz₁ : z₁ ∈ interval x y) (hz₂ : z₂ ∈ interval x y) :
    Dist.dist z₁ z₂ = |Dist.dist x z₁ - Dist.dist x z₂| := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic x y
  obtain ⟨γ₁, hγ₁, h1⟩ := exists_isGeodesic_through_of_mem_interval hz₁
  obtain ⟨γ₂, hγ₂, h2⟩ := exists_isGeodesic_through_of_mem_interval hz₂
  have hmem1 : Dist.dist x z₁ ∈ Set.Icc 0 (Dist.dist x y) :=
    ⟨_root_.dist_nonneg,
      by linarith [mem_interval_iff.mp hz₁, _root_.dist_nonneg (x := z₁) (y := y)]⟩
  have hmem2 : Dist.dist x z₂ ∈ Set.Icc 0 (Dist.dist x y) :=
    ⟨_root_.dist_nonneg,
      by linarith [mem_interval_iff.mp hz₂, _root_.dist_nonneg (x := z₂) (y := y)]⟩
  conv_lhs =>
    rw [← h1, ← h2, hγ₁.eq_on hT hγ hmem1, hγ₂.eq_on hT hγ hmem2, hγ.dist_eq hmem1 hmem2]

theorem mem_interval_of_mem_interval_dist_le [Finite V] (hT : W.graph.IsTree)
    {x y z w : MetricGraph W} (hz : z ∈ interval x y) (hw : w ∈ interval x y)
    (hle : Dist.dist x z ≤ Dist.dist x w) : z ∈ interval x w := by
  rw [mem_interval_iff, interval_dist_eq_abs hT hz hw, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hle)]
  ring

theorem interval_subset_of_mem [Finite V] (hT : W.graph.IsTree) {x y u v : MetricGraph W}
    (hu : u ∈ interval x y) (hv : v ∈ interval x y) : interval u v ⊆ interval x y := by
  wlog huv : Dist.dist x u ≤ Dist.dist x v generalizing u v
  · rw [interval_comm u v]
    exact this hv hu (le_of_not_ge huv)
  intro z hz
  have hu' : u ∈ interval x v := mem_interval_of_mem_interval_dist_le hT hu hv huv
  have hxz : z ∈ interval x v := by
    have e1 := mem_interval_iff.mp hz
    have e2 := mem_interval_iff.mp hu'
    rw [mem_interval_iff]
    linarith [_root_.dist_triangle x u z, _root_.dist_triangle x z v]
  exact mem_interval_trans_left hv hxz

theorem isClosed_interval [Finite V] (x y : MetricGraph W) :
    IsClosed (interval x y) :=
  isClosed_eq ((continuous_const.dist continuous_id).add (continuous_id.dist continuous_const))
    continuous_const

/-- In a tree metric graph, the interval between `a` and `b` is the image of an isometric
parametrization of `[0, dist a b]` from `a` to `b`. -/
theorem exists_isometry_interval [Finite V] (hT : W.graph.IsTree) (a b : MetricGraph W) :
    ∃ φ : Set.Icc (0 : ℝ) (Dist.dist a b) → MetricGraph W,
      Isometry φ ∧
      φ ⟨0, le_rfl, _root_.dist_nonneg⟩ = a ∧
      φ ⟨Dist.dist a b, _root_.dist_nonneg, le_rfl⟩ = b ∧
      Set.range φ = interval a b := by
  obtain ⟨γ, hγ⟩ := exists_isGeodesic a b
  refine ⟨fun t => γ t.1, hγ.isometry, hγ.map_zero, hγ.map_dist, Set.ext fun z => ?_⟩
  constructor
  · rintro ⟨t, rfl⟩
    exact hγ.mem_interval t.2
  · intro hz
    obtain ⟨γ', hγ', hgz⟩ := exists_isGeodesic_through_of_mem_interval hz
    have hmem : Dist.dist a z ∈ Set.Icc 0 (Dist.dist a b) :=
      ⟨_root_.dist_nonneg,
        by linarith [mem_interval_iff.mp hz, _root_.dist_nonneg (x := z) (y := b)]⟩
    exact ⟨⟨Dist.dist a z, hmem⟩, (hγ'.eq_on hT hγ hmem).symm.trans hgz⟩

end TreeGeodesic

/-! ### Tree medians and branch partitions -/

section TreeMedian

private lemma exists_edge_dart_of_ne {a b : MetricGraph W} (hab : a ≠ b) :
    Nonempty W.graph.Dart := by
  induction a using ind with
  | vertex u =>
    induction b using ind with
    | vertex v =>
      have huv : u ≠ v := fun h => hab (h ▸ rfl)
      obtain ⟨p⟩ := W.connected u v
      exact ⟨p.firstDart (Walk.not_nil_of_ne huv)⟩
    | edgePoint d _ _ _ => exact ⟨d⟩
  | edgePoint d _ _ _ => exact ⟨d⟩

/-- Every point at distance `r` strictly less than all edge weights from `vertex v` lies on
a dart starting at `v` at parameter `r / W.weight d.edge`. -/
theorem dist_vertex_mem_step_dart [Finite V] {v : V} {p : MetricGraph W} {r : ℝ}
    (hpos : 0 < r) (hr : Dist.dist (vertex v : MetricGraph W) p = r)
    (hmin : ∀ d : W.graph.Dart, r < W.weight d.edge) :
    ∃ (d : W.graph.Dart) (t : unitInterval),
      d.fst = v ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ p = edgePoint d t ∧
      (t : ℝ) * W.weight d.edge = r := by
  have hvd_ge : ∀ {u w : V}, u ≠ w → r < vertexDist W.graph W.weight u w := by
    intro u w huw
    obtain ⟨q, -, hq⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u w)
    cases q with
    | nil => exact absurd rfl huw
    | cons hadj q' =>
      have h1 := hmin ⟨(_, _), hadj⟩
      have h2 := walkLength_nonneg W.weight W.weight_nonneg q'
      rw [← hq, walkLength_cons]
      exact h1.trans_le (le_add_of_nonneg_right h2)
  induction p using ind with
  | vertex u =>
    by_cases huv : v = u
    · subst huv
      simp only [_root_.dist_self] at hr
      linarith
    · have := hvd_ge huv
      rw [dist_vertex] at hr
      linarith
  | edgePoint d t ht0 ht1 =>
    rw [dist_vertex_edgePoint] at hr
    by_cases hfst : d.fst = v
    · have hright : r < vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge := by
        have h1 := hvd_ge (hfst ▸ d.fst_ne_snd)
        have h2 : 0 ≤ (1 - (t : ℝ)) * W.weight d.edge :=
          mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d)
        linarith
      have hmin_eq : min (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
          (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) =
          vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge := by
        rcases min_choice (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
            (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) with
          hm | hm <;> linarith
      rw [hmin_eq, hfst, vertexDist_self W.weight_nonneg, zero_add] at hr
      exact ⟨d, t, hfst, ht0, ht1, rfl, hr⟩
    · by_cases hsnd : d.snd = v
      · have hleft : vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge > r := by
          have h1 := hvd_ge (fun h => hfst h.symm)
          have h2 : 0 ≤ (t : ℝ) * W.weight d.edge := mul_nonneg t.2.1 (W.dart_weight_nonneg d)
          linarith
        have hmin_eq : min (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
            (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) =
            vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge := by
          rcases min_choice (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
              (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) with
            hm | hm <;> linarith
        rw [hmin_eq, hsnd, vertexDist_self W.weight_nonneg, zero_add] at hr
        refine ⟨d.symm, unitInterval.symm t, hsnd,
          by simp only [unitInterval.coe_symm_eq]; linarith,
          by simp only [unitInterval.coe_symm_eq]; linarith,
          (edgePoint_symm d t).symm, ?_⟩
        simpa only [unitInterval.coe_symm_eq, Dart.edge_symm] using hr
      · have h1 := hvd_ge (fun h => hfst h.symm)
        have h2 := hvd_ge (fun h => hsnd h.symm)
        have hnn1 : 0 ≤ (t : ℝ) * W.weight d.edge := mul_nonneg t.2.1 (W.dart_weight_nonneg d)
        have hnn2 : 0 ≤ (1 - (t : ℝ)) * W.weight d.edge :=
          mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_nonneg d)
        rcases min_choice (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
            (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) with hm | hm
        · linarith
        · linarith

/-- Every triple of points in a tree metric graph has a point lying on shortest paths between
all three pairs. -/
theorem exists_treeMedian [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    ∃ m : MetricGraph W, m ∈ interval x y ∧ m ∈ interval y z ∧ m ∈ interval z x := by
  let S : Set (MetricGraph W) := interval x y ∩ interval x z
  have hS_closed : IsClosed S := (isClosed_interval x y).inter (isClosed_interval x z)
  have hS_compact : IsCompact S := hS_closed.isCompact
  have hS_ne : S.Nonempty := ⟨x, left_mem_interval x y, left_mem_interval x z⟩
  have hcont : ContinuousOn (fun p => Dist.dist x p) S :=
    (continuous_const.dist continuous_id).continuousOn
  obtain ⟨m, hmS, hm_max⟩ := hS_compact.exists_isMaxOn hS_ne hcont
  obtain ⟨hm_xy, hm_xz⟩ := hmS
  refine ⟨m, hm_xy, ?_, interval_comm x z ▸ hm_xz⟩
  by_cases hmy : m = y
  · rw [hmy]
    exact left_mem_interval y z
  by_cases hmz : m = z
  · rw [hmz]
    exact right_mem_interval y z
  have hdy_pos : 0 < Dist.dist m y := _root_.dist_pos.mpr hmy
  have hdz_pos : 0 < Dist.dist m z := _root_.dist_pos.mpr hmz
  have hstep_advance : ∀ p : MetricGraph W, 0 < Dist.dist m p →
      p ∈ interval m y → p ∈ interval m z → False := by
    intro p hmp hpy hpz
    have hpxy : p ∈ interval x y := by
      have hm' : m ∈ interval y x := interval_comm x y ▸ hm_xy
      have hp' : p ∈ interval y m := interval_comm m y ▸ hpy
      exact interval_comm y x ▸ mem_interval_trans_left hm' hp'
    have hpxz : p ∈ interval x z := by
      have hm' : m ∈ interval z x := interval_comm x z ▸ hm_xz
      have hp' : p ∈ interval z m := interval_comm m z ▸ hpz
      exact interval_comm z x ▸ mem_interval_trans_left hm' hp'
    have hle : Dist.dist x p ≤ Dist.dist x m := hm_max ⟨hpxy, hpxz⟩
    have hdxp : Dist.dist x p = Dist.dist x m + Dist.dist m p := by
      have h1 := mem_interval_iff.mp hpxy
      have h2 := mem_interval_iff.mp hm_xy
      have h3 := mem_interval_iff.mp hpy
      linarith
    linarith
  induction m using ind with
  | vertex v =>
    obtain ⟨d₀⟩ := exists_edge_dart_of_ne hmy
    obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
    let r : ℝ := min wmin (min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z)) / 3
    have hr_pos : 0 < r := by
      dsimp only [r]
      positivity
    have hr_lt_w : ∀ d : W.graph.Dart, r < W.weight d.edge := by
      intro d
      have hd : wmin ≤ W.weight d.edge := hwmin_le d
      have : r ≤ wmin / 3 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    have hr_le_dy : r ≤ Dist.dist (vertex v) y := by
      have : r ≤ min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z) / 3 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [min_le_left (Dist.dist (vertex v) y) (Dist.dist (vertex v) z)]
    have hr_le_dz : r ≤ Dist.dist (vertex v) z := by
      have : r ≤ min (Dist.dist (vertex v) y) (Dist.dist (vertex v) z) / 3 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [min_le_right (Dist.dist (vertex v) y) (Dist.dist (vertex v) z)]
    obtain ⟨py, hpy_mem, hpy_d, _⟩ :=
      exists_mem_interval_dist_eq (vertex v) y ⟨hr_pos.le, hr_le_dy⟩
    obtain ⟨pz, hpz_mem, hpz_d, _⟩ :=
      exists_mem_interval_dist_eq (vertex v) z ⟨hr_pos.le, hr_le_dz⟩
    obtain ⟨dy, ty, hdy_fst, hty0, hty1, rfl, hty_r⟩ :=
      dist_vertex_mem_step_dart hr_pos hpy_d hr_lt_w
    obtain ⟨dz, tz, hdz_fst, htz0, htz1, rfl, htz_r⟩ :=
      dist_vertex_mem_step_dart hr_pos hpz_d hr_lt_w
    by_cases he : dy.edge = dz.edge
    · have hdeq : dy = dz := by
        rcases (dart_edge_eq_iff dy dz).mp he with h | h
        · exact h
        · exfalso
          have hf := hdy_fst.trans hdz_fst.symm
          rw [h, Dart.fst_symm] at hf
          exact dz.snd_ne_fst hf
      subst hdeq
      have hteq : ty = tz :=
        Subtype.ext (mul_right_cancel₀ (W.dart_weight_pos dy).ne' (hty_r.trans htz_r.symm))
      subst hteq
      exact False.elim (hstep_advance (edgePoint dy ty) (by rw [hpy_d]; exact hr_pos)
        hpy_mem hpz_mem)
    · have hdy0 : edgeProj hT dy (vertex v) = 0 := by
        rw [edgeProj_vertex_eq_zero_iff, hdy_fst]
      have hpy_pos : 0 < edgeProj hT dy (edgePoint dy ty) := by
        rw [edgeProj_edgePoint_self]
        exact mul_pos hty0 (W.dart_weight_pos dy)
      have hdy_y : 0 < edgeProj hT dy y := by
        have hle :=
          (mem_interval_edgeProj_bounds hT dy hpy_mem
            (by rw [hdy0]; exact edgeProj_nonneg hT dy y)).2
        exact hpy_pos.trans_le hle
      have hpz0 : edgeProj hT dy (edgePoint dz tz) = 0 := by
        rw [edgeProj_edgePoint_of_edge_ne hT (Ne.symm he), hdz_fst, ← hdy_fst,
          edgeProj_vertex_eq_zero_iff]
      have hdy_z : edgeProj hT dy z = 0 := by
        by_contra hnz
        have hzpos : 0 < edgeProj hT dy z := lt_of_le_of_ne (edgeProj_nonneg hT dy z) (Ne.symm hnz)
        have hv_mem := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT dy hpz0 hzpos)
        have hpz_eq := mem_interval_iff.mp hpz_mem
        rw [hdy_fst, _root_.dist_comm (edgePoint dz tz) (vertex v)] at hv_mem
        linarith
      rw [← hdy_fst]
      exact interval_comm z y ▸ vertex_fst_mem_interval_of_edgeProj hT dy hdy_z hdy_y
  | edgePoint d t ht0 ht1 =>
    have hwpos := W.dart_weight_pos d
    let r : ℝ := min (min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge))
      (min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z)) / 3
    have hr_pos : 0 < r := by
      dsimp only [r]
      have : 0 < (1 - (t : ℝ)) * W.weight d.edge := mul_pos (by linarith) hwpos
      have : 0 < (t : ℝ) * W.weight d.edge := mul_pos ht0 hwpos
      positivity
    have hr_lt1 : r < (t : ℝ) * W.weight d.edge := by
      have : r ≤ min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) / 3 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith [min_le_left ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge),
        mul_pos ht0 hwpos]
    have hr_lt2 : r < (1 - (t : ℝ)) * W.weight d.edge := by
      have : r ≤ min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) / 3 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith [min_le_right ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge),
        mul_pos (sub_pos.mpr ht1) hwpos]
    have hr_le_dy : r ≤ Dist.dist (edgePoint d t) y := by
      have : r ≤ min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z) / 3 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [min_le_left (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z)]
    have hr_le_dz : r ≤ Dist.dist (edgePoint d t) z := by
      have : r ≤ min (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z) / 3 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [min_le_right (Dist.dist (edgePoint d t) y) (Dist.dist (edgePoint d t) z)]
    obtain ⟨py, hpy_mem, hpy_d, _⟩ :=
      exists_mem_interval_dist_eq (edgePoint d t) y ⟨hr_pos.le, hr_le_dy⟩
    obtain ⟨pz, hpz_mem, hpz_d, _⟩ :=
      exists_mem_interval_dist_eq (edgePoint d t) z ⟨hr_pos.le, hr_le_dz⟩
    have step_on_edge : ∀ p : MetricGraph W, Dist.dist (edgePoint d t) p = r →
        ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ p = edgePoint d s ∧
          |((s : ℝ) - t) * W.weight d.edge| = r := by
      intro p hp_d
      have hsub := abs_sub_edgeProj_le_dist hT d (edgePoint d t) p
      rw [edgeProj_edgePoint_self, hp_d] at hsub
      have hlo : 0 < edgeProj hT d p := by linarith [abs_le.mp hsub]
      have hhi : edgeProj hT d p < W.weight d.edge := by linarith [abs_le.mp hsub]
      rcases edgeProj_cases hT d p with h0 | hw | ⟨s, hs0, hs1, rfl⟩
      · linarith
      · linarith
      · have hdist := dist_edgePoint_edgePoint_same_eq hT d t s
        rw [hp_d] at hdist
        refine ⟨s, hs0, hs1, rfl, ?_⟩
        rw [abs_mul, abs_of_nonneg hwpos.le]
        simpa only [abs_sub_comm] using hdist.symm
    obtain ⟨sy, hsy0, hsy1, rfl, hsy_r⟩ := step_on_edge py hpy_d
    obtain ⟨sz, hsz0, hsz1, rfl, hsz_r⟩ := step_on_edge pz hpz_d
    rcases le_or_gt (sy : ℝ) t with hsy_le | hsy_gt
    · have hsy_lt : (sy : ℝ) < t := by
        refine lt_of_le_of_ne hsy_le (fun heq => ?_)
        rw [heq, sub_self, zero_mul, abs_zero] at hsy_r
        linarith
      have hy_proj : edgeProj hT d y ≤ (t : ℝ) * W.weight d.edge := by
        by_contra hlt
        push Not at hlt
        rw [← edgeProj_edgePoint_self hT d t] at hlt
        have hsy_t : edgeProj hT d (edgePoint d sy) < edgeProj hT d (edgePoint d t) := by
          rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self]
          exact mul_lt_mul_of_pos_right hsy_lt hwpos
        exact (dist_add_dist_gt_of_edgeProj_lt hT d hsy_t (hsy_t.trans hlt)).ne
          (mem_interval_iff.mp hpy_mem).symm
      rcases le_or_gt (sz : ℝ) t with hsz_le | hsz_gt
      · have hsz_lt : (sz : ℝ) < t := by
          refine lt_of_le_of_ne hsz_le (fun heq => ?_)
          rw [heq, sub_self, zero_mul, abs_zero] at hsz_r
          linarith
        have heq_abs : |((sy : ℝ) - t) * W.weight d.edge| = |((sz : ℝ) - t) * W.weight d.edge| :=
          hsy_r.trans hsz_r.symm
        rw [abs_of_neg (mul_neg_of_neg_of_pos (sub_neg.mpr hsy_lt) hwpos),
            abs_of_neg (mul_neg_of_neg_of_pos (sub_neg.mpr hsz_lt) hwpos)] at heq_abs
        have hsy_sz : sy = sz := Subtype.ext (by nlinarith)
        subst hsy_sz
        exact False.elim (hstep_advance (edgePoint d sy) (by rw [hpy_d]; exact hr_pos)
          hpy_mem hpz_mem)
      · have hz_proj : (t : ℝ) * W.weight d.edge ≤ edgeProj hT d z := by
          by_contra hlt
          push Not at hlt
          have ht_sym : edgeProj hT d.symm (edgePoint d sz) <
              edgeProj hT d.symm (edgePoint d t) := by
            rw [edgeProj_symm, edgeProj_symm, edgeProj_edgePoint_self, edgeProj_edgePoint_self]
            nlinarith
          have hz_sym : edgeProj hT d.symm (edgePoint d sz) < edgeProj hT d.symm z := by
            rw [edgeProj_symm, edgeProj_symm, edgeProj_edgePoint_self]
            nlinarith
          exact (dist_add_dist_gt_of_edgeProj_lt hT d.symm ht_sym hz_sym).ne
            (mem_interval_iff.mp hpz_mem).symm
        exact edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht1 hy_proj hz_proj
    · have hy_proj : (t : ℝ) * W.weight d.edge ≤ edgeProj hT d y := by
        by_contra hlt
        push Not at hlt
        have ht_sym : edgeProj hT d.symm (edgePoint d sy) <
            edgeProj hT d.symm (edgePoint d t) := by
          rw [edgeProj_symm, edgeProj_symm, edgeProj_edgePoint_self, edgeProj_edgePoint_self]
          nlinarith
        have hy_sym : edgeProj hT d.symm (edgePoint d sy) < edgeProj hT d.symm y := by
          rw [edgeProj_symm, edgeProj_symm, edgeProj_edgePoint_self]
          nlinarith
        exact (dist_add_dist_gt_of_edgeProj_lt hT d.symm ht_sym hy_sym).ne
          (mem_interval_iff.mp hpy_mem).symm
      rcases le_or_gt (sz : ℝ) t with hsz_le | hsz_gt
      · have hsz_lt : (sz : ℝ) < t := by
          refine lt_of_le_of_ne hsz_le (fun heq => ?_)
          rw [heq, sub_self, zero_mul, abs_zero] at hsz_r
          linarith
        have hz_proj : edgeProj hT d z ≤ (t : ℝ) * W.weight d.edge := by
          by_contra hlt
          push Not at hlt
          rw [← edgeProj_edgePoint_self hT d t] at hlt
          have hsz_t : edgeProj hT d (edgePoint d sz) < edgeProj hT d (edgePoint d t) := by
            rw [edgeProj_edgePoint_self, edgeProj_edgePoint_self]
            exact mul_lt_mul_of_pos_right hsz_lt hwpos
          exact (dist_add_dist_gt_of_edgeProj_lt hT d hsz_t (hsz_t.trans hlt)).ne
            (mem_interval_iff.mp hpz_mem).symm
        exact interval_comm z y ▸ edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht1 hz_proj hy_proj
      · have heq_abs : |((sy : ℝ) - t) * W.weight d.edge| = |((sz : ℝ) - t) * W.weight d.edge| :=
          hsy_r.trans hsz_r.symm
        rw [abs_of_pos (mul_pos (sub_pos.mpr hsy_gt) hwpos),
            abs_of_pos (mul_pos (sub_pos.mpr hsz_gt) hwpos)] at heq_abs
        have hsy_sz : sy = sz := Subtype.ext (by nlinarith)
        subst hsy_sz
        exact False.elim (hstep_advance (edgePoint d sy) (by rw [hpy_d]; exact hr_pos)
          hpy_mem hpz_mem)

/-- The unique metric median `treeMedian hT x y z` in a tree metric graph. -/
noncomputable def treeMedian [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    MetricGraph W :=
  (exists_treeMedian hT x y z).choose

theorem treeMedian_mem_xy [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval x y :=
  (exists_treeMedian hT x y z).choose_spec.1

theorem treeMedian_mem_yz [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval y z :=
  (exists_treeMedian hT x y z).choose_spec.2.1

theorem treeMedian_mem_zx [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    treeMedian hT x y z ∈ interval z x :=
  (exists_treeMedian hT x y z).choose_spec.2.2

theorem eq_treeMedian_of_mem [Finite V] (hT : W.graph.IsTree) {x y z m : MetricGraph W}
    (hxy : m ∈ interval x y) (hyz : m ∈ interval y z) (hzx : m ∈ interval z x) :
    m = treeMedian hT x y z := by
  refine eq_of_mem_interval_dist_eq hT hxy (treeMedian_mem_xy hT x y z) ?_
  have e1 := mem_interval_iff.mp hxy
  have e2 := mem_interval_iff.mp hyz
  have e3 := mem_interval_iff.mp hzx
  have m1 := mem_interval_iff.mp (treeMedian_mem_xy hT x y z)
  have m2 := mem_interval_iff.mp (treeMedian_mem_yz hT x y z)
  have m3 := mem_interval_iff.mp (treeMedian_mem_zx hT x y z)
  linarith [_root_.dist_comm z x, _root_.dist_comm z m, _root_.dist_comm m x,
    _root_.dist_comm m y, _root_.dist_comm z (treeMedian hT x y z),
    _root_.dist_comm (treeMedian hT x y z) x, _root_.dist_comm (treeMedian hT x y z) y]

theorem dist_add_dist_eq_treeMedian [Finite V] (hT : W.graph.IsTree) {x y z p : MetricGraph W}
    (hp : p ∈ interval x y) :
    Dist.dist z p = Dist.dist z (treeMedian hT x y z) + Dist.dist (treeMedian hT x y z) p := by
  let m := treeMedian hT x y z
  have hm_xy : m ∈ interval x y := treeMedian_mem_xy hT x y z
  have hm_yz : m ∈ interval y z := treeMedian_mem_yz hT x y z
  have hm_zx : m ∈ interval z x := treeMedian_mem_zx hT x y z
  rcases le_total (Dist.dist x p) (Dist.dist x m) with hle | hle
  · have hp_xm := mem_interval_iff.mp (mem_interval_of_mem_interval_dist_le hT hp hm_xy hle)
    have hm_zx' := mem_interval_iff.mp hm_zx
    linarith [_root_.dist_triangle z p x, _root_.dist_triangle z m p, _root_.dist_comm p x,
      _root_.dist_comm m x, _root_.dist_comm p m]
  · have hp_xy' := mem_interval_iff.mp hp
    have hm_xy' := mem_interval_iff.mp hm_xy
    have hm_xp := mem_interval_iff.mp (mem_interval_of_mem_interval_dist_le hT hm_xy hp hle)
    have hm_yz' := mem_interval_iff.mp hm_yz
    linarith [_root_.dist_triangle y p z, _root_.dist_triangle z m p, _root_.dist_comm y p,
      _root_.dist_comm p z, _root_.dist_comm y m, _root_.dist_comm m z, _root_.dist_comm y z]

/-- The median `treeMedian hT x y z` is the gate of `z` on `interval x y`: it lies between `z`
and every point of that interval. -/
theorem treeMedian_mem_interval_of_mem [Finite V] (hT : W.graph.IsTree) {x y p : MetricGraph W}
    (hp : p ∈ interval x y) (z : MetricGraph W) : treeMedian hT x y z ∈ interval z p :=
  mem_interval_iff.mpr (dist_add_dist_eq_treeMedian hT hp).symm

/-- In a tree metric graph, the interval from `x` to `z` is covered by the intervals from `x` to
`y` and from `y` to `z`. -/
theorem interval_subset_union [Finite V] (hT : W.graph.IsTree) (x y z : MetricGraph W) :
    interval x z ⊆ interval x y ∪ interval y z := by
  intro w hw
  have hm : treeMedian hT x y z ∈ interval x z := interval_comm z x ▸ treeMedian_mem_zx hT x y z
  rcases le_total (Dist.dist x w) (Dist.dist x (treeMedian hT x y z)) with hle | hle
  · exact Or.inl (interval_subset_of_mem hT (left_mem_interval x y) (treeMedian_mem_xy hT x y z)
      (mem_interval_of_mem_interval_dist_le hT hw hm hle))
  · exact Or.inr (interval_subset_of_mem hT (treeMedian_mem_yz hT x y z) (right_mem_interval y z)
      (mem_interval_trans_right hw (mem_interval_of_mem_interval_dist_le hT hm hw hle)))

/-- The branch of a tree metric graph at base point `p` in the direction of `q`:
`{ w | p ∉ interval q w }`. Equal to `∅` when `q = p`. -/
@[expose] def branch [Finite V] (p q : MetricGraph W) : Set (MetricGraph W) :=
  { w | p ∉ interval q w }

@[simp]
theorem notMem_branch_self [Finite V] (p q : MetricGraph W) : p ∉ branch p q := by
  simp [branch]

@[simp]
theorem branch_self [Finite V] (p : MetricGraph W) : branch p p = ∅ := by
  ext w
  simp [branch]

theorem mem_branch_self [Finite V] {p q : MetricGraph W} (hpq : q ≠ p) : q ∈ branch p q := by
  simp only [branch, Set.mem_ofPred_eq, interval_eq_singleton_self, Set.mem_singleton_iff]
  exact hpq.symm

theorem branch_symm [Finite V] {q₁ q₂ w : MetricGraph W} (hq : q₁ ≠ q₂)
    (hw : w ∉ branch q₁ q₂) : w ∈ branch q₂ q₁ := by
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at hw ⊢
  intro hmem
  have e1 := mem_interval_iff.mp hw
  have e2 := mem_interval_iff.mp hmem
  have hd : Dist.dist q₂ q₁ = 0 := by
    linarith [_root_.dist_comm q₁ q₂, _root_.dist_comm q₁ w, _root_.dist_comm q₂ w]
  exact hq ((_root_.dist_eq_zero.mp hd).symm)

theorem branch_eq_of_mem [Finite V] (hT : W.graph.IsTree) {p q₁ q₂ : MetricGraph W}
    (hq : q₂ ∈ branch p q₁) : branch p q₂ = branch p q₁ := by
  have sub_of : ∀ {a b : MetricGraph W}, b ∈ branch p a → branch p b ⊆ branch p a := by
    intro a b hb w hw
    dsimp only [branch] at hb hw ⊢
    intro hwa
    let m₁ := treeMedian hT p a b
    let m₂ := treeMedian hT p b w
    have hm1_ab : m₁ ∈ interval a b := treeMedian_mem_yz hT p a b
    have hm2_bw : m₂ ∈ interval b w := treeMedian_mem_yz hT p b w
    have hm1_ne : m₁ ≠ p := fun heq => hb (heq ▸ hm1_ab)
    have hm2_ne : m₂ ≠ p := fun heq => hw (heq ▸ hm2_bw)
    have h1pos : 0 < Dist.dist p m₁ := _root_.dist_pos.mpr hm1_ne.symm
    have h2pos : 0 < Dist.dist p m₂ := _root_.dist_pos.mpr hm2_ne.symm
    have hm1_pa : m₁ ∈ interval p a := treeMedian_mem_xy hT p a b
    have hm1_pb : m₁ ∈ interval p b := interval_comm b p ▸ treeMedian_mem_zx hT p a b
    have hm2_pb : m₂ ∈ interval p b := treeMedian_mem_xy hT p b w
    have hm2_pw : m₂ ∈ interval p w := interval_comm w p ▸ treeMedian_mem_zx hT p b w
    rcases le_total (Dist.dist p m₁) (Dist.dist p m₂) with hle | hle
    · have hm1_pw : m₁ ∈ interval p w :=
        mem_interval_trans_left hm2_pw (mem_interval_of_mem_interval_dist_le hT hm1_pb hm2_pb hle)
      have e1 := mem_interval_iff.mp hm1_pa
      have e2 := mem_interval_iff.mp hm1_pw
      have e3 := mem_interval_iff.mp hwa
      linarith [_root_.dist_triangle a m₁ w, _root_.dist_comm a m₁, _root_.dist_comm p a,
        _root_.dist_comm p m₁]
    · have hm2_pa : m₂ ∈ interval p a :=
        mem_interval_trans_left hm1_pa (mem_interval_of_mem_interval_dist_le hT hm2_pb hm1_pb hle)
      have e1 := mem_interval_iff.mp hm2_pa
      have e2 := mem_interval_iff.mp hm2_pw
      have e3 := mem_interval_iff.mp hwa
      linarith [_root_.dist_triangle a m₂ w, _root_.dist_comm a m₂, _root_.dist_comm p a,
        _root_.dist_comm p m₂]
  have hq' : q₁ ∈ branch p q₂ := by
    simp only [branch, Set.mem_ofPred_eq, interval_comm] at hq ⊢
    exact hq
  exact Set.Subset.antisymm (sub_of hq) (sub_of hq')

theorem branch_disjoint_of_mem_interval [Finite V] (hT : W.graph.IsTree)
    {p q₁ q₂ : MetricGraph W} (hp : p ∈ interval q₁ q₂) :
    Disjoint (branch p q₁) (branch p q₂) := by
  rw [Set.disjoint_left]
  intro w hw1 hw2
  by_cases h1 : q₁ = p
  · subst h1
    simp only [branch_self, Set.mem_empty_iff_false] at hw1
  · have hq1 : q₁ ∈ branch p q₂ := by
      rw [← branch_eq_of_mem hT hw2, branch_eq_of_mem hT hw1]
      exact mem_branch_self h1
    simp only [branch, Set.mem_ofPred_eq, interval_comm q₂ q₁] at hq1
    exact hq1 hp

/-- Two distinct branches at the same base point of a tree metric graph are disjoint. -/
theorem branch_disjoint_of_ne [Finite V] (hT : W.graph.IsTree) {y p q : MetricGraph W}
    (hpq : branch y p ≠ branch y q) : Disjoint (branch y p) (branch y q) :=
  Set.disjoint_left.mpr fun _ hwp hwq =>
    hpq ((branch_eq_of_mem hT hwp).symm.trans (branch_eq_of_mem hT hwq))

/-- Moving the base point toward `q` shrinks the branch toward `q`. -/
theorem branch_subset_branch_of_mem_interval [Finite V] {y p q : MetricGraph W}
    (hp : p ∈ interval y q) : branch p q ⊆ branch y q := by
  intro w hw
  by_contra hnot
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at hnot hw
  have h1 := mem_interval_iff.mp hp
  have h2 := mem_interval_iff.mp hnot
  have hqpw : Dist.dist q p + Dist.dist p w ≤ Dist.dist q w := by
    have htri := _root_.dist_triangle p y w
    linarith [_root_.dist_comm q p, _root_.dist_comm q y, _root_.dist_comm q w,
      _root_.dist_comm p y, _root_.dist_comm y w]
  exact hw (mem_interval_iff.mpr (le_antisymm hqpw (_root_.dist_triangle q p w)))

/-- Every point other than `y` between `y` and a point of the branch at `y` toward `q` lies in
that branch. -/
theorem mem_branch_of_mem_interval [Finite V] (hT : W.graph.IsTree) {y b q z : MetricGraph W}
    (hb : b ∈ branch y q) (hz : z ∈ interval y b) (hzy : z ≠ y) : z ∈ branch y q := by
  rw [← branch_eq_of_mem hT hb]
  simp only [branch, Set.mem_ofPred_eq]
  intro hmem
  have h1 := mem_interval_iff.mp hz
  have h2 := mem_interval_iff.mp hmem
  have hd : Dist.dist y z = 0 := by
    linarith [_root_.dist_comm b y, _root_.dist_comm b z, _root_.dist_comm y z,
      _root_.dist_comm z b]
  exact hzy (_root_.dist_eq_zero.mp hd).symm

/-- A point `π` between `z` and both `p` and `q` lies in the branch at `p` toward `q` exactly
when `z` does. This is the branch property of gates (`IsConvex.mem_branch_gate_iff`) and of
medians. -/
theorem mem_branch_iff_of_mem_interval [Finite V] {p q z π : MetricGraph W}
    (hp : π ∈ interval z p) (hq : π ∈ interval z q) : z ∈ branch p q ↔ π ∈ branch p q := by
  have hzp := mem_interval_iff.mp hp
  have hzq := mem_interval_iff.mp hq
  simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
  constructor <;> intro h heq <;> apply h <;>
    linarith [_root_.dist_comm z p, _root_.dist_comm z q, _root_.dist_comm p π,
      _root_.dist_comm q π]

/-- The branch at a vertex `c` toward an adjacent vertex `w` is the set where the projection
along the dart `(c, w)` is positive. -/
theorem mem_branch_vertex_iff_edgeProj_pos [Finite V] (hT : W.graph.IsTree) {c w : V}
    (hadj : W.graph.Adj c w) (z : MetricGraph W) :
    z ∈ branch (vertex c) (vertex w) ↔ 0 < edgeProj hT ⟨(c, w), hadj⟩ z := by
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  change z ∈ branch (vertex d.fst) (vertex d.snd) ↔ 0 < edgeProj hT d z
  have hw_pos := W.dart_weight_pos d
  have hc0 : edgeProj hT d (vertex d.fst) = 0 :=
    (edgeProj_vertex_eq_zero_iff hT d d.fst).mpr (.refl _)
  have hw_proj : edgeProj hT d (vertex d.snd) = W.weight d.edge := by
    rw [edgeProj_vertex_eq_weight_iff]
    exact fun hr => bridge_deleteEdges hT d hr.symm
  constructor
  · intro hz
    by_contra hle
    have h0 : edgeProj hT d z = 0 := le_antisymm (not_lt.mp hle) (edgeProj_nonneg hT d z)
    have hmem := vertex_fst_mem_interval_of_edgeProj hT d h0 (by rw [hw_proj]; exact hw_pos)
    exact hz (interval_comm z (vertex d.snd) ▸ hmem)
  · intro hpos
    simp only [branch, Set.mem_ofPred_eq]
    intro hmem
    have hmem' := mem_interval_iff.mp hmem
    have hdist_pos : 0 < Dist.dist (vertex d.fst : MetricGraph W) z := by
      refine _root_.dist_pos.mpr fun heq => ?_
      rw [← heq, hc0] at hpos
      exact lt_irrefl 0 hpos
    have hsym_lt : edgeProj hT d.symm z < W.weight d.edge := by
      rw [edgeProj_symm]
      linarith
    rcases lt_or_ge (edgeProj hT d z) (W.weight d.edge) with hlt | hge
    · obtain ⟨t, ht0, ht1, rfl⟩ : ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
          z = edgePoint d t := by
        rcases edgeProj_cases hT d z with h0 | hw | ⟨t, ht0, ht1, hzeq⟩
        · linarith
        · linarith
        · exact ⟨t, ht0, ht1, hzeq⟩
      have h1 := dist_edgePoint_edgePoint_same_eq hT d 0 t
      have h2 := dist_edgePoint_edgePoint_same_eq hT d t 1
      have h3 := dist_edgePoint_edgePoint_same_eq hT d 0 1
      simp only [edgePoint_zero, edgePoint_one, Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub,
        abs_neg, abs_one, one_mul] at h1 h2 h3
      rw [abs_of_nonneg ht0.le] at h1
      rw [abs_of_neg (sub_neg.mpr ht1)] at h2
      linarith [_root_.dist_comm (vertex d.snd : MetricGraph W) (vertex d.fst),
        _root_.dist_comm (vertex d.snd : MetricGraph W) (edgePoint d t)]
    · have hw_eq : edgeProj hT d z = W.weight d.edge :=
        le_antisymm (edgeProj_le_weight hT d z) hge
      have h0 : edgeProj hT d.symm z = 0 := by rw [edgeProj_symm, hw_eq, sub_self]
      have hpos' : 0 < edgeProj hT d.symm (vertex d.fst) := by
        rw [edgeProj_symm, hc0, sub_zero]
        exact hw_pos
      have hm := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d.symm h0 hpos')
      rw [Dart.fst_symm d] at hm
      have hcd_pos : 0 < Dist.dist (vertex d.snd : MetricGraph W) (vertex d.fst) :=
        _root_.dist_pos.mpr fun h => d.fst_ne_snd (vertex_injective (W := W) h.symm)
      linarith [_root_.dist_comm (vertex d.snd : MetricGraph W) (vertex d.fst),
        _root_.dist_comm (vertex d.snd : MetricGraph W) z,
        _root_.dist_comm z (vertex d.fst)]

/-- At a vertex of a tree metric graph, the branches toward distinct neighbours are disjoint. -/
theorem disjoint_branch_vertex_of_adj [Finite V] (hT : W.graph.IsTree) {c w₁ w₂ : V}
    (hadj₁ : W.graph.Adj c w₁) (hadj₂ : W.graph.Adj c w₂) (hne : w₁ ≠ w₂) :
    Disjoint (branch (vertex c : MetricGraph W) (vertex w₁))
      (branch (vertex c : MetricGraph W) (vertex w₂)) := by
  refine branch_disjoint_of_ne hT fun heq => ?_
  have hw₁ : (vertex w₁ : MetricGraph W) ∈ branch (vertex c) (vertex w₂) :=
    heq ▸ mem_branch_self fun h => hadj₁.ne (vertex_injective (W := W) h.symm)
  rw [mem_branch_vertex_iff_edgeProj_pos hT hadj₂, ← not_le] at hw₁
  refine hw₁ (le_of_eq ((edgeProj_vertex_eq_zero_iff hT _ w₁).mpr ?_))
  refine SimpleGraph.Adj.reachable ⟨hadj₁.symm, fun h => ?_⟩
  rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h.1) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hadj₁.ne h1.symm
  · exact hne h1

/-- Every nonzero direction `q ≠ y` in a finite tree metric graph begins along a positive-length
unbranched segment `interval y v₀ ⊆ branch y q ∪ {y}` inside which small balls stay in the
segment. -/
theorem exists_stem_segment [Finite V] (hT : W.graph.IsTree) {y q : MetricGraph W} (hq : q ≠ y) :
    ∃ v₀ ∈ branch y q, 0 < Dist.dist y v₀ ∧
      (∀ p ∈ interval y v₀, p ≠ y → p ∈ branch y q) ∧
      (∀ w ∈ branch y q, ∀ p ∈ interval y v₀, Dist.dist y p ≤ Dist.dist y w → p ∈ interval y w) ∧
      (∃ r₀ > 0, r₀ ≤ Dist.dist y v₀ ∧
        ∀ p ∈ interval y v₀, 0 < Dist.dist y p → Dist.dist y p ≤ r₀ →
          ∀ z : MetricGraph W, Dist.dist p z ≤ Dist.dist y p →
            z ∈ interval y v₀ ∧ Dist.dist y z ≤ 2 * Dist.dist y p) := by
  have hstem_dart : ∀ (d : W.graph.Dart) (t₀ : unitInterval) (ht₀1 : (t₀ : ℝ) < 1)
      (hyeq : y = edgePoint d t₀) (hq_gt : (t₀ : ℝ) * W.weight d.edge < edgeProj hT d q)
      (r₀ : ℝ) (hr₀_pos : 0 < r₀) (hr₀_le : r₀ ≤ (1 - (t₀ : ℝ)) * W.weight d.edge / 3)
      (hr₀_zero : t₀ = 0 ∨ r₀ ≤ (t₀ : ℝ) * W.weight d.edge / 3),
      ∃ v₀ ∈ branch y q, 0 < Dist.dist y v₀ ∧
        (∀ p ∈ interval y v₀, p ≠ y → p ∈ branch y q) ∧
        (∀ w ∈ branch y q, ∀ p ∈ interval y v₀, Dist.dist y p ≤ Dist.dist y w → p ∈ interval y w) ∧
        (∃ r₀ > 0, r₀ ≤ Dist.dist y v₀ ∧
          ∀ p ∈ interval y v₀, 0 < Dist.dist y p → Dist.dist y p ≤ r₀ →
            ∀ z : MetricGraph W, Dist.dist p z ≤ Dist.dist y p →
              z ∈ interval y v₀ ∧ Dist.dist y z ≤ 2 * Dist.dist y p) := by
    intro d t₀ ht₀1 hyeq hq_gt r₀ hr₀_pos hr₀_le hr₀_zero
    subst hyeq
    have hwpos := W.dart_weight_pos d
    have hy_proj : edgeProj hT d (edgePoint d t₀) = (t₀ : ℝ) * W.weight d.edge :=
      edgeProj_edgePoint_self hT d t₀
    have hv₀_proj : edgeProj hT d (vertex d.snd) = W.weight d.edge := by
      rw [edgeProj_vertex_eq_weight_iff]
      exact fun hr => bridge_deleteEdges hT d hr.symm
    have hdv_pos : 0 < Dist.dist (edgePoint d t₀) (vertex d.snd) := by
      have := dist_edgePoint_edgePoint_same_eq hT d t₀ 1
      rw [edgePoint_one, Set.Icc.coe_one, abs_of_neg (sub_neg.mpr ht₀1)] at this
      rw [this]
      nlinarith
    have hdv_eq : Dist.dist (edgePoint d t₀) (vertex d.snd) =
        (1 - (t₀ : ℝ)) * W.weight d.edge := by
      have := dist_edgePoint_edgePoint_same_eq hT d t₀ 1
      rw [edgePoint_one, Set.Icc.coe_one, abs_of_neg (sub_neg.mpr ht₀1)] at this
      linarith
    have hv₀_mem : (vertex d.snd : MetricGraph W) ∈ branch (edgePoint d t₀) q := by
      simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
      intro hmem
      have hlt1 : edgeProj hT d (edgePoint d t₀) < edgeProj hT d q := by linarith
      have hlt2 : edgeProj hT d (edgePoint d t₀) < edgeProj hT d (vertex d.snd) := by
        rw [hy_proj, hv₀_proj]
        nlinarith
      exact (dist_add_dist_gt_of_edgeProj_lt hT d hlt1 hlt2).ne hmem.symm
    refine ⟨vertex d.snd, hv₀_mem, hdv_pos, ?_, ?_, ?_⟩
    · intro p hp hpne
      have hp_ge : (t₀ : ℝ) * W.weight d.edge ≤ edgeProj hT d p :=
        hy_proj ▸ (mem_interval_edgeProj_bounds hT d hp (by linarith)).1
      have hp_gt : (t₀ : ℝ) * W.weight d.edge < edgeProj hT d p := by
        refine lt_of_le_of_ne hp_ge (fun heq => ?_)
        rcases edgeProj_cases hT d p with h0 | hw | ⟨sp, _, _, rfl⟩
        · have : (t₀ : ℝ) * W.weight d.edge = 0 := heq.trans h0
          have ht0 : t₀ = 0 := Subtype.ext ((mul_eq_zero.mp this).resolve_right hwpos.ne')
          subst ht0
          rw [edgePoint_zero] at hp hpne
          have hm := vertex_fst_mem_interval_of_edgeProj hT d h0
            (by rw [hv₀_proj]; exact hwpos)
          have hmem1 := mem_interval_iff.mp hp
          have hmem2 := mem_interval_iff.mp hm
          have hd0 : Dist.dist (vertex d.fst : MetricGraph W) p = 0 := by
            linarith [_root_.dist_comm p (vertex d.fst)]
          exact hpne (_root_.dist_eq_zero.mp hd0).symm
        · have : (t₀ : ℝ) * W.weight d.edge = W.weight d.edge := heq.trans hw
          have : (t₀ : ℝ) = 1 :=
            mul_right_cancel₀ hwpos.ne' (by simpa only [one_mul] using this)
          linarith
        · rw [edgeProj_edgePoint_self] at heq
          have : t₀ = sp := Subtype.ext (mul_right_cancel₀ hwpos.ne' heq)
          exact hpne (this ▸ rfl)
      simp only [branch, Set.mem_ofPred_eq, mem_interval_iff]
      exact fun h =>
        (dist_add_dist_gt_of_edgeProj_lt hT d (hy_proj ▸ hq_gt) (hy_proj ▸ hp_gt)).ne h.symm
    · intro w hw p hp hp_le
      have hw_v0 : w ∈ branch (edgePoint d t₀) (vertex d.snd) := by
        rwa [branch_eq_of_mem hT hv₀_mem]
      have hw_gt : (t₀ : ℝ) * W.weight d.edge < edgeProj hT d w := by
        by_contra hle
        push Not at hle
        rcases lt_or_eq_of_le t₀.2.1 with ht0 | ht0
        · have := edgePoint_mem_interval_of_edgeProj_le hT d ht0 ht₀1 hle
            (by rw [hv₀_proj]; exact mul_le_of_le_one_left hwpos.le t₀.2.2)
          exact hw_v0 (interval_comm w (vertex d.snd) ▸ this)
        · have ht0' : t₀ = 0 := Subtype.ext ht0.symm
          subst ht0'
          rw [edgePoint_zero] at hw_v0
          have hw0 : edgeProj hT d w = 0 :=
            le_antisymm (by simpa only [Set.Icc.coe_zero, zero_mul] using hle)
              (edgeProj_nonneg hT d w)
          have := vertex_fst_mem_interval_of_edgeProj hT d hw0 (by rw [hv₀_proj]; exact hwpos)
          exact hw_v0 (interval_comm w (vertex d.snd) ▸ this)
      have hv0_w : (vertex d.snd : MetricGraph W) ∈ interval (edgePoint d t₀) w ∨
          w ∈ interval (edgePoint d t₀) (vertex d.snd) := by
        rcases eq_or_lt_of_le (edgeProj_le_weight hT d w) with hww | hww
        · left
          have hsym_w : edgeProj hT d.symm w = 0 := by rw [edgeProj_symm, hww, sub_self]
          have hsym_y : 0 < edgeProj hT d.symm (edgePoint d t₀) := by
            rw [edgeProj_symm, hy_proj]
            nlinarith
          have hm := vertex_fst_mem_interval_of_edgeProj hT d.symm hsym_w hsym_y
          rw [Dart.fst_symm] at hm
          exact interval_comm w (edgePoint d t₀) ▸ hm
        · right
          rcases edgeProj_cases hT d w with hw0 | hw_eq | ⟨sw, _, _, rfl⟩
          · linarith [mul_nonneg t₀.2.1 hwpos.le]
          · linarith
          · rw [edgeProj_edgePoint_self] at hw_gt
            have htw : (t₀ : ℝ) ≤ sw := ((mul_lt_mul_iff_left₀ hwpos).mp hw_gt).le
            have h1 := dist_edgePoint_edgePoint_same_eq hT d t₀ sw
            have h2 := dist_edgePoint_edgePoint_same_eq hT d sw 1
            have h3 := dist_edgePoint_edgePoint_same_eq hT d t₀ 1
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htw)] at h1
            rw [abs_sub_comm, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr sw.2.2)] at h2
            rw [abs_sub_comm, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr ht₀1.le)] at h3
            rw [edgePoint_one] at h2 h3
            rw [mem_interval_iff]
            linarith
      rcases hv0_w with hv0_w | hw_v0_mem
      · exact mem_interval_trans_left hv0_w hp
      · exact mem_interval_of_mem_interval_dist_le hT hp hw_v0_mem hp_le
    · refine ⟨r₀, hr₀_pos, by linarith, fun p hp hdp_pos hdp_le z hz => ?_⟩
      have hdz_le : Dist.dist (edgePoint d t₀) z ≤ 2 * Dist.dist (edgePoint d t₀) p :=
        (_root_.dist_triangle _ p z).trans (by linarith)
      have hp_ge : (t₀ : ℝ) * W.weight d.edge ≤ edgeProj hT d p :=
        hy_proj ▸ (mem_interval_edgeProj_bounds hT d hp (by linarith)).1
      have hp_le : edgeProj hT d p ≤ (t₀ : ℝ) * W.weight d.edge + Dist.dist (edgePoint d t₀) p := by
        have := abs_sub_edgeProj_le_dist hT d p (edgePoint d t₀)
        rw [hy_proj, _root_.dist_comm] at this
        linarith [(le_abs_self _).trans this]
      have hp_lt_w : edgeProj hT d p < W.weight d.edge := by linarith
      have hp_gt0 : (t₀ : ℝ) * W.weight d.edge < edgeProj hT d p := by
        refine lt_of_le_of_ne hp_ge (fun heq => ?_)
        rcases edgeProj_cases hT d p with h0 | hw | ⟨sp, _, _, rfl⟩
        · have : (t₀ : ℝ) * W.weight d.edge = 0 := heq.trans h0
          have ht0 : t₀ = 0 := Subtype.ext ((mul_eq_zero.mp this).resolve_right hwpos.ne')
          subst ht0
          rw [edgePoint_zero] at hp hdp_pos
          have hm := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d h0
            (by rw [hv₀_proj]; exact hwpos))
          have hmem1 := mem_interval_iff.mp hp
          have : Dist.dist (vertex d.fst : MetricGraph W) p = 0 := by
            linarith [_root_.dist_comm p (vertex d.fst)]
          linarith
        · linarith
        · rw [edgeProj_edgePoint_self] at heq
          have : t₀ = sp := Subtype.ext (mul_right_cancel₀ hwpos.ne' heq)
          rw [this, _root_.dist_self] at hdp_pos
          exact lt_irrefl _ hdp_pos
      obtain ⟨sp, hs0, _, rfl, hp_sp⟩ : ∃ sp : unitInterval, 0 < (sp : ℝ) ∧ (sp : ℝ) < 1 ∧
          p = edgePoint d sp ∧ edgeProj hT d p = (sp : ℝ) * W.weight d.edge := by
        rcases edgeProj_cases hT d p with h0 | hw | ⟨sp, hs0, hs1, rfl⟩
        · linarith [mul_nonneg t₀.2.1 hwpos.le]
        · linarith
        · exact ⟨sp, hs0, hs1, rfl, edgeProj_edgePoint_self hT d sp⟩
      have hsp_ge : (t₀ : ℝ) ≤ sp := by
        rw [hp_sp] at hp_gt0
        exact ((mul_lt_mul_iff_left₀ hwpos).mp hp_gt0).le
      have hp_dist_eq : Dist.dist (edgePoint d t₀) (edgePoint d sp) =
          ((sp : ℝ) - t₀) * W.weight d.edge := by
        rw [dist_edgePoint_edgePoint_same_eq hT d t₀ sp, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr hsp_ge)]
      have hzp_proj := abs_sub_edgeProj_le_dist hT d (edgePoint d sp) z
      rw [hp_sp] at hzp_proj
      have hz_proj_le : edgeProj hT d z ≤
          (t₀ : ℝ) * W.weight d.edge + 2 * Dist.dist (edgePoint d t₀) (edgePoint d sp) := by
        linarith [(neg_le_abs _).trans hzp_proj]
      have hz_lt_w : edgeProj hT d z < W.weight d.edge := by linarith
      rcases edgeProj_cases hT d z with hz0 | hzw | ⟨sz, _, hsz1, rfl⟩
      · rcases hr₀_zero with rfl | hr0_t
        · have hz_fst : z = vertex d.fst := by
            have hm := mem_interval_iff.mp (vertex_fst_mem_interval_of_edgeProj hT d hz0
              (by rw [hp_sp]; exact mul_pos hs0 hwpos))
            rw [edgePoint_zero] at hz hdp_pos
            have : Dist.dist z (vertex d.fst) = 0 := by
              linarith [_root_.dist_comm (edgePoint d sp) z,
                _root_.dist_nonneg (x := z) (y := vertex d.fst)]
            exact _root_.dist_eq_zero.mp this
          rw [edgePoint_zero] at hdz_le
          rw [edgePoint_zero, hz_fst]
          exact ⟨left_mem_interval _ _, by simpa only [hz_fst] using hdz_le⟩
        · exfalso
          have hdiff : ((sp : ℝ) - t₀) * W.weight d.edge =
              Dist.dist (edgePoint d t₀) (edgePoint d sp) := hp_dist_eq.symm
          linarith [(le_abs_self _).trans hzp_proj]
      · linarith
      · have hz_ge_t₀ : (t₀ : ℝ) ≤ sz := by
          rcases hr₀_zero with rfl | hr0_t
          · exact sz.2.1
          · rw [edgeProj_edgePoint_self] at hzp_proj
            have h1 := (le_abs_self _).trans hzp_proj
            have : (t₀ : ℝ) * W.weight d.edge ≤ (sz : ℝ) * W.weight d.edge := by linarith
            exact (mul_le_mul_iff_left₀ hwpos).mp this
        have h1 := dist_edgePoint_edgePoint_same_eq hT d t₀ sz
        have h2 := dist_edgePoint_edgePoint_same_eq hT d sz 1
        have h3 := dist_edgePoint_edgePoint_same_eq hT d t₀ 1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hz_ge_t₀)] at h1
        rw [abs_sub_comm, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr hsz1.le)] at h2
        rw [abs_sub_comm, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr ht₀1.le)] at h3
        rw [edgePoint_one] at h2 h3
        refine ⟨?_, hdz_le⟩
        rw [mem_interval_iff]
        linarith
  induction y using ind with
  | vertex v =>
    obtain ⟨d₀⟩ := exists_edge_dart_of_ne hq.symm
    obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
    let r : ℝ := min wmin (Dist.dist (vertex v) q) / 3
    have hr_pos : 0 < r := by
      dsimp only [r]
      have : 0 < Dist.dist (vertex v) q := _root_.dist_pos.mpr hq.symm
      positivity
    have hr_lt_w : ∀ d : W.graph.Dart, r < W.weight d.edge := fun d => by
      have hd : wmin ≤ W.weight d.edge := hwmin_le d
      have : r ≤ wmin / 3 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    have hr_le_dq : r ≤ Dist.dist (vertex v) q := by
      have : r ≤ Dist.dist (vertex v) q / 3 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith [_root_.dist_nonneg (x := (vertex v : MetricGraph W)) (y := q)]
    obtain ⟨pq, hpq_mem, hpq_d, _⟩ := exists_mem_interval_dist_eq (vertex v) q ⟨hr_pos.le, hr_le_dq⟩
    obtain ⟨d, t, hd_fst, ht0, _, rfl, _⟩ := dist_vertex_mem_step_dart hr_pos hpq_d hr_lt_w
    have hq_gt : (0 : ℝ) * W.weight d.edge < edgeProj hT d q := by
      rw [zero_mul]
      have hv0 : edgeProj hT d (vertex v) = 0 := by
        rw [edgeProj_vertex_eq_zero_iff, hd_fst]
      have hp0 : 0 < edgeProj hT d (edgePoint d t) := by
        rw [edgeProj_edgePoint_self]
        exact mul_pos ht0 (W.dart_weight_pos d)
      have hb :=
        (mem_interval_edgeProj_bounds hT d hpq_mem (by rw [hv0]; exact edgeProj_nonneg hT d q)).2
      exact hp0.trans_le hb
    exact hstem_dart d 0 zero_lt_one (by rw [edgePoint_zero, hd_fst]) hq_gt
      (W.weight d.edge / 3) (div_pos (W.dart_weight_pos d) (by norm_num))
      (by simp) (Or.inl rfl)
  | edgePoint d t ht0 ht1 =>
    have hwpos := W.dart_weight_pos d
    have hq_ne : edgeProj hT d q ≠ (t : ℝ) * W.weight d.edge := by
      intro heq
      rcases edgeProj_cases hT d q with h0 | hw | ⟨sq, _, _, rfl⟩
      · have : (t : ℝ) * W.weight d.edge = 0 := heq.symm.trans h0
        have := (mul_eq_zero.mp this).resolve_right hwpos.ne'
        linarith
      · have : (t : ℝ) * W.weight d.edge = W.weight d.edge := heq.symm.trans hw
        have : (t : ℝ) = 1 :=
          mul_right_cancel₀ hwpos.ne' (by simpa only [one_mul] using this)
        linarith
      · rw [edgeProj_edgePoint_self] at heq
        have : sq = t := Subtype.ext (mul_right_cancel₀ hwpos.ne' heq)
        exact hq (this ▸ rfl)
    rcases lt_or_gt_of_ne hq_ne with hlt | hgt
    · have hq_gt : ((unitInterval.symm t : unitInterval) : ℝ) * W.weight d.symm.edge <
          edgeProj hT d.symm q := by
        rw [unitInterval.coe_symm_eq, Dart.edge_symm, edgeProj_symm]
        nlinarith
      exact hstem_dart d.symm (unitInterval.symm t)
        (by simp only [unitInterval.coe_symm_eq]; linarith)
        (edgePoint_symm d t).symm hq_gt
        (min ((t : ℝ) * W.weight d.edge / 3) ((1 - (t : ℝ)) * W.weight d.edge / 3))
        (by have : 0 < 1 - (t : ℝ) := sub_pos.mpr ht1; positivity)
        (by simp only [unitInterval.coe_symm_eq, Dart.edge_symm]
            have := min_le_left ((t : ℝ) * W.weight d.edge / 3)
              ((1 - (t : ℝ)) * W.weight d.edge / 3)
            linarith)
        (Or.inr (by simp only [unitInterval.coe_symm_eq, Dart.edge_symm]
                    exact min_le_right _ _))
    · exact hstem_dart d t ht1 rfl hgt
        (min ((t : ℝ) * W.weight d.edge / 3) ((1 - (t : ℝ)) * W.weight d.edge / 3))
        (by have : 0 < 1 - (t : ℝ) := sub_pos.mpr ht1; positivity)
        (min_le_right _ _)
        (Or.inr (min_le_left _ _))

end TreeMedian

end MetricGraph

end SimpleGraph
