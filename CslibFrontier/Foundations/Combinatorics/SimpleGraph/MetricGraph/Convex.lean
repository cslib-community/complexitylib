/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Convex.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Tree
import Mathlib.Tactic.Linarith

/-!
# Convex sets and subtrees of tree metric graphs

A set of points of a metric graph is convex when it contains the metric interval between any two
of its points. In a tree metric graph (`W.graph.IsTree`) these are the geodesically convex sets.
This module develops the convexity theory used for facility location on trees: gate projections
onto closed convex sets, the Helly property, and the subtrees spanned by vertex sets.

## Main definitions

* `SimpleGraph.MetricGraph.IsConvex`: `K` contains `interval a b` whenever it contains `a` and `b`.
* `SimpleGraph.MetricGraph.gate`: the gate of `y` in `K`, the point of `K` lying between `y` and
  every point of `K`.
* `SimpleGraph.MetricGraph.subtree`: the subtree spanned by a finite vertex set `S`, the union of
  the intervals between vertices of `S`.
* `SimpleGraph.MetricGraph.IsSubtreeVertexSet`: `S` is nonempty and contains every vertex of every
  path between two of its vertices; in a tree, the vertex sets of subtrees.
* `SimpleGraph.MetricGraph.removeBranch`: the vertices of `S` outside the branch at `c` toward `w`.

## Main results

* `SimpleGraph.MetricGraph.IsConvex.exists_gate`, `SimpleGraph.MetricGraph.IsConvex.gate_mem`,
  `SimpleGraph.MetricGraph.IsConvex.gate_mem_interval`: nonempty closed convex sets of a tree
  metric graph have gates.
* `SimpleGraph.MetricGraph.IsConvex.mem_branch_gate_iff`: a point and its gate lie in the same
  branches based in `K`.
* `SimpleGraph.MetricGraph.helly_theorem`: pairwise intersecting convex sets in a finite family
  have a common point.
* `SimpleGraph.MetricGraph.gate_subtree_mem`, `SimpleGraph.MetricGraph.mem_branch_gate_subtree_iff`:
  the same for the subtree spanned by a nonempty vertex set.
* `SimpleGraph.MetricGraph.isConvex_subtree`, `SimpleGraph.MetricGraph.vertex_mem_subtree_iff`,
  `SimpleGraph.MetricGraph.edgePoint_mem_subtree_iff`: the spanned subtree is convex and contains
  exactly the vertices and edges of `S` when `S` is a subtree vertex set.
* `SimpleGraph.MetricGraph.IsSubtreeVertexSet.exists_subtree_eq_interval`: a subtree with maximum
  degree two is an interval.
* `SimpleGraph.MetricGraph.subtree_removeBranch`,
  `SimpleGraph.MetricGraph.gate_subtree_removeBranch`: removing a branch at a vertex of a subtree
  cuts the subtree along that branch, and gates the branch to that vertex.
-/

public section

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-- `S` is the vertex set of a subtree of `W.graph`: it is nonempty and contains every vertex of
every path between two of its vertices. When `W.graph` is a tree, these are exactly the vertex sets
of its subtrees, and `subtree W S` is the corresponding subtree of `MetricGraph W`. -/
structure IsSubtreeVertexSet (W : WeightedGraph V) (S : Finset V) : Prop where
  /-- The vertex set is nonempty. -/
  nonempty : S.Nonempty
  /-- Every vertex of a path between two vertices of `S` lies in `S`. -/
  mem_of_mem_support : ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → ∀ ⦃p : W.graph.Walk u v⦄, p.IsPath →
    ∀ ⦃w⦄, w ∈ p.support → w ∈ S

theorem isSubtreeVertexSet_univ [Fintype V] [Nonempty V] (W : WeightedGraph V) :
    IsSubtreeVertexSet W (Finset.univ : Finset V) :=
  ⟨Finset.univ_nonempty, fun _ _ _ _ _ _ _ _ => Finset.mem_univ _⟩

variable [Finite V]

/-! ### Convex sets -/

section IsConvex

/-- A set `K` of points of a metric graph is *convex* if it contains the metric interval between
any two of its points. In a tree metric graph, intervals are the geodesic segments. -/
@[expose] def IsConvex (K : Set (MetricGraph W)) : Prop :=
  ∀ ⦃a b⦄, a ∈ K → b ∈ K → interval a b ⊆ K

theorem isConvex_univ : IsConvex (Set.univ : Set (MetricGraph W)) :=
  fun _ _ _ _ => Set.subset_univ _

theorem IsConvex.inter {K L : Set (MetricGraph W)} (hK : IsConvex K) (hL : IsConvex L) :
    IsConvex (K ∩ L) :=
  fun _ _ ha hb => Set.subset_inter (hK ha.1 hb.1) (hL ha.2 hb.2)

theorem isConvex_interval (hT : W.graph.IsTree) (a b : MetricGraph W) :
    IsConvex (interval a b) :=
  fun _ _ hu hv => interval_subset_of_mem hT hu hv

/-- The complement of a branch of a tree metric graph is convex. -/
theorem isConvex_compl_branch (hT : W.graph.IsTree) (y q : MetricGraph W) :
    IsConvex (branch y q)ᶜ := by
  intro a b ha hb z hz hz_mem
  rw [Set.mem_compl_iff, ← branch_eq_of_mem hT hz_mem] at ha hb
  simp only [branch, Set.mem_ofPred_eq, Classical.not_not] at ha hb
  have h1 := mem_interval_iff.mp hz
  have h2 := mem_interval_iff.mp ha
  have h3 := mem_interval_iff.mp hb
  have hd : Dist.dist y z = 0 := by
    linarith [_root_.dist_triangle a y b, _root_.dist_comm a y, _root_.dist_comm a z,
      _root_.dist_comm y z, _root_.dist_comm y a, _root_.dist_comm y b, _root_.dist_comm z b,
      _root_.dist_nonneg (x := y) (y := z)]
  exact notMem_branch_self y q ((_root_.dist_eq_zero.mp hd).symm ▸ hz_mem)

/-- Three pairwise intersecting convex sets of a tree metric graph have a common point: the median
of three points of the pairwise intersections. -/
theorem IsConvex.inter_inter_nonempty (hT : W.graph.IsTree) {K₁ K₂ K₃ : Set (MetricGraph W)}
    (h₁ : IsConvex K₁) (h₂ : IsConvex K₂) (h₃ : IsConvex K₃) (h₁₂ : (K₁ ∩ K₂).Nonempty)
    (h₂₃ : (K₂ ∩ K₃).Nonempty) (h₃₁ : (K₃ ∩ K₁).Nonempty) : (K₁ ∩ K₂ ∩ K₃).Nonempty := by
  obtain ⟨x, hx₁, hx₂⟩ := h₁₂
  obtain ⟨y, hy₂, hy₃⟩ := h₂₃
  obtain ⟨z, hz₃, hz₁⟩ := h₃₁
  exact ⟨treeMedian hT x y z,
    ⟨h₁ hz₁ hx₁ (treeMedian_mem_zx hT x y z), h₂ hx₂ hy₂ (treeMedian_mem_xy hT x y z)⟩,
    h₃ hy₃ hz₃ (treeMedian_mem_yz hT x y z)⟩

/-- **Helly's theorem** for tree metric graphs: if the convex sets of a nonempty finite family
intersect pairwise, they have a common point. -/
theorem helly_theorem (hT : W.graph.IsTree) {ι : Type*} {K : ι → Set (MetricGraph W)}
    {s : Finset ι} (hs : s.Nonempty) (hconv : ∀ i ∈ s, IsConvex (K i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, (K i ∩ K j).Nonempty) : (⋂ i ∈ s, K i).Nonempty := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | @insert i₀ s hi₀ ih =>
    have h₀ : i₀ ∈ insert i₀ s := Finset.mem_insert_self i₀ s
    have hs' : ∀ {i}, i ∈ s → i ∈ insert i₀ s := Finset.mem_insert_of_mem
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · obtain ⟨z, hz, -⟩ := hpair i₀ h₀ i₀ h₀
      exact ⟨z, by simpa using hz⟩
    obtain ⟨z, hz⟩ := ih (K := fun i => K i ∩ K i₀) hsne
      (fun i hi => (hconv i (hs' hi)).inter (hconv i₀ h₀))
      (fun i hi j hj => by
        obtain ⟨z, ⟨hzi, hzj⟩, hz₀⟩ := IsConvex.inter_inter_nonempty hT (hconv i (hs' hi))
          (hconv j (hs' hj)) (hconv i₀ h₀) (hpair i (hs' hi) j (hs' hj))
          (hpair j (hs' hj) i₀ h₀) (hpair i₀ h₀ i (hs' hi))
        exact ⟨z, ⟨hzi, hz₀⟩, hzj, hz₀⟩)
    simp only [Set.mem_iInter] at hz
    obtain ⟨i₁, hi₁⟩ := hsne
    refine ⟨z, Set.mem_iInter₂.mpr fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (hz i₁ hi₁).2
    · exact (hz i hi).1

end IsConvex

/-! ### Gates -/

section Gate

open Classical in
/-- The *gate* of `y` in `K`: the point of `K` that lies on the interval from `y` to every point
of `K`. It is unique when it exists (`gate_eq_of_forall_mem_interval`); in a tree metric graph it
exists whenever `K` is nonempty, closed and convex (`IsConvex.exists_gate`), and it is then the
point of `K` nearest to `y`. Otherwise `gate K y = y`. -/
noncomputable def gate (K : Set (MetricGraph W)) (y : MetricGraph W) : MetricGraph W :=
  if h : ∃ p ∈ K, ∀ z ∈ K, p ∈ interval y z then h.choose else y

/-- A point of `K` lying between `y` and every point of `K` is the gate of `y` in `K`. -/
theorem gate_eq_of_forall_mem_interval {K : Set (MetricGraph W)} {y p : MetricGraph W}
    (hp : p ∈ K) (h : ∀ z ∈ K, p ∈ interval y z) : gate K y = p := by
  have hex : ∃ p ∈ K, ∀ z ∈ K, p ∈ interval y z := ⟨p, hp, h⟩
  unfold gate
  rw [dite_eq_left hex]
  obtain ⟨hq, hqz⟩ := hex.choose_spec
  have e1 := mem_interval_iff.mp (hqz p hp)
  have e2 := mem_interval_iff.mp (h _ hq)
  have hd : Dist.dist hex.choose p = 0 := by
    linarith [_root_.dist_comm p hex.choose]
  exact _root_.dist_eq_zero.mp hd

/-- Points of `K` are their own gates. -/
theorem gate_eq_self {K : Set (MetricGraph W)} {y : MetricGraph W} (hy : y ∈ K) : gate K y = y :=
  gate_eq_of_forall_mem_interval hy fun z _ => left_mem_interval y z

/-- In a tree metric graph, every point has a gate in a nonempty closed convex set: the nearest
point of `K`. -/
theorem IsConvex.exists_gate (hT : W.graph.IsTree) {K : Set (MetricGraph W)} (hK : IsConvex K)
    (hKc : IsClosed K) (hKn : K.Nonempty) (y : MetricGraph W) :
    ∃ p ∈ K, ∀ z ∈ K, p ∈ interval y z := by
  obtain ⟨p, hpK, hp_min⟩ :=
    hKc.isCompact.exists_isMinOn hKn (continuous_const.dist continuous_id).continuousOn
  refine ⟨p, hpK, fun z hz => ?_⟩
  by_contra hnot
  let m := treeMedian hT y p z
  have hmK : m ∈ K := hK hpK hz (treeMedian_mem_yz hT y p z)
  have hmp : m ≠ p := fun heq => hnot (heq ▸ (interval_comm z y ▸ treeMedian_mem_zx hT y p z))
  have hle : Dist.dist y p ≤ Dist.dist y m := hp_min hmK
  have h1 := mem_interval_iff.mp (treeMedian_mem_xy hT y p z)
  have hpos : 0 < Dist.dist m p := _root_.dist_pos.mpr hmp
  linarith

theorem IsConvex.gate_mem (hT : W.graph.IsTree) {K : Set (MetricGraph W)} (hK : IsConvex K)
    (hKc : IsClosed K) (hKn : K.Nonempty) (y : MetricGraph W) : gate K y ∈ K := by
  obtain ⟨p, hp, h⟩ := hK.exists_gate hT hKc hKn y
  exact gate_eq_of_forall_mem_interval hp h ▸ hp

theorem IsConvex.gate_mem_interval (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : IsConvex K) (hKc : IsClosed K) (y : MetricGraph W) {z : MetricGraph W} (hz : z ∈ K) :
    gate K y ∈ interval y z := by
  obtain ⟨p, hp, h⟩ := hK.exists_gate hT hKc ⟨z, hz⟩ y
  exact gate_eq_of_forall_mem_interval hp h ▸ h z hz

/-- A point lies in a branch based in a closed convex set exactly when its gate does. -/
theorem IsConvex.mem_branch_gate_iff (hT : W.graph.IsTree) {K : Set (MetricGraph W)}
    (hK : IsConvex K) (hKc : IsClosed K) {p q : MetricGraph W} (hp : p ∈ K) (hq : q ∈ K)
    (z : MetricGraph W) : z ∈ branch p q ↔ gate K z ∈ branch p q :=
  mem_branch_iff_of_mem_interval (hK.gate_mem_interval hT hKc z hp)
    (hK.gate_mem_interval hT hKc z hq)

end Gate

/-! ### Subtrees spanned by vertex sets -/

section Subtree

/-- The subtree of `MetricGraph W` spanned by a vertex set `S`: the union of the intervals between
vertices of `S`. In a tree it is the smallest convex set containing these vertices
(`isConvex_subtree`). -/
def subtree (W : WeightedGraph V) (S : Finset V) : Set (MetricGraph W) :=
  { z | ∃ u ∈ S, ∃ v ∈ S, z ∈ interval (vertex u) (vertex v) }

theorem mem_subtree {S : Finset V} {z : MetricGraph W} :
    z ∈ subtree W S ↔ ∃ u ∈ S, ∃ v ∈ S, z ∈ interval (vertex u) (vertex v) :=
  Iff.rfl

theorem vertex_mem_subtree (W : WeightedGraph V) {S : Finset V} {u : V} (hu : u ∈ S) :
    (vertex u : MetricGraph W) ∈ subtree W S :=
  ⟨u, hu, u, hu, left_mem_interval _ _⟩

theorem subtree_nonempty {S : Finset V} (hS : S.Nonempty) : (subtree W S).Nonempty :=
  let ⟨u, hu⟩ := hS
  ⟨vertex u, vertex_mem_subtree W hu⟩

theorem isClosed_subtree (W : WeightedGraph V) (S : Finset V) : IsClosed (subtree W S) := by
  have heq : subtree W S = ⋃ u ∈ S, ⋃ v ∈ S, interval (vertex u) (vertex v) := by
    ext z
    simp [subtree]
  rw [heq]
  exact isClosed_biUnion_finset fun u _ => isClosed_biUnion_finset fun v _ =>
    isClosed_interval (vertex u) (vertex v)

theorem isConvex_subtree (hT : W.graph.IsTree) (S : Finset V) : IsConvex (subtree W S) := by
  rintro a b ⟨u₁, hu₁, v₁, hv₁, ha⟩ ⟨u₂, hu₂, v₂, hv₂, hb⟩ z hz
  rcases interval_subset_union hT a (vertex u₁) b hz with hz | hz
  · exact ⟨u₁, hu₁, v₁, hv₁, interval_subset_of_mem hT ha (left_mem_interval _ _) hz⟩
  rcases interval_subset_union hT (vertex u₁) (vertex u₂) b hz with hz | hz
  · exact ⟨u₁, hu₁, u₂, hu₂, hz⟩
  · exact ⟨u₂, hu₂, v₂, hv₂, interval_subset_of_mem hT (left_mem_interval _ _) hb hz⟩

/-- Every point has a gate in the subtree spanned by a nonempty vertex set. -/
theorem gate_subtree_mem (hT : W.graph.IsTree) {S : Finset V} (hS : S.Nonempty)
    (y : MetricGraph W) : gate (subtree W S) y ∈ subtree W S :=
  (isConvex_subtree hT S).gate_mem hT (isClosed_subtree W S) (subtree_nonempty hS) y

theorem gate_subtree_mem_interval (hT : W.graph.IsTree) {S : Finset V} (y : MetricGraph W)
    {z : MetricGraph W} (hz : z ∈ subtree W S) : gate (subtree W S) y ∈ interval y z :=
  (isConvex_subtree hT S).gate_mem_interval hT (isClosed_subtree W S) y hz

theorem mem_branch_gate_subtree_iff (hT : W.graph.IsTree) {S : Finset V} {p q : MetricGraph W}
    (hp : p ∈ subtree W S) (hq : q ∈ subtree W S) (z : MetricGraph W) :
    z ∈ branch p q ↔ gate (subtree W S) z ∈ branch p q :=
  (isConvex_subtree hT S).mem_branch_gate_iff hT (isClosed_subtree W S) hp hq z

theorem subtree_univ [Fintype V] (hT : W.graph.IsTree) :
    subtree W (Finset.univ : Finset V) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  induction z using ind with
  | vertex v => exact vertex_mem_subtree W (Finset.mem_univ v)
  | edgePoint d t _ _ =>
    exact ⟨d.fst, Finset.mem_univ _, d.snd, Finset.mem_univ _, edgePoint_mem_interval_vertex hT d t⟩

omit [Finite V] in
/-- A vertex outside a subtree vertex set is cut off from it by a dart: the projection along
the dart vanishes on `S` and reaches the dart's weight at `v`. -/
private lemma exists_cut_dart_of_notMem (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {v : V} (hv : v ∉ S) :
    ∃ d : W.graph.Dart,
      edgeProj hT d (vertex v) = W.weight d.edge ∧
      ∀ u ∈ S, edgeProj hT d (vertex u) = 0 := by
  obtain ⟨u₀, hu₀⟩ := hS.nonempty
  obtain ⟨q, hq⟩ := (W.connected v u₀).exists_isPath
  have hstep : ∀ {a b : V} (p : W.graph.Walk a b), a ∉ S → b ∈ S →
      ∃ d : W.graph.Dart, d.snd ∉ S ∧ d.fst ∈ S ∧
        (W.graph.deleteEdges {d.edge}).Reachable a d.snd := by
    intro a b p
    induction p with
    | nil => intro ha hb; exact absurd hb ha
    | @cons x y z hadj q' ih =>
      intro hx hz
      by_cases hy : y ∈ S
      · refine ⟨⟨(y, x), hadj.symm⟩, hx, hy, .refl x⟩
      · obtain ⟨d, hd_snd, hd_fst, hreach⟩ := ih hy hz
        refine ⟨d, hd_snd, hd_fst, ?_⟩
        have hne_e : s(x, y) ≠ d.edge := fun he => by
          rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hx hd_fst
          · exact hy hd_fst
        have hne_adj : (W.graph.deleteEdges {d.edge}).Adj x y := by
          rw [deleteEdges_adj]
          exact ⟨hadj, fun h => hne_e (Set.mem_singleton_iff.mp h)⟩
        exact hne_adj.reachable.trans hreach
  obtain ⟨d, hd_snd, hd_fst, hreach⟩ := hstep q hv hu₀
  refine ⟨d, ?_, ?_⟩
  · rw [edgeProj_vertex_eq_weight_iff]
    intro hrev
    exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj))
      (by simpa only [Dart.edge] using hrev.symm.trans hreach)
  · intro u hu
    rw [edgeProj_vertex_eq_zero_iff]
    by_contra hnot
    obtain ⟨p, hp⟩ := (W.connected d.fst u).exists_isPath
    have hsplit : d.snd ∈ p.support := by
      by_contra hsnd
      have hne : ∀ e ∈ p.edges, e ≠ d.edge := fun e he hed => by
        rw [hed] at he
        have hed' : s(d.fst, d.snd) ∈ p.edges := he
        exact hsnd (p.snd_mem_support_of_mem_edges hed')
      have hr : (W.graph.deleteEdges {d.edge}).Reachable d.fst u :=
        ⟨p.toDeleteEdges {d.edge} (fun e he hmem => by
          rw [Set.mem_singleton_iff] at hmem
          exact hne e he hmem)⟩
      exact hnot hr.symm
    exact hd_snd (hS.mem_of_mem_support hd_fst hu hp hsplit)

theorem vertex_mem_subtree_iff (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) (v : V) :
    (vertex v : MetricGraph W) ∈ subtree W S ↔ v ∈ S := by
  refine ⟨fun ⟨u₁, hu₁, u₂, hu₂, hv⟩ => ?_, vertex_mem_subtree W⟩
  by_contra hv_not
  obtain ⟨d, hdv, hdu⟩ := exists_cut_dart_of_notMem hT hS hv_not
  have h0 := edgeProj_eq_zero_of_mem_interval hT (hdu u₁ hu₁) (hdu u₂ hu₂) hv
  linarith [W.dart_weight_pos d]

private lemma fst_mem_of_edgePoint_mem_subtree (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {d : W.graph.Dart} {t : unitInterval}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (h : edgePoint d t ∈ subtree W S) : d.fst ∈ S := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hz⟩ := h
  by_contra hfst
  obtain ⟨d₀, hd₀, hd₀S⟩ := exists_cut_dart_of_notMem hT hS hfst
  have hpos : 0 < edgeProj hT d₀ (edgePoint d t) := by
    by_cases he : d.edge = d₀.edge
    · rcases (dart_edge_eq_iff d d₀).mp he with rfl | hsym
      · rw [edgeProj_edgePoint_self]
        exact mul_pos ht0 (W.dart_weight_pos d)
      · rw [hsym, edgeProj_edgePoint_symm]
        exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d₀)
    · rw [edgeProj_edgePoint_of_edge_ne hT he, hd₀]
      exact W.dart_weight_pos d₀
  exact hpos.ne' (edgeProj_eq_zero_of_mem_interval hT (hd₀S u₁ hu₁) (hd₀S u₂ hu₂) hz)

theorem edgePoint_mem_subtree_iff (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {d : W.graph.Dart} {t : unitInterval}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    edgePoint d t ∈ subtree W S ↔ d.fst ∈ S ∧ d.snd ∈ S := by
  refine ⟨fun h => ⟨fst_mem_of_edgePoint_mem_subtree hT hS ht0 ht1 h, ?_⟩,
    fun ⟨hfst, hsnd⟩ => ⟨d.fst, hfst, d.snd, hsnd, edgePoint_mem_interval_vertex hT d t⟩⟩
  rw [← edgePoint_symm] at h
  exact fst_mem_of_edgePoint_mem_subtree hT hS (by simpa using ht1) (by simpa using ht0) h

/-- A subtree in which every vertex has at most two neighbours is the interval between two of its
vertices. -/
theorem IsSubtreeVertexSet.exists_subtree_eq_interval (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S)
    (hdeg : ∀ v ∈ S, ∀ T : Finset V, (∀ u ∈ T, u ∈ S ∧ W.graph.Adj v u) → T.card ≤ 2) :
    ∃ a ∈ S, ∃ b ∈ S, subtree W S = interval (vertex a) (vertex b) := by
  classical
  let lengths : Finset ℕ :=
    (Finset.range (S.card + 1)).filter fun n =>
      ∃ a ∈ S, ∃ b ∈ S, ∃ p : W.graph.Walk a b, p.IsPath ∧ p.length = n
  have hne_len : lengths.Nonempty := by
    obtain ⟨u₀, hu₀⟩ := hS.nonempty
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
      u₀, hu₀, u₀, hu₀, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
  let L := lengths.max' hne_len
  have hL_mem : L ∈ lengths := Finset.max'_mem lengths hne_len
  obtain ⟨a, ha, b, hb, p, hp, hp_len⟩ := (Finset.mem_filter.mp hL_mem).2
  have hp_in_S : ∀ w ∈ p.support, w ∈ S := fun w hw => hS.mem_of_mem_support ha hb hp hw
  -- A longest path cannot be extended at its start by a vertex of `S`.
  have hext : ∀ {a' b' : V} (q : W.graph.Walk a' b'), q.IsPath → q.length = L → b' ∈ S →
      ∀ {u'}, u' ∈ S → u' ∉ q.support → ¬ W.graph.Adj u' a' := by
    intro a' b' q hq hqL hb' u' hu'S hu'q hadj
    have hq' : (Walk.cons hadj q).IsPath := Walk.IsPath.cons hq hu'q
    have hbd : (Walk.cons hadj q).length + 1 ≤ S.card := by
      have hsub : (Walk.cons hadj q).support.toFinset ⊆ S := fun w hw =>
        hS.mem_of_mem_support hu'S hb' hq' (List.mem_toFinset.mp hw)
      have hc := Finset.card_le_card hsub
      rwa [List.toFinset_card_of_nodup hq'.support_nodup, Walk.length_support] at hc
    have hlen' : (Walk.cons hadj q).length = L + 1 := by simp [hqL]
    have hL1_mem : L + 1 ∈ lengths := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), u', hu'S, b', hb', _, hq', hlen'⟩
    have hle := Finset.le_max' lengths (L + 1) hL1_mem
    omega
  have hall_mem : ∀ u ∈ S, u ∈ p.support := by
    intro u hu
    obtain ⟨q, hq⟩ := (W.connected u a).exists_isPath
    have hstep : ∀ {x y : V} (r : W.graph.Walk x y), r.IsPath → x ∈ S → y ∈ p.support →
        x ∉ p.support → ∃ u' ∈ S, ∃ v' ∈ p.support, u' ∉ p.support ∧ W.graph.Adj u' v' := by
      intro x y r
      induction r with
      | nil => intro _ _ hy hx; exact absurd hy hx
      | @cons x₁ z₁ w₁ hadj r' ih =>
        intro hr hx₁ hw₁ hnx₁
        have hz₁_S : z₁ ∈ S :=
          hS.mem_of_mem_support hx₁ (hp_in_S w₁ hw₁) hr (by simp)
        by_cases hz₁ : z₁ ∈ p.support
        · exact ⟨x₁, hx₁, z₁, hz₁, hnx₁, hadj⟩
        · exact ih hr.of_cons hz₁_S hw₁ hz₁
    by_contra hu_not
    obtain ⟨u', hu'S, v', hv'p, hu'not, hadj⟩ :=
      hstep q hq hu (Walk.start_mem_support p) hu_not
    by_cases hva : v' = a
    · subst hva
      exact hext p hp hp_len hb hu'S hu'not hadj
    by_cases hvb : v' = b
    · subst hvb
      exact hext p.reverse hp.reverse (by simp [hp_len]) ha hu'S
        (by simpa [Walk.support_reverse] using hu'not) hadj
    have hv'_S : v' ∈ S := hp_in_S v' hv'p
    let p₁ := p.takeUntil v' hv'p
    let p₂ := p.dropUntil v' hv'p
    have hp1_rev_ne : ¬ p₁.reverse.Nil := Walk.not_nil_of_ne hva
    have hp2_ne : ¬ p₂.Nil := Walk.not_nil_of_ne hvb
    let d₁ := p₁.reverse.firstDart hp1_rev_ne
    let d₂ := p₂.firstDart hp2_ne
    have hp_spec : p₁.append p₂ = p := Walk.take_spec p hv'p
    have hd₁ : d₁ ∈ p₁.reverse.darts := Walk.firstDart_mem_darts hp1_rev_ne
    have hd₂ : d₂ ∈ p₂.darts := Walk.firstDart_mem_darts hp2_ne
    have h1_mem : d₁.snd ∈ p.support := by
      have hd1_supp := p₁.reverse.dart_snd_mem_support_of_mem_darts hd₁
      rw [Walk.support_reverse, List.mem_reverse] at hd1_supp
      rw [← hp_spec]
      exact Walk.support_subset_support_append_left _ _ hd1_supp
    have h2_mem : d₂.snd ∈ p.support := by
      rw [← hp_spec]
      exact Walk.support_subset_support_append_right _ _
        (p₂.dart_snd_mem_support_of_mem_darts hd₂)
    have h1_ne_u : d₁.snd ≠ u' := fun heq => hu'not (heq ▸ h1_mem)
    have h2_ne_u : d₂.snd ≠ u' := fun heq => hu'not (heq ▸ h2_mem)
    have h1_ne_2 : d₁.snd ≠ d₂.snd := by
      intro heq
      have he1 : d₁.edge ∈ p₁.edges := by
        simpa [Walk.edges_reverse] using Walk.edge_mem_edges_of_mem_darts hd₁
      have he2 : d₂.edge ∈ p₂.edges := Walk.edge_mem_edges_of_mem_darts hd₂
      have he_eq : d₁.edge = d₂.edge := by
        change s(d₁.fst, d₁.snd) = s(d₂.fst, d₂.snd)
        rw [show d₁.fst = v' from rfl, show d₂.fst = v' from rfl, heq]
      have hnodup : p.edges.Nodup := hp.isTrail.edges_nodup
      rw [← Walk.take_spec p hv'p, Walk.edges_append, List.nodup_append] at hnodup
      exact hnodup.2.2 d₁.edge he1 d₂.edge he2 he_eq
    have hcard3 : ({u', d₁.snd, d₂.snd} : Finset V).card ≤ 2 := by
      refine hdeg v' hv'_S {u', d₁.snd, d₂.snd} fun x hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨hu'S, hadj.symm⟩
      · exact ⟨hp_in_S _ h1_mem, d₁.adj⟩
      · exact ⟨hp_in_S _ h2_mem, d₂.adj⟩
    have hc3 : ({u', d₁.snd, d₂.snd} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · exact fun h => h1_ne_2 (Finset.mem_singleton.mp h)
      · simp [h1_ne_u.symm, h2_ne_u.symm]
    omega
  refine ⟨a, ha, b, hb, Set.Subset.antisymm ?_ fun z hz => ⟨a, ha, b, hb, hz⟩⟩
  rintro z ⟨u, hu, v, hv, hz⟩
  exact interval_subset_of_mem hT (vertex_mem_interval_of_mem_support hT hp (hall_mem u hu))
    (vertex_mem_interval_of_mem_support hT hp (hall_mem v hv)) hz

/-- Every point of a subtree other than one of its vertices `c` lies in the branch at `c` toward
some neighbour of `c` in the subtree. -/
theorem exists_adj_mem_branch_of_mem_subtree (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {c : V} (hc : c ∈ S) {y : MetricGraph W}
    (hy_S : y ∈ subtree W S) (hy_ne : y ≠ vertex c) :
    ∃ w ∈ S, W.graph.Adj c w ∧ y ∈ branch (vertex c) (vertex w) := by
  classical
  have hne_univ : (Set.univ : Set W.graph.Dart).Nonempty := by
    obtain ⟨u, _, v, _, hy_uv⟩ := hy_S
    by_cases huv : u = v
    · subst huv
      rw [interval_eq_singleton_self] at hy_uv
      have huc : u ≠ c := fun h => hy_ne (hy_uv.trans (h ▸ rfl))
      obtain ⟨p⟩ := W.connected u c
      exact ⟨p.firstDart (Walk.not_nil_of_ne huc), Set.mem_univ _⟩
    · obtain ⟨p⟩ := W.connected u v
      exact ⟨p.firstDart (Walk.not_nil_of_ne huv), Set.mem_univ _⟩
  obtain ⟨d₀⟩ := hne_univ
  obtain ⟨wmin, hwmin_pos, hwmin_le⟩ := exists_min_dart_weight (W := W) d₀
  have hdy : 0 < Dist.dist (vertex c : MetricGraph W) y := _root_.dist_pos.mpr hy_ne.symm
  let r := min wmin (Dist.dist (vertex c : MetricGraph W) y) / 2
  have hr_pos : 0 < r := by positivity
  have hr_lt_w : ∀ d : W.graph.Dart, r < W.weight d.edge := fun d => by
    have hd : wmin ≤ W.weight d.edge := hwmin_le d
    have : r ≤ wmin / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hr_le_dy : r ≤ Dist.dist (vertex c : MetricGraph W) y := by
    have : r ≤ Dist.dist (vertex c : MetricGraph W) y / 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  obtain ⟨p, hp_mem, hp_dist, _⟩ :=
    exists_mem_interval_dist_eq (vertex c) y ⟨hr_pos.le, hr_le_dy⟩
  obtain ⟨d, t, hd_fst, ht0, ht1, rfl, _⟩ :=
    dist_vertex_mem_step_dart hr_pos hp_dist hr_lt_w
  have hp_S : edgePoint d t ∈ subtree W S :=
    isConvex_subtree hT S (vertex_mem_subtree W hc) hy_S hp_mem
  have hd_S := (edgePoint_mem_subtree_iff hT hS ht0 ht1).mp hp_S
  have hadj : W.graph.Adj c d.snd := hd_fst ▸ d.adj
  have hp_br : edgePoint d t ∈ branch (vertex c) (vertex d.snd) := by
    rw [mem_branch_vertex_iff_edgeProj_pos hT hadj]
    have hd_eq : (⟨(c, d.snd), hadj⟩ : W.graph.Dart) = d := by
      ext <;> simp [hd_fst]
    rw [hd_eq, edgeProj_edgePoint_self]
    exact mul_pos ht0 (W.dart_weight_pos d)
  have hp_ne : edgePoint d t ≠ vertex c := fun heq => by
    rw [heq, _root_.dist_self] at hp_dist
    linarith
  have hp_bry : edgePoint d t ∈ branch (vertex c) y :=
    mem_branch_of_mem_interval hT (mem_branch_self hy_ne) hp_mem hp_ne
  refine ⟨d.snd, hd_S.2, hadj, ?_⟩
  rw [← branch_eq_of_mem hT hp_br, branch_eq_of_mem hT hp_bry]
  exact mem_branch_self hy_ne

end Subtree

/-! ### Removing a branch from a subtree -/

section RemoveBranch

open Classical in
/-- The vertices of `S` outside the branch at `c` toward `w`. When `S` is a subtree vertex set,
`c ∈ S` and `w` is adjacent to `c`, this prunes the part of the subtree hanging off `c` through the
edge `cw` (`subtree_removeBranch`). -/
noncomputable def removeBranch (W : WeightedGraph V) (S : Finset V) (c w : V) : Finset V :=
  S.filter fun u => (vertex u : MetricGraph W) ∉ branch (vertex c) (vertex w)

theorem mem_removeBranch {S : Finset V} {c w u : V} :
    u ∈ removeBranch W S c w ↔
      u ∈ S ∧ (vertex u : MetricGraph W) ∉ branch (vertex c) (vertex w) := by
  classical
  exact Finset.mem_filter

theorem removeBranch_subset (W : WeightedGraph V) (S : Finset V) (c w : V) :
    removeBranch W S c w ⊆ S :=
  fun _ hu => (mem_removeBranch.mp hu).1

/-- A vertex survives `removeBranch W S c w` exactly when it reaches `c` without the edge `cw`. -/
theorem mem_removeBranch_iff (hT : W.graph.IsTree) {S : Finset V} {c w u : V}
    (hadj : W.graph.Adj c w) :
    u ∈ removeBranch W S c w ↔
      u ∈ S ∧ (W.graph.deleteEdges {s(c, w)}).Reachable u c := by
  rw [mem_removeBranch, mem_branch_vertex_iff_edgeProj_pos hT hadj, not_lt]
  refine and_congr_right fun _ => Iff.trans ?_ (edgeProj_vertex_eq_zero_iff hT ⟨(c, w), hadj⟩ u)
  exact ⟨fun h => le_antisymm h (edgeProj_nonneg hT _ _), le_of_eq⟩

theorem IsSubtreeVertexSet.removeBranch (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w) :
    IsSubtreeVertexSet W (removeBranch W S c w) := by
  classical
  refine ⟨⟨c, (mem_removeBranch_iff hT hadj).mpr ⟨hc, .refl c⟩⟩, fun u hu v hv p hp x hx => ?_⟩
  rw [mem_removeBranch_iff hT hadj] at hu hv ⊢
  refine ⟨hS.mem_of_mem_support hu.1 hv.1 hp hx, ?_⟩
  obtain ⟨q, hq⟩ := (hu.2.trans hv.2.symm).exists_isPath
  let q' := q.map (SimpleGraph.Hom.ofLE (W.graph.deleteEdges_le {s(c, w)}))
  have hq' : q'.IsPath := hq.map (fun _ _ h => h)
  have hpath : (⟨p, hp⟩ : W.graph.Path u v) = ⟨q', hq'⟩ :=
    (hT.isAcyclic.subsingleton_path u v).elim _ _
  have hpq : p = q' := congrArg Subtype.val hpath
  rw [hpq] at hx
  have hx' : x ∈ q.support := by simpa [q', Walk.support_map] using hx
  have hrx : (W.graph.deleteEdges {s(c, w)}).Reachable x u := ⟨(q.takeUntil x hx').reverse⟩
  exact hrx.trans hu.2

theorem card_removeBranch_lt (hT : W.graph.IsTree) {S : Finset V}
    {c w : V} (hw : w ∈ S) (hadj : W.graph.Adj c w) :
    (removeBranch W S c w).card < S.card := by
  refine Finset.card_lt_card ⟨removeBranch_subset W S c w, fun hsub => ?_⟩
  have hw_rem := (mem_removeBranch_iff hT hadj).mp (hsub hw)
  exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hadj)) hw_rem.2.symm

/-- Removing the branch at `c ∈ S` toward a neighbour `w` cuts that branch out of the subtree. -/
theorem subtree_removeBranch (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w) :
    subtree W (removeBranch W S c w) =
      subtree W S ∩ (branch (vertex c) (vertex w))ᶜ := by
  have hS_rem := hS.removeBranch hT hc hadj
  let d : W.graph.Dart := ⟨(c, w), hadj⟩
  have hbridge : ¬ (W.graph.deleteEdges {d.edge}).Reachable d.snd d.fst := fun hr =>
    (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic d.adj)) hr.symm
  ext z
  simp only [Set.mem_inter_iff, Set.mem_compl_iff]
  induction z using ind with
  | vertex u =>
    rw [vertex_mem_subtree_iff hT hS_rem, vertex_mem_subtree_iff hT hS, mem_removeBranch]
  | edgePoint d' t ht0 ht1 =>
    rw [edgePoint_mem_subtree_iff hT hS_rem ht0 ht1, edgePoint_mem_subtree_iff hT hS ht0 ht1,
      mem_branch_vertex_iff_edgeProj_pos hT hadj, mem_removeBranch_iff hT hadj,
      mem_removeBranch_iff hT hadj]
    by_cases he : d'.edge = d.edge
    · constructor
      · rintro ⟨⟨_, hr1⟩, ⟨_, hr2⟩⟩
        rcases (dart_edge_eq_iff d' d).mp he with rfl | rfl
        · exact absurd hr2 hbridge
        · exact absurd hr1 hbridge
      · rintro ⟨_, hnot⟩
        exfalso
        apply hnot
        rcases (dart_edge_eq_iff d' d).mp he with rfl | rfl
        · rw [edgeProj_edgePoint_self]
          exact mul_pos ht0 (W.dart_weight_pos d)
        · rw [edgeProj_edgePoint_symm]
          exact mul_pos (sub_pos.mpr ht1) (W.dart_weight_pos d)
    · have hadj_del : (W.graph.deleteEdges {d.edge}).Adj d'.fst d'.snd :=
        ⟨d'.adj, fun h => he (Set.mem_singleton_iff.mp h.1)⟩
      rw [edgeProj_edgePoint_of_edge_ne hT he, not_lt]
      constructor
      · rintro ⟨⟨hfS, hfr⟩, ⟨hsS, _⟩⟩
        exact ⟨⟨hfS, hsS⟩, ((edgeProj_vertex_eq_zero_iff hT d d'.fst).mpr hfr).le⟩
      · rintro ⟨⟨hfS, hsS⟩, hle⟩
        have hfr : (W.graph.deleteEdges {s(c, w)}).Reachable d'.fst c :=
          (edgeProj_vertex_eq_zero_iff hT d d'.fst).mp
            (le_antisymm hle (edgeProj_nonneg hT d _))
        exact ⟨⟨hfS, hfr⟩, ⟨hsS, hadj_del.symm.reachable.trans hfr⟩⟩

/-- After removing the branch at `c` toward `w`, every point of that branch has gate `c`. -/
theorem gate_subtree_removeBranch (hT : W.graph.IsTree) {S : Finset V}
    (hS : IsSubtreeVertexSet W S) {c w : V} (hc : c ∈ S) (hadj : W.graph.Adj c w)
    {z : MetricGraph W} (hbr : z ∈ branch (vertex c) (vertex w)) :
    gate (subtree W (removeBranch W S c w)) z = vertex c := by
  refine gate_eq_of_forall_mem_interval
    (vertex_mem_subtree W ((mem_removeBranch_iff hT hadj).mpr ⟨hc, .refl c⟩)) fun z' hz' => ?_
  rw [subtree_removeBranch hT hS hc hadj] at hz'
  have hz'_not := hz'.2
  rw [← branch_eq_of_mem hT hbr] at hz'_not
  exact of_not_not hz'_not

end RemoveBranch

end MetricGraph

end SimpleGraph
