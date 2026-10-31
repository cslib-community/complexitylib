/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Kruskal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# SimpleGraph Bridge for Kruskal's Algorithm

This module connects the multigraph and `DisjointSet.Partition` formulation of Kruskal's algorithm
in `Complexity.Algorithms.Lean.Kruskal.Basic` to Mathlib's `SimpleGraph`, `SimpleGraph.IsAcyclic`,
maximal acyclic subgraphs (`Maximal (fun H => H ≤ G ∧ H.IsAcyclic)`), and `SimpleGraph.IsTree`.

## Main definitions

* `WeightedEdge.sym2`: unordered vertex pair `s(e.u, e.v) : Sym2 (Fin n)` of a weighted edge.
* `toSimpleGraph`: simple graph on `Fin n` spanned by an edge list (discarding self-loops and
  collapsing parallel edges).
* `graphEdges`: canonical computable enumeration (`u < v` with `G.Adj u v`) of the undirected edges
  of `G : SimpleGraph (Fin n)` weighted by `w : Sym2 (Fin n) → W`.
* `kruskalGraph`, `kruskalGraphM`: pure and `TimeM Cost` Kruskal runners directly on a weighted
  `SimpleGraph (Fin n)`.

## Main results

* `rel_edgePartition_iff_reachable`, `numComponents_edgePartition_eq_one_iff_connected`:
  equivalence between `edgePartition` connectivity and `SimpleGraph.Reachable` /
  `SimpleGraph.Connected`.
* `isAcyclic_iff_toSimpleGraph`: exact characterization
  `IsAcyclic F ↔ (toSimpleGraph F).IsAcyclic ∧ (F.map WeightedEdge.sym2).Nodup ∧`
  `∀ e ∈ F, e.u ≠ e.v`.
* `toSimpleGraph_kruskalEdges_maximal_isAcyclic`, `toSimpleGraph_kruskalEdges_isTree`: the simple
  graph spanned by `kruskalEdges es` is a maximal acyclic subgraph of `toSimpleGraph es` (and a
  `SimpleGraph.IsTree` with `n - 1` edges when `toSimpleGraph es` is connected).
* `kruskalGraph_maximal_isAcyclic`, `sum_edgeFinset_kruskalGraph_le_of_maximal_isAcyclic`:
  `toSimpleGraph (kruskalGraph G w)` is a minimum-weight Mathlib spanning forest of `G`.
* `kruskalGraph_isTree`, `sum_edgeFinset_kruskalGraph_le_of_isTree`: when `G.Connected`,
  `toSimpleGraph (kruskalGraph G w)` is a minimum-weight Mathlib spanning tree of `G`.
* `eq_toSimpleGraph_kruskalGraph_of_injOn`, `eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn`:
  when `w` is injective on `G.edgeSet` (generalizing [Kruskal, Opening paragraph, Construction A,
  and uniqueness proof, pp. 48–50][Kruskal1956] to disconnected simple graphs and ordered
  cancellative monoids), the minimum spanning forest (and minimum spanning tree when connected) is
  **unique as a `SimpleGraph (Fin n)`**.
* `kruskalGraphM_comparisons_le`, `kruskalGraphM_ufSteps_le`, `kruskalGraphM_total_le`: explicit
  sorting comparison and disjoint-set step bounds in terms of `m = G.edgeFinset.card` and `n`.

## Cost model and limitations

`kruskalGraphM G w := kruskalM (graphEdges G w)` charges only the `List.mergeSortM` weight
comparisons (`Cost.comparisons`) and post-initialization `DisjointSet.UnionFind` forest steps
(`Cost.ufSteps`) performed on the extracted `m`-edge list. The pure `graphEdges G w` enumeration
pass (which inspects all `n²` ordered pairs in `List.finRange n`, evaluating `decide (G.Adj u v)`
and `w s(u, v)` on matching edges) and `DisjointSet.UnionFind.init n` (`O(n)` initialization) carry
`0` `TimeM Cost` charge; callers that already hold an explicit edge list should invoke `kruskalM`
directly.

## References

* [J. B. Kruskal, Jr., *On the Shortest Spanning Subtree of a Graph and the Traveling Salesman
  Problem*][Kruskal1956]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 23][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Kruskal

open Cslib.Algorithms.Lean.DisjointSet
open Cslib.Algorithms.Lean

/-! ### Edge-list projection to `SimpleGraph (Fin n)` -/

/-- Unordered endpoint pair `s(e.u, e.v)` of a weighted edge. -/
@[expose] def WeightedEdge.sym2 {n : ℕ} {W : Type} (e : WeightedEdge n W) : Sym2 (Fin n) :=
  s(e.u, e.v)

@[simp]
theorem WeightedEdge.sym2_eq {n : ℕ} {W : Type} (e : WeightedEdge n W) :
    e.sym2 = s(e.u, e.v) := rfl

/-- Simple graph on `Fin n` spanned by `es` (discarding self-loops and collapsing parallel
edges). -/
@[expose] def toSimpleGraph {n : ℕ} {W : Type} (es : List (WeightedEdge n W)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet ↑(es.map WeightedEdge.sym2).toFinset

instance instDecidableRelToSimpleGraphAdj {n : ℕ} {W : Type}
    (es : List (WeightedEdge n W)) : DecidableRel (toSimpleGraph es).Adj := by
  unfold toSimpleGraph
  infer_instance

theorem toSimpleGraph_adj {n : ℕ} {W : Type} (es : List (WeightedEdge n W)) (x y : Fin n) :
    (toSimpleGraph es).Adj x y ↔ s(x, y) ∈ es.map WeightedEdge.sym2 ∧ x ≠ y := by
  simp [toSimpleGraph, SimpleGraph.fromEdgeSet_adj]

@[simp]
theorem toSimpleGraph_nil {n : ℕ} {W : Type} :
    toSimpleGraph ([] : List (WeightedEdge n W)) = ⊥ := by
  simp [toSimpleGraph, SimpleGraph.fromEdgeSet_empty]

theorem toSimpleGraph_cons {n : ℕ} {W : Type} (e : WeightedEdge n W)
    (es : List (WeightedEdge n W)) :
    toSimpleGraph (e :: es) = SimpleGraph.edge e.u e.v ⊔ toSimpleGraph es := by
  ext x y
  simp only [toSimpleGraph_adj, List.map_cons, List.mem_cons, WeightedEdge.sym2_eq,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨hmem | hmem, hne⟩
    · rcases Sym2.eq_iff.mp hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl ⟨.inl ⟨rfl, rfl⟩, hne⟩
      · exact .inl ⟨.inr ⟨rfl, rfl⟩, hne⟩
    · exact .inr ⟨hmem, hne⟩
  · rintro (⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩ | ⟨hmem, hne⟩)
    · exact ⟨.inl rfl, hne⟩
    · exact ⟨.inl Sym2.eq_swap, hne⟩
    · exact ⟨.inr hmem, hne⟩

theorem toSimpleGraph_append {n : ℕ} {W : Type}
    (es₁ es₂ : List (WeightedEdge n W)) :
    toSimpleGraph (es₁ ++ es₂) = toSimpleGraph es₁ ⊔ toSimpleGraph es₂ := by
  ext x y
  simp [toSimpleGraph_adj, or_and_right]

theorem toSimpleGraph_singleton {n : ℕ} {W : Type} (e : WeightedEdge n W) :
    toSimpleGraph [e] = SimpleGraph.edge e.u e.v := by
  rw [toSimpleGraph_cons, toSimpleGraph_nil, sup_bot_eq]

/-- Permuting an edge list preserves `toSimpleGraph`. -/
theorem Perm.toSimpleGraph_eq {n : ℕ} {W : Type}
    {es₁ es₂ : List (WeightedEdge n W)} (h : es₁.Perm es₂) :
    toSimpleGraph es₁ = toSimpleGraph es₂ := by
  ext x y
  simp [toSimpleGraph_adj, (h.map WeightedEdge.sym2).mem_iff]

/-- A sub-multiset (`Subperm`) spans a subgraph. -/
theorem Subperm.toSimpleGraph_le {n : ℕ} {W : Type}
    {es₁ es₂ : List (WeightedEdge n W)} (h : es₁.Subperm es₂) :
    toSimpleGraph es₁ ≤ toSimpleGraph es₂ := by
  intro x y hadj
  rw [toSimpleGraph_adj] at hadj ⊢
  obtain ⟨e, he, hsym⟩ := List.mem_map.mp hadj.1
  exact ⟨hsym ▸ List.mem_map_of_mem (h.subset he), hadj.2⟩

/-! ### Reachability, connectedness, and acyclicity correspondence -/

/-- Exact correspondence between partition equivalence in `edgePartition es` and walk reachability
in `toSimpleGraph es`. -/
theorem rel_edgePartition_iff_reachable {n : ℕ} {W : Type}
    (es : List (WeightedEdge n W)) (x y : Fin n) :
    (edgePartition es).rel x y = true ↔ (toSimpleGraph es).Reachable x y := by
  rw [rel_edgePartition_iff_eqvGen]
  constructor
  · intro h
    induction h with
    | rel u v huv =>
      obtain ⟨e, he, rfl, rfl⟩ := huv
      rcases eq_or_ne e.u e.v with heq | hne
      · rw [heq]
      · refine SimpleGraph.Adj.reachable ?_
        rw [toSimpleGraph_adj]
        exact ⟨List.mem_map_of_mem he, hne⟩
    | refl u => exact SimpleGraph.Reachable.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rintro ⟨w⟩
    induction w with
    | nil => exact .refl _
    | @cons a b c hadj _ ih =>
      rw [toSimpleGraph_adj] at hadj
      obtain ⟨e, he, hsym⟩ := List.mem_map.mp hadj.1
      rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .trans _ _ _ (.rel _ _ ⟨e, he, rfl, rfl⟩) ih
      · exact .trans _ _ _ (.symm _ _ (.rel _ _ ⟨e, he, rfl, rfl⟩)) ih

/-- Two edge lists induce the same `edgePartition` iff their simple graphs have the same
`Reachable` relation. -/
theorem edgePartition_eq_iff_reachable_eq {n : ℕ} {W₁ W₂ : Type}
    (es₁ : List (WeightedEdge n W₁)) (es₂ : List (WeightedEdge n W₂)) :
    edgePartition es₁ = edgePartition es₂ ↔
      (toSimpleGraph es₁).Reachable = (toSimpleGraph es₂).Reachable := by
  constructor
  · intro h
    ext x y
    rw [← rel_edgePartition_iff_reachable, ← rel_edgePartition_iff_reachable, h]
  · intro h
    ext x y
    rw [Bool.eq_iff_iff, rel_edgePartition_iff_reachable, rel_edgePartition_iff_reachable, h]

/-- `edgePartition es` has a single connected component iff `toSimpleGraph es` is `Connected`
(including the empty-graph boundary `n = 0`, where both sides are false). -/
theorem numComponents_edgePartition_eq_one_iff_connected {n : ℕ} {W : Type}
    (es : List (WeightedEdge n W)) :
    (edgePartition es).numComponents = 1 ↔ (toSimpleGraph es).Connected := by
  constructor
  · intro hcomp
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hcomp
      · exact hpos
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨fun x y => ?_⟩
    rw [← rel_edgePartition_iff_reachable]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcomp
    have hx : (edgePartition es).classOf x = c :=
      Finset.mem_singleton.mp (hc ▸ (edgePartition es).classOf_mem_components x)
    have hy : (edgePartition es).classOf y = c :=
      Finset.mem_singleton.mp (hc ▸ (edgePartition es).classOf_mem_components y)
    exact Partition.classOf_eq_iff.mp (hx.trans hy.symm)
  · intro hconn
    obtain ⟨v₀⟩ := hconn.nonempty
    have hcomp : (edgePartition es).components = {(edgePartition es).classOf v₀} := by
      ext c
      simp only [Partition.mem_components, Finset.mem_singleton]
      constructor
      · rintro ⟨x, rfl⟩
        exact Partition.classOf_eq_iff.mpr
          ((rel_edgePartition_iff_reachable es x v₀).mpr (hconn x v₀))
      · rintro rfl
        exact ⟨v₀, rfl⟩
    unfold Partition.numComponents
    rw [hcomp, Finset.card_singleton]

private theorem isAcyclic_append_singleton {n : ℕ} {W : Type}
    (F : List (WeightedEdge n W)) (e : WeightedEdge n W) :
    IsAcyclic (F ++ [e]) ↔ IsAcyclic F ∧ (edgePartition F).rel e.u e.v = false := by
  rw [isAcyclic_iff, isAcyclic_iff]
  have hep : edgePartition (F ++ [e]) = (edgePartition F).merge e.u e.v := by
    simp [edgePartition]
  rw [hep, List.length_append, List.length_singleton]
  have hlow : n ≤ (edgePartition F).numComponents + F.length := by
    simpa [edgePartition] using
      numComponents_le_edgePartitionFrom_add_length (Partition.discrete n) F
  cases hrel : (edgePartition F).rel e.u e.v
  · have hm := Partition.numComponents_merge_of_not_rel hrel
    simp only [and_true]
    omega
  · rw [Partition.merge_of_rel hrel]
    simp only [Bool.true_eq_false, and_false, iff_false]
    omega

private theorem nodup_append_singleton {α : Type} (l : List α) (a : α) :
    (l ++ [a]).Nodup ↔ l.Nodup ∧ a ∉ l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or, ih, List.mem_cons]
    grind

/-- Exact equivalence between edge-list acyclicity `IsAcyclic F` and simple-graph acyclicity
`(toSimpleGraph F).IsAcyclic` without parallel edges or self-loops. -/
theorem isAcyclic_iff_toSimpleGraph {n : ℕ} {W : Type} (F : List (WeightedEdge n W)) :
    IsAcyclic F ↔
      (toSimpleGraph F).IsAcyclic ∧
      (F.map WeightedEdge.sym2).Nodup ∧
      ∀ e ∈ F, e.u ≠ e.v := by
  induction F using List.reverseRecOn with
  | nil => simp
  | append_singleton F₀ e ih =>
    rw [isAcyclic_append_singleton, ih, toSimpleGraph_append, toSimpleGraph_singleton,
      List.map_append, List.map_singleton, nodup_append_singleton]
    constructor
    · rintro ⟨⟨hacyc, hnodup, hloop⟩, hrel⟩
      have hnreach : ¬(toSimpleGraph F₀).Reachable e.u e.v := by
        rw [← rel_edgePartition_iff_reachable, hrel]
        decide
      have hne : e.u ≠ e.v := fun heq => hnreach (heq ▸ SimpleGraph.Reachable.rfl)
      have hnot_mem : e.sym2 ∉ F₀.map WeightedEdge.sym2 := fun hmem =>
        hnreach (SimpleGraph.Adj.reachable ((toSimpleGraph_adj F₀ e.u e.v).mpr ⟨hmem, hne⟩))
      refine ⟨hacyc.sup_edge_of_not_reachable hnreach, ⟨hnodup, hnot_mem⟩, ?_⟩
      intro f hf
      rcases List.mem_append.mp hf with hf₀ | hfe
      · exact hloop f hf₀
      · rwa [List.mem_singleton.mp hfe]
    · rintro ⟨hacyc_sup, ⟨hnodup, hnot_mem⟩, hloop⟩
      have hne : e.u ≠ e.v := hloop e (by simp)
      have hloop₀ : ∀ f ∈ F₀, f.u ≠ f.v := fun f hf => hloop f (List.mem_append_left _ hf)
      have hnadj : ¬(toSimpleGraph F₀).Adj e.u e.v := fun hadj =>
        hnot_mem ((toSimpleGraph_adj F₀ e.u e.v).mp hadj).1
      obtain ⟨hacyc₀, hreach_imp⟩ := SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.mp hacyc_sup
      have hnreach : ¬(toSimpleGraph F₀).Reachable e.u e.v := fun hr =>
        (hreach_imp hr).elim hne hnadj
      have hrel : (edgePartition F₀).rel e.u e.v = false := by
        cases h : (edgePartition F₀).rel e.u e.v
        · rfl
        · exact absurd ((rel_edgePartition_iff_reachable F₀ e.u e.v).mp h) hnreach
      exact ⟨⟨hacyc₀, hnodup, hloop₀⟩, hrel⟩

theorem IsAcyclic.toSimpleGraph_isAcyclic {n : ℕ} {W : Type} {F : List (WeightedEdge n W)}
    (hF : IsAcyclic F) : (toSimpleGraph F).IsAcyclic :=
  (isAcyclic_iff_toSimpleGraph F).mp hF |>.1

theorem IsAcyclic.nodup_map_sym2 {n : ℕ} {W : Type} {F : List (WeightedEdge n W)}
    (hF : IsAcyclic F) : (F.map WeightedEdge.sym2).Nodup :=
  (isAcyclic_iff_toSimpleGraph F).mp hF |>.2.1

/-- When `es` has no self-loops, `(toSimpleGraph es).edgeFinset` is `(es.map sym2).toFinset`. -/
theorem edgeFinset_toSimpleGraph_of_no_loops {n : ℕ} {W : Type}
    {es : List (WeightedEdge n W)} (hloop : ∀ e ∈ es, e.u ≠ e.v) :
    (toSimpleGraph es).edgeFinset = (es.map WeightedEdge.sym2).toFinset := by
  ext z
  induction z using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, toSimpleGraph_adj,
      List.mem_toFinset, and_iff_left_iff_imp]
    intro hmem
    obtain ⟨e, he, hsym⟩ := List.mem_map.mp hmem
    rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hloop e he
    · exact (hloop e he).symm

/-- An acyclic edge list `F` has `(toSimpleGraph F).edgeFinset.card = F.length`. -/
theorem IsAcyclic.card_edgeFinset_toSimpleGraph {n : ℕ} {W : Type}
    {F : List (WeightedEdge n W)} (hF : IsAcyclic F) :
    (toSimpleGraph F).edgeFinset.card = F.length := by
  obtain ⟨_, hnodup, hloop⟩ := (isAcyclic_iff_toSimpleGraph F).mp hF
  rw [edgeFinset_toSimpleGraph_of_no_loops hloop, List.toFinset_card_of_nodup hnodup,
    List.length_map]

private theorem sum_toFinset_of_nodup {α W : Type} [DecidableEq α] [AddCommMonoid W]
    (f : α → W) {l : List α} (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, f x) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.nodup_cons.mp hl
    rw [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr ha), ih has,
      List.map_cons, List.sum_cons]

/-- When `F` is acyclic and every edge in `F` carries weight `w e.sym2`, `totalWeight F` equals
`∑ z ∈ (toSimpleGraph F).edgeFinset, w z`. -/
theorem IsAcyclic.sum_edgeFinset_toSimpleGraph {n : ℕ} {W : Type} [AddCommMonoid W]
    {F : List (WeightedEdge n W)} (hF : IsAcyclic F) (w : Sym2 (Fin n) → W)
    (hw : ∀ e ∈ F, e.weight = w e.sym2) :
    (∑ z ∈ (toSimpleGraph F).edgeFinset, w z) = totalWeight F := by
  obtain ⟨_, hnodup, hloop⟩ := (isAcyclic_iff_toSimpleGraph F).mp hF
  rw [edgeFinset_toSimpleGraph_of_no_loops hloop, sum_toFinset_of_nodup w hnodup, List.map_map,
    totalWeight]
  congr 1
  exact List.map_congr_left fun e he => (hw e he).symm

/-- Every `IsSpanningForest es F` projects to a Mathlib maximal acyclic subgraph of
`toSimpleGraph es`. -/
theorem IsSpanningForest.toSimpleGraph_maximal_isAcyclic {n : ℕ} {W : Type}
    {es F : List (WeightedEdge n W)} (hF : IsSpanningForest es F) :
    Maximal (fun H => H ≤ toSimpleGraph es ∧ H.IsAcyclic) (toSimpleGraph F) := by
  obtain ⟨hsub, hacyc, hpart⟩ := hF
  rw [SimpleGraph.maximal_isAcyclic_iff_reachable_eq (Subperm.toSimpleGraph_le hsub)
    hacyc.toSimpleGraph_isAcyclic]
  exact (edgePartition_eq_iff_reachable_eq F es).mp hpart

/-- `toSimpleGraph (kruskalEdges es)` is a maximal acyclic subgraph of `toSimpleGraph es`. -/
theorem toSimpleGraph_kruskalEdges_maximal_isAcyclic {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    Maximal (fun H => H ≤ toSimpleGraph es ∧ H.IsAcyclic) (toSimpleGraph (kruskalEdges es)) :=
  (kruskalEdges_isSpanningForest es).toSimpleGraph_maximal_isAcyclic

/-- When `toSimpleGraph es` is connected, `toSimpleGraph (kruskalEdges es)` is a
`SimpleGraph.IsTree` with `(kruskalEdges es).length + 1 = n`. -/
theorem toSimpleGraph_kruskalEdges_isTree {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    {es : List (WeightedEdge n W)} (hconn : (toSimpleGraph es).Connected) :
    (toSimpleGraph (kruskalEdges es)).IsTree ∧ (kruskalEdges es).length + 1 = n := by
  have hmax := toSimpleGraph_kruskalEdges_maximal_isAcyclic es
  have hle : toSimpleGraph (kruskalEdges es) ≤ toSimpleGraph es := hmax.prop.1
  have htree : (toSimpleGraph (kruskalEdges es)).IsTree :=
    (hconn.maximal_le_isAcyclic_iff_isTree hle).mp hmax
  have hcard := htree.card_edgeFinset
  rw [(kruskalEdges_isAcyclic es).card_edgeFinset_toSimpleGraph, Fintype.card_fin] at hcard
  exact ⟨htree, hcard⟩

/-! ### Canonical Kruskal runner on weighted `SimpleGraph (Fin n)` -/

/-- Canonical computable enumeration of the undirected edges of `G : SimpleGraph (Fin n)`:
pairs `(u, v)` with `u < v` and `G.Adj u v`, weighted by `w s(u, v)`. Each undirected edge in
`G.edgeFinset` appears once. -/
@[expose] def graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → W) : List (WeightedEdge n W) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => decide (u < v) && decide (G.Adj u v)).map fun v =>
      ⟨u, v, w s(u, v)⟩

/-- Exact membership predicate for `graphEdges G w`. -/
theorem mem_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → W) (e : WeightedEdge n W) :
    e ∈ graphEdges G w ↔ e.u < e.v ∧ G.Adj e.u e.v ∧ e.weight = w s(e.u, e.v) := by
  simp only [graphEdges, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, ⟨hlt, hadj⟩, rfl⟩
    exact ⟨hlt, hadj, rfl⟩
  · rintro ⟨hlt, hadj, hw⟩
    refine ⟨e.u, e.v, ⟨hlt, hadj⟩, ?_⟩
    cases e
    simp_all

/-- `(graphEdges G w)` contains no duplicate edges. -/
theorem nodup_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → W) : (graphEdges G w).Nodup := by
  unfold graphEdges
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · refine List.Nodup.map (fun v₁ v₂ h => ?_) ((List.nodup_finRange n).filter _)
    exact congrArg WeightedEdge.v h
  · refine (List.nodup_finRange n).imp ?_
    intro u₁ u₂ hne e he₁ he₂
    simp only [List.mem_map, List.mem_filter] at he₁ he₂
    obtain ⟨_, _, heq₁⟩ := he₁
    obtain ⟨_, _, heq₂⟩ := he₂
    exact hne ((congrArg WeightedEdge.u heq₁).trans (congrArg WeightedEdge.u heq₂).symm)

/-- Unordered endpoint pairs in `graphEdges G w` have no duplicates. -/
theorem nodup_map_sym2_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    ((graphEdges G w).map WeightedEdge.sym2).Nodup := by
  refine (nodup_graphEdges G w).map_on fun e₁ he₁ e₂ he₂ hsym => ?_
  obtain ⟨hlt₁, _, hw₁⟩ := (mem_graphEdges G w e₁).mp he₁
  obtain ⟨hlt₂, _, hw₂⟩ := (mem_graphEdges G w e₂).mp he₂
  rcases Sym2.eq_iff.mp hsym with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · cases e₁
    cases e₂
    dsimp only at hu hv hw₁ hw₂
    subst hu hv
    rw [hw₁, hw₂]
  · exfalso
    rw [hu, hv] at hlt₁
    exact lt_asymm hlt₁ hlt₂

/-- `s(x, y)` appears in `(graphEdges G w).map sym2` iff `G.Adj x y`. -/
theorem mem_map_sym2_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) (x y : Fin n) :
    s(x, y) ∈ (graphEdges G w).map WeightedEdge.sym2 ↔ G.Adj x y := by
  simp only [List.mem_map, mem_graphEdges, WeightedEdge.sym2_eq]
  constructor
  · rintro ⟨e, ⟨_, hadj, _⟩, hsym⟩
    rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · intro hadj
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
    · exact ⟨⟨x, y, w s(x, y)⟩, ⟨hlt, hadj, rfl⟩, rfl⟩
    · exact ⟨⟨y, x, w s(y, x)⟩, ⟨hgt, hadj.symm, rfl⟩, Sym2.eq_swap⟩

/-- `toSimpleGraph (graphEdges G w)` recovers `G` exactly. -/
@[simp]
theorem toSimpleGraph_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    toSimpleGraph (graphEdges G w) = G := by
  ext x y
  rw [toSimpleGraph_adj, mem_map_sym2_graphEdges]
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

/-- `G.edgeFinset` agrees with `((graphEdges G w).map sym2).toFinset` for any `Fintype G.edgeSet`
instance. -/
theorem edgeFinset_eq_toFinset_graphEdges {n : ℕ} {W : Type}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (w : Sym2 (Fin n) → W) :
    G.edgeFinset = ((graphEdges G w).map WeightedEdge.sym2).toFinset := by
  ext z
  induction z using Sym2.ind with
  | _ x y => simp [mem_map_sym2_graphEdges]

/-- `(graphEdges G w)` has length `G.edgeFinset.card`. -/
@[simp]
theorem length_graphEdges {n : ℕ} {W : Type} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Fintype G.edgeSet] (w : Sym2 (Fin n) → W) :
    (graphEdges G w).length = G.edgeFinset.card := by
  rw [edgeFinset_eq_toFinset_graphEdges G w,
    List.toFinset_card_of_nodup (nodup_map_sym2_graphEdges G w), List.length_map]

/-- If `F ≤ G`, `graphEdges F w` is a sub-multiset of `graphEdges G w`. -/
theorem graphEdges_subperm_of_le {n : ℕ} {W : Type}
    {F G : SimpleGraph (Fin n)} [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hle : F ≤ G) (w : Sym2 (Fin n) → W) :
    (graphEdges F w).Subperm (graphEdges G w) := by
  refine List.subperm_of_subset (nodup_graphEdges F w) fun e he => ?_
  obtain ⟨hlt, hadj, hw⟩ := (mem_graphEdges F w e).mp he
  exact (mem_graphEdges G w e).mpr ⟨hlt, hle hadj, hw⟩

/-- For any subgraph `F`, `totalWeight (graphEdges F w)` equals `∑ e ∈ F.edgeFinset, w e`. -/
theorem totalWeight_graphEdges {n : ℕ} {W : Type} [AddCommMonoid W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] [Fintype F.edgeSet] (w : Sym2 (Fin n) → W) :
    totalWeight (graphEdges F w) = ∑ z ∈ F.edgeFinset, w z := by
  rw [edgeFinset_eq_toFinset_graphEdges F w,
    sum_toFinset_of_nodup w (nodup_map_sym2_graphEdges F w), List.map_map, totalWeight]
  congr 1
  exact List.map_congr_left fun e he => ((mem_graphEdges F w e).mp he).2.2

/-- Every Mathlib maximal acyclic subgraph `F` of `G` corresponds to an `IsSpanningForest` of
`graphEdges G w`. -/
theorem isSpanningForest_graphEdges_of_maximal_isAcyclic {n : ℕ} {W : Type}
    {F G : SimpleGraph (Fin n)} [DecidableRel F.Adj] [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → W) (hF : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) F) :
    IsSpanningForest (graphEdges G w) (graphEdges F w) := by
  have hle : F ≤ G := hF.prop.1
  have hacyc : F.IsAcyclic := hF.prop.2
  have hreach : F.Reachable = G.Reachable :=
    (SimpleGraph.maximal_isAcyclic_iff_reachable_eq hle hacyc).mp hF
  have hloop : ∀ e ∈ graphEdges F w, e.u ≠ e.v :=
    fun e he => ne_of_lt ((mem_graphEdges F w e).mp he).1
  have hacyc_list : IsAcyclic (graphEdges F w) := by
    rw [isAcyclic_iff_toSimpleGraph, toSimpleGraph_graphEdges]
    exact ⟨hacyc, nodup_map_sym2_graphEdges F w, hloop⟩
  have hpart : edgePartition (graphEdges F w) = edgePartition (graphEdges G w) := by
    rw [edgePartition_eq_iff_reachable_eq, toSimpleGraph_graphEdges, toSimpleGraph_graphEdges]
    exact hreach
  exact ⟨graphEdges_subperm_of_le hle w, hacyc_list, hpart⟩

/-- Pure Kruskal runner on a weighted `SimpleGraph (Fin n)`. -/
@[expose] def kruskalGraph {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    List (WeightedEdge n W) :=
  kruskalEdges (graphEdges G w)

/-- `toSimpleGraph (kruskalGraph G w)` is a Mathlib maximal acyclic subgraph (spanning forest) of
`G`. -/
theorem kruskalGraph_maximal_isAcyclic {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (toSimpleGraph (kruskalGraph G w)) := by
  simpa only [kruskalGraph, toSimpleGraph_graphEdges] using
    toSimpleGraph_kruskalEdges_maximal_isAcyclic (graphEdges G w)

/-- The edge-finset weight sum of `toSimpleGraph (kruskalGraph G w)` equals
`totalWeight (kruskalGraph G w)`. -/
theorem sum_edgeFinset_toSimpleGraph_kruskalGraph {n : ℕ} {W : Type}
    [AddCommMonoid W] [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    (∑ z ∈ (toSimpleGraph (kruskalGraph G w)).edgeFinset, w z) =
      totalWeight (kruskalGraph G w) := by
  refine (kruskalEdges_isAcyclic (graphEdges G w)).sum_edgeFinset_toSimpleGraph w ?_
  intro e he
  have he_mem : e ∈ graphEdges G w := (kruskalEdges_subperm (graphEdges G w)).subset he
  exact ((mem_graphEdges G w e).mp he_mem).2.2

/-- **Simple-graph Kruskal spanning-forest optimality** (generalizing [Cormen et al., Section 23.2,
`MST-KRUSKAL`, p. 631][CLRS2009] from connected real-weighted graphs to arbitrary finite simple
graphs over `[AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]`):
`toSimpleGraph (kruskalGraph G w)` minimizes `∑ e ∈ F.edgeFinset, w e` over all Mathlib spanning
forests `F` of `G` (without requiring `DecidableRel F.Adj` on competing subgraphs `F`). -/
theorem sum_edgeFinset_kruskalGraph_le_of_maximal_isAcyclic {n : ℕ} {W : Type}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W)
    (F : SimpleGraph (Fin n)) [Fintype F.edgeSet]
    (hF : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) F) :
    (∑ z ∈ (toSimpleGraph (kruskalGraph G w)).edgeFinset, w z) ≤
      ∑ z ∈ F.edgeFinset, w z := by
  classical
  have hsf := isSpanningForest_graphEdges_of_maximal_isAcyclic w hF
  have hmin := (kruskalEdges_isMinSpanningForest (graphEdges G w)).2 (graphEdges F w) hsf
  rw [sum_edgeFinset_toSimpleGraph_kruskalGraph, kruskalGraph, ← totalWeight_graphEdges F w]
  exact hmin

/-- When `G` is connected, `toSimpleGraph (kruskalGraph G w)` is a `SimpleGraph.IsTree` with
`n - 1` edges (`(kruskalGraph G w).length + 1 = n`). -/
theorem kruskalGraph_isTree {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hconn : G.Connected)
    (w : Sym2 (Fin n) → W) :
    (toSimpleGraph (kruskalGraph G w)).IsTree ∧ (kruskalGraph G w).length + 1 = n := by
  have hconn' : (toSimpleGraph (graphEdges G w)).Connected := by
    rwa [toSimpleGraph_graphEdges]
  exact toSimpleGraph_kruskalEdges_isTree hconn'

/-- **Simple-graph Kruskal minimum spanning tree optimality** ([Cormen et al., Section 23.2,
p. 631][CLRS2009]): on a connected graph `G`, `toSimpleGraph (kruskalGraph G w)` minimizes
`∑ e ∈ T.edgeFinset, w e` over all spanning trees `T ≤ G`. -/
theorem sum_edgeFinset_kruskalGraph_le_of_isTree {n : ℕ} {W : Type}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hconn : G.Connected)
    (w : Sym2 (Fin n) → W) (T : SimpleGraph (Fin n)) [Fintype T.edgeSet]
    (hle : T ≤ G) (hT : T.IsTree) :
    (∑ z ∈ (toSimpleGraph (kruskalGraph G w)).edgeFinset, w z) ≤
      ∑ z ∈ T.edgeFinset, w z :=
  sum_edgeFinset_kruskalGraph_le_of_maximal_isAcyclic G w T
    ((hconn.maximal_le_isAcyclic_iff_isTree hle).mpr hT)

/-- **Distinct-weight uniqueness on simple graphs** (generalizing [Kruskal, Opening paragraph,
Construction A, and uniqueness proof, pp. 48–50][Kruskal1956]): when `w` is injective on
`G.edgeSet`, any minimum-weight spanning forest `F` of `G` is equal as a `SimpleGraph (Fin n)` to
`toSimpleGraph (kruskalGraph G w)`. -/
theorem eq_toSimpleGraph_kruskalGraph_of_injOn {n : ℕ} {W : Type}
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W)
    (hinj : Set.InjOn w G.edgeSet)
    {F : SimpleGraph (Fin n)} [Fintype F.edgeSet]
    (hF : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) F)
    (hopt : (∑ z ∈ F.edgeFinset, w z) ≤
      ∑ z ∈ (toSimpleGraph (kruskalGraph G w)).edgeFinset, w z) :
    F = toSimpleGraph (kruskalGraph G w) := by
  classical
  have hnodup_w : ((graphEdges G w).map WeightedEdge.weight).Nodup := by
    have hmap : (graphEdges G w).map WeightedEdge.weight =
        ((graphEdges G w).map WeightedEdge.sym2).map w := by
      rw [List.map_map]
      exact List.map_congr_left fun e he => ((mem_graphEdges G w e).mp he).2.2
    rw [hmap]
    refine (nodup_map_sym2_graphEdges G w).map_on fun z₁ hz₁ z₂ hz₂ hwz => ?_
    have hm₁ : z₁ ∈ G.edgeSet := by
      obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp hz₁
      simpa using ((mem_graphEdges G w e₁).mp he₁).2.1
    have hm₂ : z₂ ∈ G.edgeSet := by
      obtain ⟨e₂, he₂, rfl⟩ := List.mem_map.mp hz₂
      simpa using ((mem_graphEdges G w e₂).mp he₂).2.1
    exact hinj hm₁ hm₂ hwz
  have hsf_F : IsSpanningForest (graphEdges G w) (graphEdges F w) :=
    isSpanningForest_graphEdges_of_maximal_isAcyclic w hF
  have hmin_F : IsMinSpanningForest (graphEdges G w) (graphEdges F w) := by
    refine ⟨hsf_F, fun H hH => ?_⟩
    have hk := (kruskalEdges_isMinSpanningForest (graphEdges G w)).2 H hH
    have hle_k : totalWeight (graphEdges F w) ≤ totalWeight (kruskalGraph G w) := by
      rw [totalWeight_graphEdges F w, ← sum_edgeFinset_toSimpleGraph_kruskalGraph]
      exact hopt
    exact hle_k.trans hk
  have hperm := perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights hnodup_w hmin_F
  calc
    F = toSimpleGraph (graphEdges F w) := (toSimpleGraph_graphEdges F w).symm
    _ = toSimpleGraph (kruskalGraph G w) := Perm.toSimpleGraph_eq hperm

/-- Connected specialization of `eq_toSimpleGraph_kruskalGraph_of_injOn`: when `G` is connected and
`w` is injective on `G.edgeSet`, `toSimpleGraph (kruskalGraph G w)` is the unique minimum-weight
spanning tree of `G`. -/
theorem eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn {n : ℕ} {W : Type}
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (hconn : G.Connected)
    (w : Sym2 (Fin n) → W) (hinj : Set.InjOn w G.edgeSet)
    {T : SimpleGraph (Fin n)} [Fintype T.edgeSet]
    (hle : T ≤ G) (hT : T.IsTree)
    (hopt : (∑ z ∈ T.edgeFinset, w z) ≤
      ∑ z ∈ (toSimpleGraph (kruskalGraph G w)).edgeFinset, w z) :
    T = toSimpleGraph (kruskalGraph G w) :=
  eq_toSimpleGraph_kruskalGraph_of_injOn G w hinj
    ((hconn.maximal_le_isAcyclic_iff_isTree hle).mpr hT) hopt

/-! ### `TimeM Cost` Kruskal runner on `SimpleGraph (Fin n)` -/

/-- Execute Kruskal's algorithm in `TimeM Cost` on the canonical edge list `graphEdges G w`.
Note that `Cost` charges sorting comparisons and post-initialization `UnionFind` forest steps on the
extracted `m`-edge list; the pure `graphEdges G w` enumeration (`Θ(n²)` adjacency/weight checks) and
`DisjointSet.UnionFind.init n` carry `0` `TimeM Cost` charge. -/
@[expose] def kruskalGraphM {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    TimeM Cost (Output n W) :=
  kruskalM (graphEdges G w)

@[simp]
theorem kruskalGraphM_forest {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    (kruskalGraphM G w).ret.forest = kruskalGraph G w :=
  kruskalM_forest (graphEdges G w)

/-- Sorting comparison bound for `kruskalGraphM` in terms of `m = G.edgeFinset.card`: at most
`m * ⌈log₂ m⌉` weight comparisons. -/
theorem kruskalGraphM_comparisons_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    (kruskalGraphM G w).time.comparisons ≤
      G.edgeFinset.card * Nat.clog 2 G.edgeFinset.card := by
  simpa only [kruskalGraphM, length_graphEdges] using
    kruskalM_comparisons_le (graphEdges G w)

/-- Disjoint-set forest step bound for `kruskalGraphM` in terms of `m = G.edgeFinset.card` and `n`:
at most `m * (2 * ⌊log₂ n⌋ + 3)` union-find steps. -/
theorem kruskalGraphM_ufSteps_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    (kruskalGraphM G w).time.ufSteps ≤ G.edgeFinset.card * (2 * Nat.log 2 n + 3) := by
  simpa only [kruskalGraphM, length_graphEdges] using
    kruskalM_ufSteps_le (graphEdges G w)

/-- Combined bound on `(kruskalGraphM G w).time.total` in terms of `m = G.edgeFinset.card` and
`n`. -/
theorem kruskalGraphM_total_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Sym2 (Fin n) → W) :
    (kruskalGraphM G w).time.total ≤
      G.edgeFinset.card * Nat.clog 2 G.edgeFinset.card +
        G.edgeFinset.card * (2 * Nat.log 2 n + 3) :=
  Nat.add_le_add (kruskalGraphM_comparisons_le G w) (kruskalGraphM_ufSteps_le G w)

end Cslib.Algorithms.Lean.Kruskal
