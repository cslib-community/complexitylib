/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.DisjointSet.UnionFind
public import Cslib.Algorithms.Lean.Sort.Merge
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
import Complexity.Algorithms.Lean.MergeSort.Comparator

/-!
# Kruskal's Minimum Spanning Forest and Tree Algorithm

This module formalizes Kruskal's greedy algorithm for minimum-weight spanning forests and minimum
spanning trees on finite multigraphs over `Fin n`, together with its functional correctness,
global optimality, distinct-weight uniqueness, `Cslib.Stateful` disjoint-set client specification,
and `TimeM` comparison and disjoint-set step bounds.

## Mathematical model and source mapping

An input multigraph on `n` vertices is represented as a finite list `es : List (WeightedEdge n W)`
of undirected weighted edges `(u, v, weight)` with `u v : Fin n` (allowing parallel edges,
self-loops, disconnected graphs, and negative or duplicate weights). Connectivity is tracked via
`Cslib.Algorithms.Lean.DisjointSet.Partition n`:

* `edgePartitionFrom p es` folds `Partition.merge` across `es` starting from `p`, and
  `edgePartition es := edgePartitionFrom (Partition.discrete n) es` is the induced
  connected-component partition on `Fin n`.
* `IsAcyclic F` states the exact component-edge conservation law
  `(edgePartition F).numComponents + F.length = n`: starting from `n` isolated vertices, every edge
  in `F` merges two previously distinct connected components. The companion module
  `Complexity.Algorithms.Lean.Kruskal.SimpleGraph` bridges `IsAcyclic`, `IsSpanningForest`, and
  `IsSpanningTree` to Mathlib's `SimpleGraph.IsAcyclic`, maximal acyclic subgraphs, and
  `SimpleGraph.IsTree`.
* `IsSpanningForest es F` requires `F.Subperm es`, `IsAcyclic F`, and
  `edgePartition F = edgePartition es` (matching maximal forest subgraphs of `es`).

Primary-source correspondence:

* **[Cormen et al., Chapter 23, Section 23.1 (Theorem 23.1, pp. 626–628, and Corollary 23.2,
  p. 628) and Section 23.2 (`MST-KRUSKAL`, pp. 631–633)][CLRS2009]**: `[CLRS2009]` formulates
  Theorem 23.1 and `MST-KRUSKAL` for connected, simple undirected graphs with real-valued edge
  weights. Here `kruskalEdges` sorts `es` in nondecreasing weight order via `List.mergeSort` and
  scans the sorted list, accepting each edge whose endpoints lie in distinct components;
  `kruskalEdges_isMinSpanningForest` generalizes global weight optimality to arbitrary finite
  multigraphs (connected or disconnected, with parallel edges, self-loops, and negative or equal
  weights) over any `[AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]`, and
  `kruskalEdges_isMinSpanningTree` specializes to connected inputs
  (`(edgePartition es).numComponents = 1`).
* **[Kruskal, Opening paragraph, Construction A, and uniqueness proof, pp. 48–50][Kruskal1956]**:
  Kruskal's original paper assumes a finite connected graph with distinct positive real edge lengths
  and proves (`T = A_{n-1}`, p. 50) that Construction A yields the unique shortest spanning subtree.
  Here `perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights` generalizes uniqueness (up to
  list permutation, hence exact edge-multiset equality) to arbitrary finite multigraphs (connected
  or disconnected) with distinct weights in any `[AddCancelCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W]`.

## Cost model and limitations

`kruskalM` executes Kruskal's algorithm in `TimeM Cost` with two separate operation counters:

* `Cost.comparisons`: exact number of edge-weight comparisons `decide (a.weight ≤ b.weight)`
  performed by `List.mergeSortM`, bounded by `m * Nat.clog 2 m` (`m = es.length`) via
  `Cslib.Algorithms.Lean.TimeM.time_mergeSortM_le`.
* `Cost.ufSteps`: exact number of disjoint-set forest steps (`find` parent-pointer inspections plus
  `union` root links) recorded by `Cslib.Algorithms.Lean.DisjointSet.UnionFind.run` on
  `kruskalClient`, bounded by `m * (2 * Nat.log 2 n + 3)` via `DisjointSet.UnionFind.run_correct`
  (worst-case `O(log n)` per operation from union by rank, rather than Tarjan's amortized
  `O(α(n))` inverse-Ackermann bound).
* `realized_kruskal` additionally decouples Kruskal's scan from any particular concrete forest:
  any `Cslib.Stateful.Realization` and `Cslib.Stateful.Bound` for `DisjointSet.spec n` immediately
  transfers its cost certificate to `kruskalClient (sortEdges es)`.

`DisjointSet.UnionFind.init n` (`O(n)` `MAKE-SET` initialization in `[CLRS2009]`, `MST-KRUSKAL`
lines 2–3, pp. 631, 633), list splitting/allocation in `List.mergeSortM` and `kruskalClient`, and
pure Lean array updates inside `Batteries.UnionFind` carry `0` `TimeM Cost` charge (so `Cost`
records only sorting weight comparisons and post-initialization `UnionFind` `find`/`union` steps,
not Word-RAM instructions; if a `Batteries.UnionFind` value were shared non-linearly, array updates
could copy, whereas `DisjointSet.UnionFind.run` threads its state single-threadedly).

## Main definitions

* `WeightedEdge`, `totalWeight`: weighted undirected multigraph edges on `Fin n` and edge-list
  weight sum.
* `edgePartitionFrom`, `edgePartition`: connected-component partitions induced by an edge list.
* `IsAcyclicFrom`, `IsAcyclic`, `IsSpanningForest`, `IsSpanningTree`, `IsMinSpanningForest`,
  `IsMinSpanningTree`: forest, spanning-forest, spanning-tree, and minimum-weight predicates.
* `kruskalScan`, `sortEdges`, `kruskalEdges`: pure Kruskal scan, weight merge-sort, and Kruskal's
  algorithm.
* `kruskalClient`: `DisjointSet.spec n` client for the Kruskal cycle-filtering pass.
* `Cost`, `Output`, `sortEdgesM`, `kruskalScanM`, `kruskalM`: structured two-resource cost profile,
  algorithm output, and `TimeM` implementations.

## Main results

* `rel_edgePartitionFrom_iff_eqvGen`, `rel_edgePartition_iff_eqvGen`: exact `Relation.EqvGen`
  characterization of edge-induced partitions.
* `numComponents_le_edgePartitionFrom_add_length`, `isAcyclicFrom_cons`: component-count lower bound
  and inductive characterization of relative acyclicity.
* `kruskalEdges_isSpanningForest`, `kruskalEdges_isMinSpanningForest`,
  `kruskalEdges_isMinSpanningTree`: Kruskal's algorithm computes a minimum-weight spanning forest
  (and a minimum spanning tree when connected).
* `perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights`: uniqueness of the minimum spanning
  forest up to permutation when edge weights are pairwise distinct.
* `realized_kruskal`: backend-parametric `Cslib.Stateful` correctness and resource bound for any
  realization of `DisjointSet.spec n`.
* `kruskalM_forest`, `kruskalM_rep`, `kruskalM_comparisons_le`, `kruskalM_ufSteps_le`,
  `kruskalM_total_le`: functional correctness, final union-find representation, `m ⌈log₂ m⌉`
  comparison bound, and `m (2 ⌊log₂ n⌋ + 3)` disjoint-set step bound for `kruskalM`.

## References

* [J. B. Kruskal, Jr., *On the Shortest Spanning Subtree of a Graph and the Traveling Salesman
  Problem*][Kruskal1956]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 23][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Kruskal

open Cslib.Stateful Cslib.Algorithms.Lean.DisjointSet

/-! ### Weighted edges and edge-induced partitions -/

/-- A weighted undirected edge on `Fin n` (allowing parallel edges and self-loops). -/
structure WeightedEdge (n : ℕ) (W : Type) where
  /-- First endpoint. -/
  u : Fin n
  /-- Second endpoint. -/
  v : Fin n
  /-- Edge weight. -/
  weight : W
  deriving Repr

namespace WeightedEdge

variable {n : ℕ} {W : Type}

instance instDecidableEq [DecidableEq W] : DecidableEq (WeightedEdge n W) := fun a b =>
  if hu : a.u = b.u then
    if hv : a.v = b.v then
      if hw : a.weight = b.weight then
        isTrue (by cases a; cases b; subst hu hv hw; rfl)
      else
        isFalse fun h => hw (congrArg weight h)
    else
      isFalse fun h => hv (congrArg v h)
  else
    isFalse fun h => hu (congrArg u h)

/-- Endpoint pair `(e.u, e.v)` forgetting the weight, for interoperability with unweighted
`DisjointSet.spanningForestEdges`. -/
@[expose] def endpoints (e : WeightedEdge n W) : Fin n × Fin n :=
  (e.u, e.v)

@[simp]
theorem endpoints_fst (e : WeightedEdge n W) : e.endpoints.1 = e.u := rfl

@[simp]
theorem endpoints_snd (e : WeightedEdge n W) : e.endpoints.2 = e.v := rfl

end WeightedEdge

/-- Total weight of an edge list. -/
@[expose] def totalWeight {n : ℕ} {W : Type} [AddCommMonoid W]
    (es : List (WeightedEdge n W)) : W :=
  (es.map WeightedEdge.weight).sum

@[simp]
theorem totalWeight_nil {n : ℕ} {W : Type} [AddCommMonoid W] :
    totalWeight ([] : List (WeightedEdge n W)) = 0 := rfl

@[simp]
theorem totalWeight_cons {n : ℕ} {W : Type} [AddCommMonoid W]
    (e : WeightedEdge n W) (es : List (WeightedEdge n W)) :
    totalWeight (e :: es) = e.weight + totalWeight es := by
  simp [totalWeight]

@[simp]
theorem totalWeight_append {n : ℕ} {W : Type} [AddCommMonoid W]
    (es₁ es₂ : List (WeightedEdge n W)) :
    totalWeight (es₁ ++ es₂) = totalWeight es₁ + totalWeight es₂ := by
  simp [totalWeight]

/-- Permuting an edge list preserves its total weight. -/
theorem Perm.totalWeight_eq {n : ℕ} {W : Type} [AddCommMonoid W]
    {es₁ es₂ : List (WeightedEdge n W)} (h : es₁.Perm es₂) :
    totalWeight es₁ = totalWeight es₂ :=
  (h.map WeightedEdge.weight).sum_eq

/-- Partition obtained by merging the endpoints of every edge in `es` starting from `p`. -/
@[expose] def edgePartitionFrom {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) : Partition n :=
  es.foldl (fun acc e => acc.merge e.u e.v) p

/-- Connected-component partition of `Fin n` induced by `es`. -/
@[expose] def edgePartition {n : ℕ} {W : Type} (es : List (WeightedEdge n W)) : Partition n :=
  edgePartitionFrom (Partition.discrete n) es

@[simp]
theorem edgePartitionFrom_nil {n : ℕ} {W : Type} (p : Partition n) :
    edgePartitionFrom p ([] : List (WeightedEdge n W)) = p := rfl

@[simp]
theorem edgePartitionFrom_cons {n : ℕ} {W : Type} (p : Partition n)
    (e : WeightedEdge n W) (es : List (WeightedEdge n W)) :
    edgePartitionFrom p (e :: es) = edgePartitionFrom (p.merge e.u e.v) es := rfl

@[simp]
theorem edgePartitionFrom_append {n : ℕ} {W : Type} (p : Partition n)
    (es₁ es₂ : List (WeightedEdge n W)) :
    edgePartitionFrom p (es₁ ++ es₂) = edgePartitionFrom (edgePartitionFrom p es₁) es₂ := by
  simp [edgePartitionFrom]

@[simp]
theorem edgePartition_nil {n : ℕ} {W : Type} :
    edgePartition ([] : List (WeightedEdge n W)) = Partition.discrete n := rfl

/-- `edgePartitionFrom p es` is the final partition reached by
`DisjointSet.spanningForestEdges WeightedEdge.endpoints es`. -/
theorem edgePartitionFrom_eq_eval_spanningForestEdges {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    edgePartitionFrom p es =
      (eval (DisjointSet.spec n)
        (DisjointSet.spanningForestEdges WeightedEdge.endpoints es) p).2 := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [edgePartitionFrom_cons, DisjointSet.eval_spanningForestEdges_cons]
    exact ih (p.merge e.u e.v)

/-- Exact equivalence-closure characterization of `edgePartitionFrom p es`. -/
theorem rel_edgePartitionFrom_iff_eqvGen {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) (a b : Fin n) :
    (edgePartitionFrom p es).rel a b = true ↔
      Relation.EqvGen (fun x y => p.rel x y = true ∨ ∃ e ∈ es, x = e.u ∧ y = e.v) a b := by
  rw [edgePartitionFrom_eq_eval_spanningForestEdges]
  exact DisjointSet.spanningForestEdges_rel_iff_eqvGen WeightedEdge.endpoints es p a b

/-- Two vertices are in the same component of `edgePartition es` iff they are connected by the
equivalence closure of the edges in `es`. -/
theorem rel_edgePartition_iff_eqvGen {n : ℕ} {W : Type}
    (es : List (WeightedEdge n W)) (a b : Fin n) :
    (edgePartition es).rel a b = true ↔
      Relation.EqvGen (fun x y => ∃ e ∈ es, x = e.u ∧ y = e.v) a b := by
  rw [edgePartition, rel_edgePartitionFrom_iff_eqvGen]
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      rcases hxy with hxy | he
      · rw [Partition.rel_discrete_eq_true.mp hxy]
        exact .refl y
      · exact .rel _ _ he
    | refl x => exact .refl x
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    exact h.mono fun _ _ hxy => .inr hxy

/-- Every edge in `es` relates its endpoints in `edgePartitionFrom p es`. -/
theorem rel_edgePartitionFrom_of_mem {n : ℕ} {W : Type} (p : Partition n)
    {e : WeightedEdge n W} {es : List (WeightedEdge n W)} (he : e ∈ es) :
    (edgePartitionFrom p es).rel e.u e.v = true :=
  (rel_edgePartitionFrom_iff_eqvGen p es e.u e.v).mpr (.rel _ _ (.inr ⟨e, he, rfl, rfl⟩))

/-- `edgePartitionFrom` is invariant under edge-list permutations. -/
theorem Perm.edgePartitionFrom_eq {n : ℕ} {W : Type}
    {es₁ es₂ : List (WeightedEdge n W)} (h : es₁.Perm es₂) (p : Partition n) :
    edgePartitionFrom p es₁ = edgePartitionFrom p es₂ := by
  ext a b
  rw [Bool.eq_iff_iff, rel_edgePartitionFrom_iff_eqvGen, rel_edgePartitionFrom_iff_eqvGen]
  constructor
  · intro hab
    exact hab.mono fun _ _ hxy =>
      hxy.elim .inl fun ⟨e, he, hu, hv⟩ => .inr ⟨e, h.mem_iff.mp he, hu, hv⟩
  · intro hab
    exact hab.mono fun _ _ hxy =>
      hxy.elim .inl fun ⟨e, he, hu, hv⟩ => .inr ⟨e, h.mem_iff.mpr he, hu, hv⟩

/-- `edgePartition` is invariant under edge-list permutations. -/
theorem Perm.edgePartition_eq {n : ℕ} {W : Type}
    {es₁ es₂ : List (WeightedEdge n W)} (h : es₁.Perm es₂) :
    edgePartition es₁ = edgePartition es₂ :=
  Perm.edgePartitionFrom_eq h (Partition.discrete n)

/-- Merging `(x, y)` before folding `es` is equal to folding `es` and then merging `(x, y)`. -/
theorem edgePartitionFrom_merge {n : ℕ} {W : Type} (p : Partition n) (x y : Fin n)
    (es : List (WeightedEdge n W)) :
    edgePartitionFrom (p.merge x y) es = (edgePartitionFrom p es).merge x y := by
  ext a b
  rw [Bool.eq_iff_iff, rel_edgePartitionFrom_iff_eqvGen, Partition.rel_merge_iff_eqvGen]
  constructor
  · intro h
    induction h with
    | rel u v huv =>
      rcases huv with huv | ⟨e, he, rfl, rfl⟩
      · exact (Partition.rel_merge_iff_eqvGen.mp huv).mono fun w z hwz =>
          hwz.elim (fun hwz' => .inl ((rel_edgePartitionFrom_iff_eqvGen p es w z).mpr
            (.rel _ _ (.inl hwz')))) .inr
      · exact .rel _ _ (.inl (rel_edgePartitionFrom_of_mem p he))
    | refl u => exact .refl u
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel u v huv =>
      rcases huv with huv | ⟨rfl, rfl⟩
      · exact ((rel_edgePartitionFrom_iff_eqvGen p es u v).mp huv).mono fun w z hwz =>
          hwz.elim (fun hwz' => .inl (Partition.rel_merge_eq_true.mpr (.inl hwz'))) .inr
      · exact .rel _ _ (.inl (Partition.rel_merge_eq_true.mpr
          (.inr (.inl ⟨p.refl u, p.refl v⟩))))
    | refl u => exact .refl u
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Each edge reduces the number of connected components by at most `1`. -/
theorem numComponents_le_edgePartitionFrom_add_length {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    p.numComponents ≤ (edgePartitionFrom p es).numComponents + es.length := by
  induction es generalizing p with
  | nil => simp
  | cons e es ih =>
    rw [edgePartitionFrom_cons, List.length_cons]
    have hrec := ih (p.merge e.u e.v)
    cases hrel : p.rel e.u e.v
    · have hm := Partition.numComponents_merge_of_not_rel hrel
      omega
    · have hm := Partition.numComponents_merge_of_rel hrel
      omega

/-! ### Relative acyclicity, spanning forests, and spanning trees -/

/-- `F` is acyclic relative to an initial partition `p` when every edge in `F` merges two distinct
components, decreasing the component count by `F.length`. -/
@[expose] def IsAcyclicFrom {n : ℕ} {W : Type} (p : Partition n)
    (F : List (WeightedEdge n W)) : Prop :=
  (edgePartitionFrom p F).numComponents + F.length = p.numComponents

/-- An edge list `F` on `Fin n` is acyclic (a forest) when each edge merges two distinct connected
components starting from `Partition.discrete n`, i.e.,
`(edgePartition F).numComponents + F.length = n`. -/
@[expose] def IsAcyclic {n : ℕ} {W : Type} (F : List (WeightedEdge n W)) : Prop :=
  IsAcyclicFrom (Partition.discrete n) F

instance instDecidableIsAcyclicFrom {n : ℕ} {W : Type} (p : Partition n)
    (F : List (WeightedEdge n W)) : Decidable (IsAcyclicFrom p F) :=
  inferInstanceAs
    (Decidable ((edgePartitionFrom p F).numComponents + F.length = p.numComponents))

instance instDecidableIsAcyclic {n : ℕ} {W : Type} (F : List (WeightedEdge n W)) :
    Decidable (IsAcyclic F) :=
  instDecidableIsAcyclicFrom (Partition.discrete n) F

@[simp]
theorem isAcyclicFrom_nil {n : ℕ} {W : Type} (p : Partition n) :
    IsAcyclicFrom p ([] : List (WeightedEdge n W)) := by
  simp [IsAcyclicFrom]

@[simp]
theorem isAcyclic_nil {n : ℕ} {W : Type} :
    IsAcyclic ([] : List (WeightedEdge n W)) := by
  simp [IsAcyclic]

theorem isAcyclic_iff {n : ℕ} {W : Type} (F : List (WeightedEdge n W)) :
    IsAcyclic F ↔ (edgePartition F).numComponents + F.length = n := by
  simp [IsAcyclic, IsAcyclicFrom, edgePartition]

/-- Inductive characterization of relative acyclicity: `e :: F` is acyclic over `p` iff `e`'s
endpoints lie in distinct classes of `p` and `F` is acyclic over `p.merge e.u e.v`. -/
theorem isAcyclicFrom_cons {n : ℕ} {W : Type} {p : Partition n} {e : WeightedEdge n W}
    {F : List (WeightedEdge n W)} :
    IsAcyclicFrom p (e :: F) ↔ p.rel e.u e.v = false ∧ IsAcyclicFrom (p.merge e.u e.v) F := by
  unfold IsAcyclicFrom
  rw [edgePartitionFrom_cons, List.length_cons]
  cases hrel : p.rel e.u e.v
  · have hm := Partition.numComponents_merge_of_not_rel hrel
    simp only [true_and]
    omega
  · simp only [Bool.true_eq_false, false_and, iff_false]
    rw [Partition.merge_of_rel hrel]
    have hle := numComponents_le_edgePartitionFrom_add_length p F
    omega

/-- Relative acyclicity is invariant under edge-list permutations. -/
theorem Perm.isAcyclicFrom_iff {n : ℕ} {W : Type} {p : Partition n}
    {F₁ F₂ : List (WeightedEdge n W)} (h : F₁.Perm F₂) :
    IsAcyclicFrom p F₁ ↔ IsAcyclicFrom p F₂ := by
  simp only [IsAcyclicFrom, Perm.edgePartitionFrom_eq h p, h.length_eq]

/-- Acyclicity is invariant under edge-list permutations. -/
theorem Perm.isAcyclic_iff {n : ℕ} {W : Type} {F₁ F₂ : List (WeightedEdge n W)}
    (h : F₁.Perm F₂) : IsAcyclic F₁ ↔ IsAcyclic F₂ :=
  Perm.isAcyclicFrom_iff h

/-- Every acyclic edge list on `Fin n` has at most `n` edges (and at most `n - 1` when `0 < n`). -/
theorem IsAcyclic.length_le {n : ℕ} {W : Type} {F : List (WeightedEdge n W)}
    (hF : IsAcyclic F) : F.length ≤ n := by
  have h := isAcyclic_iff F |>.mp hF
  omega

theorem IsAcyclic.length_le_pred {n : ℕ} {W : Type} {F : List (WeightedEdge n W)}
    (hn : 0 < n) (hF : IsAcyclic F) : F.length + 1 ≤ n := by
  have h := isAcyclic_iff F |>.mp hF
  have hpos := Partition.numComponents_pos hn (edgePartition F)
  omega

/-- No self-loop belongs to an acyclic edge list. -/
theorem IsAcyclic.ne_of_mem {n : ℕ} {W : Type} {F : List (WeightedEdge n W)}
    (hF : IsAcyclic F) {e : WeightedEdge n W} (he : e ∈ F) : e.u ≠ e.v := by
  classical
  have hcons := (Perm.isAcyclic_iff (List.perm_cons_erase he)).mp hF
  obtain ⟨hrel, _⟩ := isAcyclicFrom_cons.mp hcons
  intro heq
  rw [heq, Partition.rel_refl] at hrel
  cases hrel

/-- Redundant-edge extraction: if `L` has exactly one redundant merge over `p`, removing that
redundant edge yields a sub-list `L'` (`L.Perm (f :: L')`) with the same final partition and
`IsAcyclicFrom p L'`. -/
private theorem exists_perm_cons_of_numComponents_add_length_eq_succ {n : ℕ} {W : Type}
    {p : Partition n} {L : List (WeightedEdge n W)}
    (h : (edgePartitionFrom p L).numComponents + L.length = p.numComponents + 1) :
    ∃ f L', L.Perm (f :: L') ∧
      edgePartitionFrom p L' = edgePartitionFrom p L ∧
      IsAcyclicFrom p L' := by
  induction L generalizing p with
  | nil =>
    simp only [edgePartitionFrom_nil, List.length_nil, Nat.add_zero] at h
    omega
  | cons e L₀ ih =>
    rw [edgePartitionFrom_cons, List.length_cons] at h
    cases hrel : p.rel e.u e.v
    · have hm := Partition.numComponents_merge_of_not_rel hrel
      have h' : (edgePartitionFrom (p.merge e.u e.v) L₀).numComponents + L₀.length =
          (p.merge e.u e.v).numComponents + 1 := by omega
      obtain ⟨f, L₁, hperm, hpart, hacyc⟩ := ih h'
      refine ⟨f, e :: L₁, ?_, ?_, isAcyclicFrom_cons.mpr ⟨hrel, hacyc⟩⟩
      · exact (hperm.cons e).trans (List.Perm.swap f e L₁)
      · simpa only [edgePartitionFrom_cons] using hpart
    · rw [Partition.merge_of_rel hrel] at h
      have hacyc : IsAcyclicFrom p L₀ := by
        unfold IsAcyclicFrom
        omega
      refine ⟨e, L₀, List.Perm.refl _, ?_, hacyc⟩
      rw [edgePartitionFrom_cons, Partition.merge_of_rel hrel]

/-- Relative spanning forest of `es` starting from partition `p`. -/
@[expose] def IsSpanningForestFrom {n : ℕ} {W : Type} (p : Partition n)
    (es F : List (WeightedEdge n W)) : Prop :=
  F.Subperm es ∧ IsAcyclicFrom p F ∧ edgePartitionFrom p F = edgePartitionFrom p es

/-- `F` is a spanning forest of the multigraph `es` when `F` is a sub-multiset (`Subperm`) of `es`,
`F` is acyclic, and `F` induces the exact same connected components as `es`. -/
@[expose] def IsSpanningForest {n : ℕ} {W : Type}
    (es F : List (WeightedEdge n W)) : Prop :=
  F.Subperm es ∧ IsAcyclic F ∧ edgePartition F = edgePartition es

/-- `T` is a spanning tree of `es` when `T` is a sub-multiset of `es`, `T` is acyclic, and `T`
connects `Fin n` into a single component (`numComponents = 1`). -/
@[expose] def IsSpanningTree {n : ℕ} {W : Type}
    (es T : List (WeightedEdge n W)) : Prop :=
  T.Subperm es ∧ IsAcyclic T ∧ (edgePartition T).numComponents = 1

/-- `F` is a minimum-weight spanning forest of `es` when `F` is a spanning forest of `es` of
minimum `totalWeight`. -/
@[expose] def IsMinSpanningForest {n : ℕ} {W : Type} [AddCommMonoid W] [LE W]
    (es F : List (WeightedEdge n W)) : Prop :=
  IsSpanningForest es F ∧ ∀ F', IsSpanningForest es F' → totalWeight F ≤ totalWeight F'

/-- `T` is a minimum-weight spanning tree of `es` when `T` is a spanning tree of `es` of minimum
`totalWeight`. -/
@[expose] def IsMinSpanningTree {n : ℕ} {W : Type} [AddCommMonoid W] [LE W]
    (es T : List (WeightedEdge n W)) : Prop :=
  IsSpanningTree es T ∧ ∀ T', IsSpanningTree es T' → totalWeight T ≤ totalWeight T'

theorem isSpanningForest_iff_from_discrete {n : ℕ} {W : Type}
    (es F : List (WeightedEdge n W)) :
    IsSpanningForest es F ↔ IsSpanningForestFrom (Partition.discrete n) es F :=
  Iff.rfl

/-- Every spanning tree on a connected multigraph `(edgePartition es).numComponents = 1` is a
spanning forest, and vice versa. -/
theorem isSpanningTree_iff_isSpanningForest_of_connected {n : ℕ} {W : Type}
    {es T : List (WeightedEdge n W)} (hconn : (edgePartition es).numComponents = 1) :
    IsSpanningTree es T ↔ IsSpanningForest es T := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hconn
    · exact hpos
  constructor
  · rintro ⟨hsub, hacyc, hcomp⟩
    refine ⟨hsub, hacyc, ?_⟩
    -- Since `(edgePartition T).numComponents = 1`, all vertices are pairwise equivalent in `T`,
    -- and likewise in `es` because `(edgePartition es).numComponents = 1`.
    have hall_one : ∀ {q : Partition n}, q.numComponents = 1 → ∀ x y : Fin n, q.rel x y = true := by
      intro q hq x y
      have hcard : q.components.card = 1 := hq
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
      have hx : q.classOf x = c := Finset.mem_singleton.mp (hc ▸ q.classOf_mem_components x)
      have hy : q.classOf y = c := Finset.mem_singleton.mp (hc ▸ q.classOf_mem_components y)
      exact Partition.classOf_eq_iff.mp (hx.trans hy.symm)
    ext x y
    rw [hall_one hcomp x y, hall_one hconn x y]
  · rintro ⟨hsub, hacyc, hpart⟩
    exact ⟨hsub, hacyc, hpart.symm ▸ hconn⟩

/-- Every spanning tree on `Fin n` has `n - 1` edges (`T.length + 1 = n`). -/
theorem IsSpanningTree.length_add_one {n : ℕ} {W : Type} {es T : List (WeightedEdge n W)}
    (hT : IsSpanningTree es T) : T.length + 1 = n := by
  obtain ⟨_, hacyc, hcomp⟩ := hT
  have h := (isAcyclic_iff T).mp hacyc
  omega

/-- All spanning forests of the same multigraph `es` have the exact same cardinality
`n - (edgePartition es).numComponents`. -/
theorem IsSpanningForest.length_eq {n : ℕ} {W : Type} {es F₁ F₂ : List (WeightedEdge n W)}
    (h₁ : IsSpanningForest es F₁) (h₂ : IsSpanningForest es F₂) :
    F₁.length = F₂.length := by
  have ha₁ := (isAcyclic_iff F₁).mp h₁.2.1
  have ha₂ := (isAcyclic_iff F₂).mp h₂.2.1
  rw [h₁.2.2] at ha₁
  rw [h₂.2.2] at ha₂
  omega

/-! ### Pure Kruskal scan, merge-sort, optimality, and uniqueness -/

/-- Greedy Kruskal scan starting from partition `p`: inspect edges in order, accepting an edge iff
its endpoints currently lie in distinct classes of `p`. -/
@[expose] def kruskalScan {n : ℕ} {W : Type} (p : Partition n) :
    List (WeightedEdge n W) → List (WeightedEdge n W)
  | [] => []
  | e :: es =>
    if !p.rel e.u e.v then
      e :: kruskalScan (p.merge e.u e.v) es
    else
      kruskalScan p es

@[simp]
theorem kruskalScan_nil {n : ℕ} {W : Type} (p : Partition n) :
    kruskalScan p ([] : List (WeightedEdge n W)) = [] := rfl

@[simp]
theorem kruskalScan_cons {n : ℕ} {W : Type} (p : Partition n) (e : WeightedEdge n W)
    (es : List (WeightedEdge n W)) :
    kruskalScan p (e :: es) =
      if !p.rel e.u e.v then e :: kruskalScan (p.merge e.u e.v) es else kruskalScan p es := rfl

/-- `kruskalScan p es` is the edge list returned by
`DisjointSet.spanningForestEdges WeightedEdge.endpoints es`. -/
theorem kruskalScan_eq_eval_spanningForestEdges {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    kruskalScan p es =
      (eval (DisjointSet.spec n)
        (DisjointSet.spanningForestEdges WeightedEdge.endpoints es) p).1 := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [kruskalScan_cons, DisjointSet.eval_spanningForestEdges_cons]
    dsimp only [WeightedEdge.endpoints_fst, WeightedEdge.endpoints_snd]
    by_cases hrel : p.rel e.u e.v = true
    · simp [hrel, Partition.merge_of_rel hrel, ih p]
    · simp [hrel, ih (p.merge e.u e.v)]

/-- `kruskalScan p es` is an order-preserving sublist of `es`. -/
theorem kruskalScan_sublist {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    (kruskalScan p es).Sublist es := by
  rw [kruskalScan_eq_eval_spanningForestEdges]
  exact DisjointSet.spanningForestEdges_sublist WeightedEdge.endpoints es p

/-- `kruskalScan p es` preserves the final partition `edgePartitionFrom p es`. -/
theorem edgePartitionFrom_kruskalScan {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    edgePartitionFrom p (kruskalScan p es) = edgePartitionFrom p es := by
  rw [edgePartitionFrom_eq_eval_spanningForestEdges, kruskalScan_eq_eval_spanningForestEdges,
    DisjointSet.spanningForestEdges_idempotent_partition,
    ← edgePartitionFrom_eq_eval_spanningForestEdges]

/-- `kruskalScan p es` is acyclic relative to `p`. -/
theorem kruskalScan_isAcyclicFrom {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    IsAcyclicFrom p (kruskalScan p es) := by
  unfold IsAcyclicFrom
  rw [edgePartitionFrom_kruskalScan, edgePartitionFrom_eq_eval_spanningForestEdges,
    kruskalScan_eq_eval_spanningForestEdges]
  exact DisjointSet.spanningForestEdges_numComponents_add_length WeightedEdge.endpoints es p

/-- `kruskalScan p es` is a relative spanning forest of `es` over `p`. -/
theorem kruskalScan_isSpanningForestFrom {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    IsSpanningForestFrom p es (kruskalScan p es) :=
  ⟨(kruskalScan_sublist p es).subperm, kruskalScan_isAcyclicFrom p es,
    edgePartitionFrom_kruskalScan p es⟩

/-- Core exchange-inductive optimality of `kruskalScan` on weight-sorted inputs: for any initial
partition `p` and any relative spanning forest `H` of `sorted` over `p`, `kruskalScan p sorted` has
total weight at most `totalWeight H`. -/
theorem totalWeight_kruskalScan_le {n : ℕ} {W : Type}
    [AddCommMonoid W] [Preorder W] [IsOrderedAddMonoid W]
    (p : Partition n) {sorted H : List (WeightedEdge n W)}
    (hsorted : sorted.Pairwise (fun a b => a.weight ≤ b.weight))
    (hH : IsSpanningForestFrom p sorted H) :
    totalWeight (kruskalScan p sorted) ≤ totalWeight H := by
  induction sorted generalizing p H with
  | nil =>
    simp only [kruskalScan_nil, totalWeight_nil]
    rw [List.subperm_nil.mp hH.1, totalWeight_nil]
  | cons e es ih =>
    obtain ⟨he_le, hes_sorted⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨hsub, hacyc, hpart⟩ := hH
    obtain ⟨l, hlH, hsub_l⟩ := hsub
    have hHl := hlH.symm
    rw [kruskalScan_cons]
    cases hrel : p.rel e.u e.v
    · simp only [Bool.not_false, ↓reduceIte, totalWeight_cons]
      let p' := p.merge e.u e.v
      cases hsub_l with
      | cons _ hsl =>
        -- `H` avoids this copy of `e`: `l.Sublist es`, so `H.Subperm es`, and `H` has exactly one
        -- redundant merge over `p' = p.merge e.u e.v`.
        have he_rel : (edgePartitionFrom p H).rel e.u e.v = true := by
          rw [hpart]
          exact rel_edgePartitionFrom_of_mem p List.mem_cons_self
        have hp'H : edgePartitionFrom p' H = edgePartitionFrom p H := by
          rw [edgePartitionFrom_merge, Partition.merge_of_rel he_rel]
        have hp'es : edgePartitionFrom p' H = edgePartitionFrom p' es := by
          rw [hp'H, hpart, edgePartitionFrom_cons]
        have hm : p'.numComponents + 1 = p.numComponents :=
          Partition.numComponents_merge_of_not_rel hrel
        have hsucc : (edgePartitionFrom p' H).numComponents + H.length = p'.numComponents + 1 := by
          rw [hp'H]
          have ha : (edgePartitionFrom p H).numComponents + H.length = p.numComponents := hacyc
          omega
        obtain ⟨f, H', hHperm, hH'part, hH'acyc⟩ :=
          exists_perm_cons_of_numComponents_add_length_eq_succ hsucc
        have hf_es : f ∈ es :=
          hsl.subset (hHl.mem_iff.mp (hHperm.mem_iff.mpr List.mem_cons_self))
        have hef : e.weight ≤ f.weight := he_le f hf_es
        have hH'_sub : H'.Subperm es := by
          have h₁ : H'.Subperm (f :: H') := (List.Sublist.cons f (List.Sublist.refl H')).subperm
          exact (h₁.trans hHperm.symm.subperm).trans (hHl.subperm.trans hsl.subperm)
        have hH'_sf : IsSpanningForestFrom p' es H' :=
          ⟨hH'_sub, hH'acyc, hH'part.trans hp'es⟩
        have hrec := ih p' hes_sorted hH'_sf
        rw [Perm.totalWeight_eq hHperm, totalWeight_cons]
        exact add_le_add hef hrec
      | cons_cons _ hsl =>
        -- `H` contains this copy of `e`: `H.Perm (e :: l')` with `l'.Sublist es`.
        rename_i l'
        have hl'_acyc : IsAcyclicFrom p' l' :=
          (isAcyclicFrom_cons.mp ((Perm.isAcyclicFrom_iff hHl).mp hacyc)).2
        have hl'_part : edgePartitionFrom p' l' = edgePartitionFrom p' es := by
          calc
            edgePartitionFrom p' l' = edgePartitionFrom p (e :: l') := rfl
            _ = edgePartitionFrom p H := (Perm.edgePartitionFrom_eq hHl p).symm
            _ = edgePartitionFrom p (e :: es) := hpart
            _ = edgePartitionFrom p' es := rfl
        have hl'_sf : IsSpanningForestFrom p' es l' := ⟨hsl.subperm, hl'_acyc, hl'_part⟩
        have hrec := ih p' hes_sorted hl'_sf
        rw [Perm.totalWeight_eq hHl, totalWeight_cons]
        exact add_le_add le_rfl hrec
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hsub_l with
      | cons _ hsl =>
        have hpart' : edgePartitionFrom p H = edgePartitionFrom p es := by
          rw [hpart, edgePartitionFrom_cons, Partition.merge_of_rel hrel]
        exact ih p hes_sorted ⟨hHl.subperm.trans hsl.subperm, hacyc, hpart'⟩
      | cons_cons _ _ =>
        have hcons_acyc := (Perm.isAcyclicFrom_iff hHl).mp hacyc
        have hfalse := (isAcyclicFrom_cons.mp hcons_acyc).1
        rw [hrel] at hfalse
        cases hfalse

/-- Uniqueness of the minimum relative spanning forest on weight-sorted inputs with distinct
weights. -/
theorem perm_kruskalScan_of_totalWeight_le_of_nodup_weights {n : ℕ} {W : Type}
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    (p : Partition n) {sorted H : List (WeightedEdge n W)}
    (hsorted : sorted.Pairwise (fun a b => a.weight ≤ b.weight))
    (hnodup : (sorted.map WeightedEdge.weight).Nodup)
    (hH : IsSpanningForestFrom p sorted H)
    (hopt : totalWeight H ≤ totalWeight (kruskalScan p sorted)) :
    H.Perm (kruskalScan p sorted) := by
  induction sorted generalizing p H with
  | nil =>
    simp only [kruskalScan_nil]
    rw [List.subperm_nil.mp hH.1]
  | cons e es ih =>
    obtain ⟨he_le, hes_sorted⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨he_not_mem, hes_nodup⟩ := List.nodup_cons.mp hnodup
    obtain ⟨hsub, hacyc, hpart⟩ := hH
    obtain ⟨l, hlH, hsub_l⟩ := hsub
    have hHl := hlH.symm
    rw [kruskalScan_cons] at hopt ⊢
    cases hrel : p.rel e.u e.v
    · rw [hrel] at hopt
      simp only [Bool.not_false, ↓reduceIte] at hopt ⊢
      let p' := p.merge e.u e.v
      cases hsub_l with
      | cons _ hsl =>
        exfalso
        have he_rel : (edgePartitionFrom p H).rel e.u e.v = true := by
          rw [hpart]
          exact rel_edgePartitionFrom_of_mem p List.mem_cons_self
        have hp'H : edgePartitionFrom p' H = edgePartitionFrom p H := by
          rw [edgePartitionFrom_merge, Partition.merge_of_rel he_rel]
        have hp'es : edgePartitionFrom p' H = edgePartitionFrom p' es := by
          rw [hp'H, hpart, edgePartitionFrom_cons]
        have hm : p'.numComponents + 1 = p.numComponents :=
          Partition.numComponents_merge_of_not_rel hrel
        have hsucc : (edgePartitionFrom p' H).numComponents + H.length = p'.numComponents + 1 := by
          rw [hp'H]
          have ha : (edgePartitionFrom p H).numComponents + H.length = p.numComponents := hacyc
          omega
        obtain ⟨f, H', hHperm, hH'part, hH'acyc⟩ :=
          exists_perm_cons_of_numComponents_add_length_eq_succ hsucc
        have hf_es : f ∈ es :=
          hsl.subset (hHl.mem_iff.mp (hHperm.mem_iff.mpr List.mem_cons_self))
        have hne_w : e.weight ≠ f.weight := fun heq =>
          he_not_mem (heq ▸ List.mem_map_of_mem hf_es)
        have hlt_w : e.weight < f.weight := lt_of_le_of_ne (he_le f hf_es) hne_w
        have hH'_sub : H'.Subperm es := by
          have h₁ : H'.Subperm (f :: H') := (List.Sublist.cons f (List.Sublist.refl H')).subperm
          exact (h₁.trans hHperm.symm.subperm).trans (hHl.subperm.trans hsl.subperm)
        have hH'_sf : IsSpanningForestFrom p' es H' :=
          ⟨hH'_sub, hH'acyc, hH'part.trans hp'es⟩
        have hrec := totalWeight_kruskalScan_le p' hes_sorted hH'_sf
        have hstrict :
            totalWeight (e :: kruskalScan p' es) < totalWeight H := by
          rw [totalWeight_cons, Perm.totalWeight_eq hHperm, totalWeight_cons]
          exact add_lt_add_of_lt_of_le hlt_w hrec
        exact not_lt_of_ge hopt hstrict
      | cons_cons _ hsl =>
        rename_i l'
        have hl'_acyc : IsAcyclicFrom p' l' :=
          (isAcyclicFrom_cons.mp ((Perm.isAcyclicFrom_iff hHl).mp hacyc)).2
        have hl'_part : edgePartitionFrom p' l' = edgePartitionFrom p' es := by
          calc
            edgePartitionFrom p' l' = edgePartitionFrom p (e :: l') := rfl
            _ = edgePartitionFrom p H := (Perm.edgePartitionFrom_eq hHl p).symm
            _ = edgePartitionFrom p (e :: es) := hpart
            _ = edgePartitionFrom p' es := rfl
        have hl'_sf : IsSpanningForestFrom p' es l' := ⟨hsl.subperm, hl'_acyc, hl'_part⟩
        have hopt' : totalWeight l' ≤ totalWeight (kruskalScan p' es) := by
          rw [Perm.totalWeight_eq hHl, totalWeight_cons, totalWeight_cons] at hopt
          exact le_of_add_le_add_left hopt
        exact hHl.trans ((ih p' hes_sorted hes_nodup hl'_sf hopt').cons e)
    · rw [hrel] at hopt
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hopt ⊢
      cases hsub_l with
      | cons _ hsl =>
        have hpart' : edgePartitionFrom p H = edgePartitionFrom p es := by
          rw [hpart, edgePartitionFrom_cons, Partition.merge_of_rel hrel]
        exact ih p hes_sorted hes_nodup ⟨hHl.subperm.trans hsl.subperm, hacyc, hpart'⟩ hopt
      | cons_cons _ _ =>
        have hcons_acyc := (Perm.isAcyclicFrom_iff hHl).mp hacyc
        have hfalse := (isAcyclicFrom_cons.mp hcons_acyc).1
        rw [hrel] at hfalse
        cases hfalse

/-- Sort an edge list by nondecreasing weight using `List.mergeSort`. -/
@[expose] def sortEdges {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) : List (WeightedEdge n W) :=
  es.mergeSort fun a b => decide (a.weight ≤ b.weight)

@[simp]
theorem sortEdges_nil {n : ℕ} {W : Type} [LE W] [DecidableLE W] :
    sortEdges ([] : List (WeightedEdge n W)) = [] := by
  simp [sortEdges]

@[simp]
theorem sortEdges_singleton {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (e : WeightedEdge n W) :
    sortEdges [e] = [e] := by
  simp [sortEdges]

/-- Balanced-split unfolding step for `sortEdges` on lists of length at least `2`. -/
theorem sortEdges_cons_cons {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (a b : WeightedEdge n W) (es : List (WeightedEdge n W)) :
    sortEdges (a :: b :: es) =
      List.merge (sortEdges ((a :: b :: es).take ((es.length + 3) / 2)))
        (sortEdges ((a :: b :: es).drop ((es.length + 3) / 2)))
        (fun x y => decide (x.weight ≤ y.weight)) := by
  unfold sortEdges
  have h := List.mergeSort_append
    ((a :: b :: es).take ((es.length + 3) / 2))
    ((a :: b :: es).drop ((es.length + 3) / 2))
    (le := fun x y : WeightedEdge n W => decide (x.weight ≤ y.weight))
    (by simp; omega)
    (by simp; omega)
  rwa [List.take_append_drop] at h

/-- `sortEdges es` is a permutation of `es`. -/
theorem sortEdges_perm {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (sortEdges es).Perm es :=
  List.mergeSort_perm es _

@[simp]
theorem sortEdges_length {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (sortEdges es).length = es.length :=
  List.length_mergeSort es

/-- Over a linear order, `sortEdges es` is sorted in nondecreasing weight order. -/
theorem sortEdges_sorted {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n W)) :
    (sortEdges es).Pairwise (fun a b => a.weight ≤ b.weight) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : WeightedEdge n W => decide (a.weight ≤ b.weight))
    (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      rcases le_total a.weight b.weight with h | h <;> simp [h])
    es
  exact h.imp fun hle => of_decide_eq_true hle

/-- Kruskal's algorithm: merge-sort edges in nondecreasing weight order and scan from the discrete
partition `Partition.discrete n`, retaining each edge whose endpoints lie in distinct components. -/
@[expose] def kruskalEdges {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) : List (WeightedEdge n W) :=
  kruskalScan (Partition.discrete n) (sortEdges es)

/-- `kruskalEdges es` is sorted in nondecreasing weight order. -/
theorem kruskalEdges_sorted {n : ℕ} {W : Type} [LinearOrder W]
    (es : List (WeightedEdge n W)) :
    (kruskalEdges es).Pairwise (fun a b => a.weight ≤ b.weight) :=
  (sortEdges_sorted es).sublist (kruskalScan_sublist _ _)

/-- `kruskalEdges es` is a sub-multiset (`Subperm`) of `es`. -/
theorem kruskalEdges_subperm {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalEdges es).Subperm es :=
  (kruskalScan_sublist _ _).subperm.trans (sortEdges_perm es).subperm

/-- `kruskalEdges es` is acyclic. -/
theorem kruskalEdges_isAcyclic {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    IsAcyclic (kruskalEdges es) :=
  kruskalScan_isAcyclicFrom (Partition.discrete n) (sortEdges es)

/-- `kruskalEdges es` induces the exact same connected-component partition as `es`. -/
theorem edgePartition_kruskalEdges {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    edgePartition (kruskalEdges es) = edgePartition es :=
  (edgePartitionFrom_kruskalScan (Partition.discrete n) (sortEdges es)).trans
    (Perm.edgePartition_eq (sortEdges_perm es))

/-- `kruskalEdges es` is a spanning forest of `es`. -/
theorem kruskalEdges_isSpanningForest {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    IsSpanningForest es (kruskalEdges es) :=
  ⟨kruskalEdges_subperm es, kruskalEdges_isAcyclic es, edgePartition_kruskalEdges es⟩

/-- **Kruskal's minimum spanning forest theorem** (generalizing [Cormen et al., Section 23.2,
`MST-KRUSKAL`, p. 631][CLRS2009] from connected simple real-weighted graphs to arbitrary finite
multigraphs): for any weighted multigraph `es` on `Fin n` with weights in an ordered additive
commutative monoid, `kruskalEdges es` is a minimum-weight spanning forest of `es`. -/
theorem kruskalEdges_isMinSpanningForest {n : ℕ} {W : Type}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    (es : List (WeightedEdge n W)) :
    IsMinSpanningForest es (kruskalEdges es) := by
  refine ⟨kruskalEdges_isSpanningForest es, fun F ⟨hsub, hacyc, hpart⟩ => ?_⟩
  have hsub' : F.Subperm (sortEdges es) := hsub.trans (sortEdges_perm es).symm.subperm
  have hpart' : edgePartitionFrom (Partition.discrete n) F =
      edgePartitionFrom (Partition.discrete n) (sortEdges es) :=
    hpart.trans (Perm.edgePartition_eq (sortEdges_perm es)).symm
  exact totalWeight_kruskalScan_le (Partition.discrete n) (sortEdges_sorted es)
    ⟨hsub', hacyc, hpart'⟩

/-- **Kruskal's minimum spanning tree theorem** ([Cormen et al., Section 23.2, p. 631][CLRS2009]):
when `es` connects `Fin n` into a single component (`(edgePartition es).numComponents = 1`),
`kruskalEdges es` is a minimum-weight spanning tree of `es`. -/
theorem kruskalEdges_isMinSpanningTree {n : ℕ} {W : Type}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    {es : List (WeightedEdge n W)} (hconn : (edgePartition es).numComponents = 1) :
    IsMinSpanningTree es (kruskalEdges es) := by
  obtain ⟨hsf, hmin⟩ := kruskalEdges_isMinSpanningForest es
  refine ⟨(isSpanningTree_iff_isSpanningForest_of_connected hconn).mpr hsf, fun T hT => ?_⟩
  exact hmin T ((isSpanningTree_iff_isSpanningForest_of_connected hconn).mp hT)

/-- **Distinct-weight uniqueness of Kruskal's forest** (generalizing [Kruskal, Opening paragraph,
Construction A, and uniqueness proof, pp. 48–50][Kruskal1956]): when all edges in `es` have pairwise
distinct weights, every minimum-weight spanning forest of `es` is a permutation of `kruskalEdges es`
(i.e., selects the exact same multiset of edges). -/
theorem perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights {n : ℕ} {W : Type}
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {es F : List (WeightedEdge n W)}
    (hnodup : (es.map WeightedEdge.weight).Nodup)
    (hF : IsMinSpanningForest es F) :
    F.Perm (kruskalEdges es) := by
  obtain ⟨⟨hsub, hacyc, hpart⟩, hmin⟩ := hF
  have hsub' : F.Subperm (sortEdges es) := hsub.trans (sortEdges_perm es).symm.subperm
  have hpart' : edgePartitionFrom (Partition.discrete n) F =
      edgePartitionFrom (Partition.discrete n) (sortEdges es) :=
    hpart.trans (Perm.edgePartition_eq (sortEdges_perm es)).symm
  have hnodup' : ((sortEdges es).map WeightedEdge.weight).Nodup :=
    ((sortEdges_perm es).map WeightedEdge.weight).nodup_iff.mpr hnodup
  have hopt : totalWeight F ≤ totalWeight (kruskalEdges es) :=
    hmin (kruskalEdges es) (kruskalEdges_isSpanningForest es)
  exact perm_kruskalScan_of_totalWeight_le_of_nodup_weights (Partition.discrete n)
    (sortEdges_sorted es) hnodup' ⟨hsub', hacyc, hpart'⟩ hopt

/-- Distinct-weight uniqueness specialized to connected multigraphs: when edge weights in `es` are
pairwise distinct and `es` is connected, every minimum spanning tree of `es` is a permutation of
`kruskalEdges es`. -/
theorem perm_kruskalEdges_of_isMinSpanningTree_of_nodup_weights {n : ℕ} {W : Type}
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {es T : List (WeightedEdge n W)}
    (hconn : (edgePartition es).numComponents = 1)
    (hnodup : (es.map WeightedEdge.weight).Nodup)
    (hT : IsMinSpanningTree es T) :
    T.Perm (kruskalEdges es) := by
  refine perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights hnodup ⟨?_, ?_⟩
  · exact (isSpanningTree_iff_isSpanningForest_of_connected hconn).mp hT.1
  · intro F' hF'
    exact hT.2 F' ((isSpanningTree_iff_isSpanningForest_of_connected hconn).mpr hF')

/-! ### `DisjointSet.spec` client and backend-parametric realization -/

/-- `DisjointSet.spec n` client for the Kruskal scan, defined as the `WeightedEdge.endpoints`
specialization of `DisjointSet.spanningForestEdges`. -/
@[expose] def kruskalClient {n : ℕ} {W : Type} (es : List (WeightedEdge n W)) :
    (DisjointSet.spec n).Client (List (WeightedEdge n W)) :=
  DisjointSet.spanningForestEdges WeightedEdge.endpoints es

/-- `eval` view of `kruskalClient`. -/
@[simp]
theorem eval_kruskalClient {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    eval (DisjointSet.spec n) (kruskalClient es) p =
      (kruskalScan p es, edgePartitionFrom p es) :=
  Prod.ext (kruskalScan_eq_eval_spanningForestEdges p es).symm
    (edgePartitionFrom_eq_eval_spanningForestEdges p es).symm

/-- Exact mathematical evaluation and operation history of `kruskalClient`: it computes
`kruskalScan p es`, reaches `edgePartitionFrom p es`, and issues one `Op.union e.u e.v` per edge. -/
theorem runClient_kruskalClient {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    (DisjointSet.spec n).runClient p (kruskalClient es) =
      (kruskalScan p es, edgePartitionFrom p es, es.map fun e => DisjointSet.Op.union e.u e.v) := by
  have hev := eval_kruskalClient p es
  unfold eval at hev
  have h₁ : ((DisjointSet.spec n).runClient p (kruskalClient es)).1 = kruskalScan p es :=
    congrArg Prod.fst hev
  have h₂ : ((DisjointSet.spec n).runClient p (kruskalClient es)).2.1 = edgePartitionFrom p es :=
    congrArg Prod.snd hev
  have hhist := DisjointSet.runClient_spanningForestEdges_history WeightedEdge.endpoints es p
  exact Prod.ext h₁ (Prod.ext h₂ hhist)

/-- Projecting endpoints of `kruskalClient` matches unweighted
`DisjointSet.spanningForestEdges id`. -/
theorem kruskalScan_map_endpoints {n : ℕ} {W : Type} (p : Partition n)
    (es : List (WeightedEdge n W)) :
    (kruskalScan p es).map WeightedEdge.endpoints =
      (eval (DisjointSet.spec n)
        (DisjointSet.spanningForestEdges id (es.map WeightedEdge.endpoints)) p).1 := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    rw [kruskalScan_cons, List.map_cons, DisjointSet.eval_spanningForestEdges_cons]
    dsimp only [id_eq, WeightedEdge.endpoints_fst, WeightedEdge.endpoints_snd]
    by_cases hrel : p.rel e.u e.v = true
    · simp [hrel, Partition.merge_of_rel hrel, ih p]
    · simp [hrel, ih (p.merge e.u e.v)]

/-- Backend-parametric Kruskal execution: any `Cslib.Stateful.Realization` and
`Cslib.Stateful.Bound` for `DisjointSet.spec n` executes `kruskalClient (sortEdges es)` to produce
`kruskalEdges es` and transfers its resource bound along the `m` `Op.union` calls. -/
theorem realized_kruskal {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    {C τ : Type} {exec : Execution (DisjointSet.spec n) C τ}
    (R : Realization (DisjointSet.spec n) exec)
    {cost : τ → ℕ} {charge : Partition n → DisjointSet.Op n → ℕ}
    (B : Bound R cost charge)
    {s₀ : C} (hr : R.rep (Partition.discrete n) s₀)
    (es : List (WeightedEdge n W)) :
    ∃ s' traces,
      Executes exec (kruskalClient (sortEdges es)) s₀ (kruskalEdges es) s' traces ∧
      R.rep (edgePartition es) s' ∧
      total cost traces ≤
        (DisjointSet.spec n).totalCost charge (Partition.discrete n)
          ((sortEdges es).map fun e => DisjointSet.Op.union e.u e.v) := by
  have hv := (DisjointSet.spec n).validHistory_of_forall_valid (fun _ _ => trivial)
    (Partition.discrete n) ((DisjointSet.spec n).runClient (Partition.discrete n)
      (kruskalClient (sortEdges es))).2.2
  obtain ⟨s', traces, hexec, hrep, hcost⟩ :=
    Bound.exists_executes B (kruskalClient (sortEdges es)) hr hv
  rw [runClient_kruskalClient] at hexec hrep hcost
  refine ⟨s', traces, hexec, ?_, hcost⟩
  rwa [← edgePartition, Perm.edgePartition_eq (sortEdges_perm es)] at hrep

/-! ### `TimeM` complexity with sorting comparisons and `UnionFind` steps -/

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

/-- Two-component cost profile for Kruskal's algorithm: edge-weight comparisons during merge sort
and disjoint-set forest steps during the cycle-filtering scan. -/
@[ext]
structure Cost where
  /-- Number of edge-weight comparisons performed while sorting edges. -/
  comparisons : ℕ
  /-- Number of disjoint-set forest steps (`find` parent-pointer inspections plus `union` root
  links) performed during the Kruskal scan. -/
  ufSteps : ℕ
  deriving Repr

namespace Cost

instance instDecidableEq : DecidableEq Cost := fun a b =>
  if hc : a.comparisons = b.comparisons then
    if hu : a.ufSteps = b.ufSteps then
      isTrue (by cases a; cases b; subst hc hu; rfl)
    else
      isFalse fun h => hu (congrArg ufSteps h)
  else
    isFalse fun h => hc (congrArg comparisons h)

/-- Combined operation count `comparisons + ufSteps`. -/
@[expose] def total (c : Cost) : ℕ :=
  c.comparisons + c.ufSteps

instance : Zero Cost where
  zero := ⟨0, 0⟩

instance : Add Cost where
  add a b := ⟨a.comparisons + b.comparisons, a.ufSteps + b.ufSteps⟩

@[simp] theorem comparisons_zero : (0 : Cost).comparisons = 0 := rfl
@[simp] theorem ufSteps_zero : (0 : Cost).ufSteps = 0 := rfl
@[simp] theorem total_zero : (0 : Cost).total = 0 := rfl

@[simp]
theorem comparisons_add (a b : Cost) : (a + b).comparisons = a.comparisons + b.comparisons := rfl

@[simp]
theorem ufSteps_add (a b : Cost) : (a + b).ufSteps = a.ufSteps + b.ufSteps := rfl

@[simp]
theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [total, comparisons_add, ufSteps_add]
  omega

instance : AddCommMonoid Cost where
  add_assoc a b c := by ext <;> simp [Nat.add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp [Nat.add_comm]

end Cost

/-- Concrete output of `kruskalM`: the selected forest edges together with the final
`DisjointSet.UnionFind.State n` representing the graph's connected components. -/
structure Output (n : ℕ) (W : Type) where
  /-- Selected spanning-forest edges. -/
  forest : List (WeightedEdge n W)
  /-- Final concrete union-find forest state after scanning all edges. -/
  ufState : DisjointSet.UnionFind.State n

/-- Lift a comparison-counting `TimeM ℕ` computation into `TimeM Cost`. -/
@[expose] def liftComparisons {α : Type} (m : TimeM ℕ α) : TimeM Cost α :=
  ⟨m.ret, ⟨m.time, 0⟩⟩

@[simp]
theorem ret_liftComparisons {α : Type} (m : TimeM ℕ α) :
    (liftComparisons m).ret = m.ret := rfl

@[simp]
theorem time_liftComparisons {α : Type} (m : TimeM ℕ α) :
    (liftComparisons m).time = ⟨m.time, 0⟩ := rfl

/-- Merge-sort edges by nondecreasing weight in `TimeM ℕ`, charging `1` per weight comparison. -/
@[expose] def sortEdgesM {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) : TimeM ℕ (List (WeightedEdge n W)) :=
  List.mergeSortM es fun a b => do ✓ return decide (a.weight ≤ b.weight)

@[simp]
theorem sortEdgesM_nil {n : ℕ} {W : Type} [LE W] [DecidableLE W] :
    sortEdgesM ([] : List (WeightedEdge n W)) = pure [] := by
  simp [sortEdgesM]

@[simp]
theorem sortEdgesM_singleton {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (e : WeightedEdge n W) :
    sortEdgesM [e] = pure [e] := by
  simp [sortEdgesM]

@[simp]
theorem ret_sortEdgesM {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (sortEdgesM es).ret = sortEdges es := by
  simp [sortEdgesM, sortEdges]

/-- `sortEdgesM es` performs at most `es.length * Nat.clog 2 es.length` weight comparisons. -/
theorem time_sortEdgesM_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (sortEdgesM es).time ≤ es.length * Nat.clog 2 es.length :=
  TimeM.mergeSortM_time es _ fun _ _ => le_rfl

/-- Timed Kruskal scan starting from a concrete `DisjointSet.UnionFind.State n`, charging exact
union-find forest steps to `Cost.ufSteps`. -/
@[expose] def kruskalScanM {n : ℕ} {W : Type}
    (s : DisjointSet.UnionFind.State n) (sorted : List (WeightedEdge n W)) :
    TimeM Cost (Output n W) :=
  let res := DisjointSet.UnionFind.run s (kruskalClient sorted)
  ⟨⟨res.1, res.2.1⟩, ⟨0, total id res.2.2⟩⟩

@[simp]
theorem comparisons_kruskalScanM {n : ℕ} {W : Type}
    (s : DisjointSet.UnionFind.State n) (sorted : List (WeightedEdge n W)) :
    (kruskalScanM s sorted).time.comparisons = 0 := rfl

/-- Correctness and `O(log n)` per-edge disjoint-set step bound for `kruskalScanM`. -/
theorem kruskalScanM_correct {n : ℕ} {W : Type}
    {p : Partition n} {s : DisjointSet.UnionFind.State n}
    (hr : DisjointSet.UnionFind.Rep p s) (sorted : List (WeightedEdge n W)) :
    (kruskalScanM s sorted).ret.forest = kruskalScan p sorted ∧
      DisjointSet.UnionFind.Rep (edgePartitionFrom p sorted) (kruskalScanM s sorted).ret.ufState ∧
      (kruskalScanM s sorted).time.ufSteps ≤ sorted.length * (2 * Nat.log 2 n + 3) := by
  obtain ⟨hans, hrep, _, hunif⟩ := DisjointSet.UnionFind.run_correct (kruskalClient sorted) hr
  rw [runClient_kruskalClient] at hans hrep hunif
  rw [List.length_map] at hunif
  exact ⟨hans, hrep, hunif⟩

/-- Kruskal's minimum-spanning-forest algorithm in `TimeM Cost` ([Cormen et al., Section 23.2,
`MST-KRUSKAL`, pp. 631–633][CLRS2009]): merge-sort `es` by weight (charging comparisons to
`Cost.comparisons`) and scan the sorted edges from `DisjointSet.UnionFind.init n` (charging
post-initialization parent-pointer inspections and root links to `Cost.ufSteps`, with
`DisjointSet.UnionFind.init n` uncharged). -/
@[expose] def kruskalM {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) : TimeM Cost (Output n W) := do
  let sorted ← liftComparisons (sortEdgesM es)
  kruskalScanM (DisjointSet.UnionFind.init n) sorted

/-- Pure return value of `kruskalM es` in terms of kernel-reducible `sortEdges` and
`kruskalScanM`. -/
theorem kruskalM_ret {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).ret = (kruskalScanM (DisjointSet.UnionFind.init n) (sortEdges es)).ret := by
  simp [kruskalM]

/-- `kruskalM es` computes `kruskalEdges es`. -/
@[simp]
theorem kruskalM_forest {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).ret.forest = kruskalEdges es := by
  unfold kruskalM
  simp only [TimeM.ret_bind, ret_liftComparisons, ret_sortEdgesM]
  exact (kruskalScanM_correct (DisjointSet.UnionFind.rep_init n) (sortEdges es)).1

/-- Over an ordered additive commutative monoid, `(kruskalM es).ret.forest` is a minimum-weight
spanning forest of `es`. -/
theorem kruskalM_isMinSpanningForest {n : ℕ} {W : Type}
    [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]
    (es : List (WeightedEdge n W)) :
    IsMinSpanningForest es (kruskalM es).ret.forest := by
  rw [kruskalM_forest]
  exact kruskalEdges_isMinSpanningForest es

/-- Final union-find state invariant: `(kruskalM es).ret.ufState` represents `edgePartition es`. -/
theorem kruskalM_rep {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    DisjointSet.UnionFind.Rep (edgePartition es) (kruskalM es).ret.ufState := by
  unfold kruskalM
  simp only [TimeM.ret_bind, ret_liftComparisons, ret_sortEdgesM]
  have hrep := (kruskalScanM_correct (DisjointSet.UnionFind.rep_init n) (sortEdges es)).2.1
  rwa [← edgePartition, Perm.edgePartition_eq (sortEdges_perm es)] at hrep

/-- The maintained component counter of `(kruskalM es).ret.ufState` equals the number of connected
components `(edgePartition es).numComponents`. -/
theorem kruskalM_numComp {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).ret.ufState.numComp = (edgePartition es).numComponents :=
  (kruskalM_rep es).numComp_eq

/-- Sorting comparison bound for `kruskalM`: at most `m * ⌈log₂ m⌉` weight comparisons where
`m = es.length`. -/
theorem kruskalM_comparisons_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).time.comparisons ≤ es.length * Nat.clog 2 es.length := by
  unfold kruskalM
  simp only [TimeM.time_bind, time_liftComparisons, ret_liftComparisons, ret_sortEdgesM,
    Cost.comparisons_add, comparisons_kruskalScanM, Nat.add_zero]
  exact time_sortEdgesM_le es

/-- Disjoint-set forest step bound for `kruskalM`: at most `m * (2 * ⌊log₂ n⌋ + 3)` union-find
steps where `m = es.length`. -/
theorem kruskalM_ufSteps_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).time.ufSteps ≤ es.length * (2 * Nat.log 2 n + 3) := by
  unfold kruskalM
  simp only [TimeM.time_bind, time_liftComparisons, ret_liftComparisons, ret_sortEdgesM,
    Cost.ufSteps_add, Nat.zero_add]
  simpa only [sortEdges_length] using
    (kruskalScanM_correct (DisjointSet.UnionFind.rep_init n) (sortEdges es)).2.2

/-- Combined `O(m log m + m log n)` bound on total operations `(kruskalM es).time.total`. -/
theorem kruskalM_total_le {n : ℕ} {W : Type} [LE W] [DecidableLE W]
    (es : List (WeightedEdge n W)) :
    (kruskalM es).time.total ≤
      es.length * Nat.clog 2 es.length + es.length * (2 * Nat.log 2 n + 3) := by
  exact Nat.add_le_add (kruskalM_comparisons_le es) (kruskalM_ufSteps_le es)

end Cslib.Algorithms.Lean.Kruskal
