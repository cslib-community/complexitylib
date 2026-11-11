/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SteinerTree.Metric
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Steiner tree in graphs: the metric completion and the Kou–Markowsky–Berman heuristic

This module carries the MST 2-approximation of `CslibFrontier.Algorithms.Lean.SteinerTree.Metric`
over to Steiner tree in an edge-weighted graph, whose costs need not satisfy the triangle
inequality ([WilliamsonShmoys2011], Exercise 2.5(b)). The algorithm computes a minimum spanning
tree on the terminals under shortest-path distances (the *metric completion*), and then replaces
each tree edge by the edges of a shortest walk. This is steps 1–3 of the heuristic of Kou, Markowsky
and Berman [KouMarkowskyBerman1981].

## Model

* The graph is a Mathlib `SimpleGraph V` with edge weights `w : Sym2 V → ℕ`. The cost of a walk is
  `walkWeight w p`, the sum of the weights of its edges with multiplicity.
* A solution is a finite edge set `F : Finset (Sym2 V)` of edges of `G` whose spanning subgraph
  `SimpleGraph.fromEdgeSet F` connects every two terminals (`IsSteinerSubgraph`). Its cost is
  `F.sum w`. Weights are nonnegative, so a cheapest such `F` may be taken to be a tree.
* `graphSteinerOpt w G R` is the least cost of a Steiner subgraph. It is `0` when there is no
  Steiner subgraph. With a shortest-walk oracle there always is one (`isSteinerSubgraph_kmbEdges`).
* Shortest walks are given by an oracle `P : ∀ u v, G.Walk u v` with no walk cheaper than
  `P u v` (`IsShortestWalkOracle`). Any shortest-path algorithm can supply it. Every preconnected
  graph has an oracle (`exists_isShortestWalkOracle`). Conversely, the walks `P u v` themselves
  show that `G` is preconnected. The oracle's costs are the metric completion
  `metricCompletion w G` (`IsShortestWalkOracle.walkWeight_eq`).
* `kmbEdges w P R` runs `steinerMST` on the costs `walkWeight w (P u v)` and returns the set of
  edges of the walks `P u v` along the tree edges.
* The bounds assume duplicate-free terminals (`R.Nodup`), because they are derived from the metric
  theorems of `CslibFrontier.Algorithms.Lean.SteinerTree.Metric`. There, `Nodup` is needed only for
  costs with a nonzero diagonal. Oracle costs have a zero diagonal (`walkWeight w (P x x) ≤
  walkWeight w Walk.nil = 0`), so repeated terminals do not change the weight of the minimum
  spanning tree. Dropping the hypothesis would need a zero-diagonal variant of the metric theorem,
  which is not proved here.

## Source mapping

* [WilliamsonShmoys2011], Exercise 2.5(b): for a connected graph, running the MST algorithm in the
  metric completion and adding the edges of a shortest path for each tree edge is a
  2-approximation. The Lean statements are `isSteinerSubgraph_kmbEdges` and
  `sum_kmbEdges_le_two_mul_graphSteinerOpt`. The exercise's output is a tree. Ours is the connected
  edge set before cycles are removed, and any spanning tree of it is no more expensive. That
  reduction is not formalized here.
* [KouMarkowskyBerman1981], steps 1–3 (shortest-path distance graph on the terminals, its minimum
  spanning tree, replacement by shortest paths) are `kmbEdges`. Steps 4–5 (a minimum spanning
  tree of the result, then pruning non-terminal leaves) only lower the cost and are not formalized.
  The sharper factor `2 (1 - 1/|R|)` is `length_mul_sum_kmbEdges_le`. The paper's `2 (1 - 1/ℓ)`,
  with `ℓ` the number of leaves of an optimal tree, is not formalized. The paper's
  `O(|S| |V|²)` running time is not formalized either. (The locators for
  [KouMarkowskyBerman1981] come from its abstract, not from its body.)

## Main definitions

* `walkWeight`, `metricCompletion`: walk costs and shortest-path distances.
* `IsShortestWalkOracle`: a choice of shortest walks.
* `IsSteinerSubgraph`, `graphSteinerOpt`: the graph Steiner tree problem.
* `expandEdges`, `kmbEdges`: replacing pairs by shortest walks, and the heuristic.

## Main results

* `exists_isShortestWalkOracle`, `IsShortestWalkOracle.walkWeight_eq`: shortest-walk oracles exist
  on preconnected graphs and compute the metric completion.
* `IsShortestWalkOracle.symm`, `IsShortestWalkOracle.triangle`: the metric completion is
  symmetric and satisfies the triangle inequality.
* `isSteinerSubgraph_kmbEdges`: the heuristic returns a Steiner subgraph.
* `length_mul_sum_kmbEdges_le`: `|R| · cost(kmbEdges) ≤ 2 (|R| - 1) · cost(F)` for every Steiner
  subgraph `F`.
* `sum_kmbEdges_le_two_mul_graphSteinerOpt`: `cost(kmbEdges) ≤ 2 · OPT`.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Exercise 2.5(b).
* [L. Kou, G. Markowsky and L. Berman, *A fast algorithm for Steiner trees*][KouMarkowskyBerman1981]
-/

public section

namespace Cslib.Algorithms.Lean.SteinerTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Walk costs and the metric completion -/

/-- The cost of a walk: the sum of the weights of its edges, with multiplicity. -/
@[expose] def walkWeight (w : Sym2 V → ℕ) {u v : V} (p : G.Walk u v) : ℕ :=
  (p.edges.map w).sum

variable (w : Sym2 V → ℕ)

@[simp] theorem walkWeight_nil {u : V} : walkWeight w (Walk.nil : G.Walk u u) = 0 := rfl

theorem walkWeight_reverse {u v : V} (p : G.Walk u v) :
    walkWeight w p.reverse = walkWeight w p := by
  simp only [walkWeight, Walk.edges_reverse, List.map_reverse, List.sum_reverse]

theorem walkWeight_append {u v x : V} (p : G.Walk u v) (q : G.Walk v x) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
  simp only [walkWeight, Walk.edges_append, List.map_append, List.sum_append]

theorem walkWeight_cons_nil {u v : V} (h : G.Adj u v) :
    walkWeight w (Walk.cons h Walk.nil) = w s(u, v) := by
  simp [walkWeight]

/-- The **metric completion** of `G`: the least cost of a walk from `u` to `v`. It is `0` when
there is no such walk. -/
noncomputable def metricCompletion (G : SimpleGraph V) (u v : V) : ℕ :=
  sInf {c | ∃ p : G.Walk u v, walkWeight w p = c}

/-- `P` chooses a shortest walk between every two vertices. -/
def IsShortestWalkOracle (G : SimpleGraph V) (P : ∀ u v : V, G.Walk u v) : Prop :=
  ∀ u v (p : G.Walk u v), walkWeight w (P u v) ≤ walkWeight w p

/-- A preconnected graph has a shortest-walk oracle. -/
theorem exists_isShortestWalkOracle (hG : G.Preconnected) :
    ∃ P, IsShortestWalkOracle w G P := by
  have h : ∀ u v : V, ∃ p : G.Walk u v, walkWeight w p = metricCompletion w G u v := fun u v =>
    Nat.sInf_mem (s := {c | ∃ p : G.Walk u v, walkWeight w p = c}) ⟨_, (hG u v).some, rfl⟩
  refine ⟨fun u v => (h u v).choose, fun u v p => ?_⟩
  rw [(h u v).choose_spec]
  exact Nat.sInf_le ⟨p, rfl⟩

variable {w}

/-- A shortest-walk oracle computes the metric completion. -/
theorem IsShortestWalkOracle.walkWeight_eq {P : ∀ u v : V, G.Walk u v}
    (hP : IsShortestWalkOracle w G P) (u v : V) :
    walkWeight w (P u v) = metricCompletion w G u v :=
  le_antisymm (by
      obtain ⟨p, hp⟩ := Nat.sInf_mem (s := {c | ∃ p : G.Walk u v, walkWeight w p = c})
        ⟨_, P u v, rfl⟩
      exact (hP u v p).trans_eq hp)
    (Nat.sInf_le ⟨P u v, rfl⟩)

theorem IsShortestWalkOracle.symm {P : ∀ u v : V, G.Walk u v}
    (hP : IsShortestWalkOracle w G P) (u v : V) :
    walkWeight w (P u v) = walkWeight w (P v u) :=
  le_antisymm ((hP u v _).trans_eq (walkWeight_reverse w (P v u)))
    ((hP v u _).trans_eq (walkWeight_reverse w (P u v)))

theorem IsShortestWalkOracle.triangle {P : ∀ u v : V, G.Walk u v}
    (hP : IsShortestWalkOracle w G P) (x y z : V) :
    walkWeight w (P x z) ≤ walkWeight w (P x y) + walkWeight w (P y z) :=
  (hP x z _).trans_eq (walkWeight_append w (P x y) (P y z))

theorem IsShortestWalkOracle.le_of_adj {P : ∀ u v : V, G.Walk u v}
    (hP : IsShortestWalkOracle w G P) {u v : V} (h : G.Adj u v) :
    walkWeight w (P u v) ≤ w s(u, v) :=
  (hP u v _).trans_eq (walkWeight_cons_nil w h)

/-! ### The problem -/

/-- `F` is a set of edges of `G` whose spanning subgraph connects every two terminals. -/
@[expose] def IsSteinerSubgraph (G : SimpleGraph V) (R : List V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧
    ∀ a ∈ R, ∀ b ∈ R, (fromEdgeSet (↑F : Set (Sym2 V))).Reachable a b

/-- The optimum graph Steiner cost: the least weight of a Steiner subgraph (`0` if there is
none). -/
noncomputable def graphSteinerOpt (w : Sym2 V → ℕ) (G : SimpleGraph V) (R : List V) : ℕ :=
  sInf {c | ∃ F, IsSteinerSubgraph G R F ∧ F.sum w = c}

theorem graphSteinerOpt_le {R : List V} {F : Finset (Sym2 V)} (hF : IsSteinerSubgraph G R F) :
    graphSteinerOpt w G R ≤ F.sum w :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-! ### Expanding pairs into walks -/

variable [DecidableEq V]

/-- The edges of the walks `P u v` for the pairs `(u, v)` of `T`. -/
@[expose] def expandEdges (P : ∀ u v : V, G.Walk u v) (T : List (V × V)) : Finset (Sym2 V) :=
  (T.flatMap fun e => (P e.1 e.2).edges).toFinset

theorem expandEdges_subset (P : ∀ u v : V, G.Walk u v) (T : List (V × V)) :
    (↑(expandEdges P T) : Set (Sym2 V)) ⊆ G.edgeSet := by
  intro e he
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 he)
  exact (P x.1 x.2).edges_subset_edgeSet hx

/-- Pairs related by `T` are connected through the expanded edges. -/
theorem reachable_expandEdges (P : ∀ u v : V, G.Walk u v) {T : List (V × V)} {a b : V}
    (h : Relation.EqvGen (fun x y => (x, y) ∈ T) a b) :
    (fromEdgeSet (↑(expandEdges P T) : Set (Sym2 V))).Reachable a b := by
  induction h with
  | rel x y hxy =>
    refine ⟨(P x y).transfer _ fun e he => ?_⟩
    rw [edgeSet_fromEdgeSet]
    refine ⟨List.mem_toFinset.2 (List.mem_flatMap.2 ⟨(x, y), hxy, he⟩), ?_⟩
    exact G.not_isDiag_of_mem_edgeSet ((P x y).edges_subset_edgeSet he)
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The expanded edges cost at most the walks: shared edges are paid for once. -/
theorem sum_expandEdges_le (P : ∀ u v : V, G.Walk u v) (T : List (V × V)) :
    (expandEdges P T).sum w ≤ edgeCost (fun u v => walkWeight w (P u v)) T := by
  have hL : ∀ T : List (V × V), ((T.flatMap fun e => (P e.1 e.2).edges).map w).sum =
      edgeCost (fun u v => walkWeight w (P u v)) T := by
    intro T
    induction T with
    | nil => rfl
    | cons e T ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
      rfl
  unfold expandEdges
  rw [← hL, ← List.toFinset_dedup, List.sum_toFinset _ (List.nodup_dedup _)]
  exact List.Sublist.sum_le_sum ((List.dedup_sublist _).map w) fun _ _ => Nat.zero_le _

/-! ### From edge sets to pair lists -/

omit [DecidableEq V] in
/-- An edge set connects the vertices that its list of representative pairs connects. -/
private theorem eqvGen_of_reachable {F : Finset (Sym2 V)} {a b : V}
    (h : (fromEdgeSet (↑F : Set (Sym2 V))).Reachable a b) :
    Relation.EqvGen (fun x y => (x, y) ∈ F.toList.map Quot.out) a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons x y z hxy _ ih =>
    refine .trans _ _ _ ?_ ih
    have hmem : s(x, y) ∈ F := ((fromEdgeSet_adj _).1 hxy).1
    obtain ⟨o, ho, hq⟩ : ∃ o : V × V, o ∈ F.toList.map Quot.out ∧ s(o.1, o.2) = s(x, y) :=
      ⟨_, List.mem_map_of_mem (Finset.mem_toList.2 hmem), Sym2.mk_fst_out_snd_out _⟩
    obtain ⟨a, b⟩ := o
    rcases Sym2.eq_iff.1 hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .rel _ _ ho
    · exact .symm _ _ (.rel _ _ ho)

omit [DecidableEq V] in
/-- Under shortest-walk costs, the representative pairs of a set of edges of `G` cost at most the
edges. -/
private theorem edgeCost_out_le {P : ∀ u v : V, G.Walk u v} (hP : IsShortestWalkOracle w G P)
    {F : Finset (Sym2 V)} (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) :
    edgeCost (fun u v => walkWeight w (P u v)) (F.toList.map Quot.out) ≤ F.sum w := by
  unfold edgeCost
  rw [List.map_map, ← Finset.sum_map_toList F w]
  refine List.sum_le_sum fun e he => ?_
  have hq := Sym2.mk_fst_out_snd_out e
  have hadj : G.Adj (Quot.out e).1 (Quot.out e).2 := by
    rw [← mem_edgeSet, hq]
    exact hF (Finset.mem_toList.1 he)
  have := hP.le_of_adj hadj
  rw [hq] at this
  exact this

/-! ### The Kou–Markowsky–Berman heuristic -/

/-- **The Kou–Markowsky–Berman heuristic**, steps 1–3: the MST heuristic on the terminals under
the shortest-walk costs of `P`, with each tree edge replaced by the edges of its shortest walk. -/
@[expose] def kmbEdges (w : Sym2 V → ℕ) (P : ∀ u v : V, G.Walk u v) (R : List V) :
    Finset (Sym2 V) :=
  expandEdges P (steinerMST (fun u v => walkWeight w (P u v)) R)

/-- For a shortest-walk oracle, the tree in `kmbEdges` is the MST heuristic in the metric
completion. -/
theorem kmbEdges_eq {P : ∀ u v : V, G.Walk u v} (hP : IsShortestWalkOracle w G P) (R : List V) :
    kmbEdges w P R = expandEdges P (steinerMST (metricCompletion w G) R) := by
  unfold kmbEdges
  congr 2
  funext u v
  exact hP.walkWeight_eq u v

/-- The heuristic returns a Steiner subgraph. -/
theorem isSteinerSubgraph_kmbEdges (P : ∀ u v : V, G.Walk u v) (R : List V) :
    IsSteinerSubgraph G R (kmbEdges w P R) :=
  ⟨expandEdges_subset P _, fun a ha b hb =>
    reachable_expandEdges P (connects_steinerMST _ R a ha b hb)⟩

/-- **The Kou–Markowsky–Berman heuristic, sharp form**: for a shortest-walk oracle and
duplicate-free terminals `R`, `|R| · cost(kmbEdges) ≤ 2 (|R| - 1) · cost(F)` for every Steiner
subgraph `F`. This is the factor `2 (1 - 1/|R|)`, a restricted form of [KouMarkowskyBerman1981]'s
`2 (1 - 1/ℓ)` with `ℓ` the number of leaves of an optimal tree. -/
theorem length_mul_sum_kmbEdges_le {P : ∀ u v : V, G.Walk u v} (hP : IsShortestWalkOracle w G P)
    {R : List V} (hR : R.Nodup) {F : Finset (Sym2 V)} (hF : IsSteinerSubgraph G R F) :
    R.length * (kmbEdges w P R).sum w ≤ 2 * (R.length - 1) * F.sum w := by
  set δ : V → V → ℕ := fun u v => walkWeight w (P u v)
  have hconn : Connects (F.toList.map Quot.out) R := fun a ha b hb =>
    eqvGen_of_reachable (hF.2 a ha b hb)
  calc R.length * (kmbEdges w P R).sum w
      ≤ R.length * edgeCost δ (steinerMST δ R) :=
        Nat.mul_le_mul_left _ (sum_expandEdges_le P _)
    _ ≤ 2 * (R.length - 1) * edgeCost δ (F.toList.map Quot.out) :=
        length_mul_edgeCost_steinerMST_le hP.symm hP.triangle hR hconn
    _ ≤ 2 * (R.length - 1) * F.sum w := Nat.mul_le_mul_left _ (edgeCost_out_le hP hF.1)

/-- The heuristic costs at most twice any Steiner subgraph. -/
theorem sum_kmbEdges_le_two_mul {P : ∀ u v : V, G.Walk u v} (hP : IsShortestWalkOracle w G P)
    {R : List V} (hR : R.Nodup) {F : Finset (Sym2 V)} (hF : IsSteinerSubgraph G R F) :
    (kmbEdges w P R).sum w ≤ 2 * F.sum w := by
  set δ : V → V → ℕ := fun u v => walkWeight w (P u v)
  have hconn : Connects (F.toList.map Quot.out) R := fun a ha b hb =>
    eqvGen_of_reachable (hF.2 a ha b hb)
  calc (kmbEdges w P R).sum w ≤ edgeCost δ (steinerMST δ R) := sum_expandEdges_le P _
    _ ≤ 2 * edgeCost δ (F.toList.map Quot.out) :=
        edgeCost_steinerMST_le_two_mul hP.symm hP.triangle hR hconn
    _ ≤ 2 * F.sum w := Nat.mul_le_mul_left _ (edgeCost_out_le hP hF.1)

omit [DecidableEq V] in
/-- If `G` has walks between all pairs of vertices, the optimum is attained. -/
theorem exists_isSteinerSubgraph_sum_eq_graphSteinerOpt (P : ∀ u v : V, G.Walk u v)
    (R : List V) : ∃ F, IsSteinerSubgraph G R F ∧ F.sum w = graphSteinerOpt w G R := by
  classical
  exact Nat.sInf_mem (s := {c | ∃ F, IsSteinerSubgraph G R F ∧ F.sum w = c})
    ⟨_, _, isSteinerSubgraph_kmbEdges (w := w) P R, rfl⟩

/-- **The metric-completion MST 2-approximation for Steiner tree in graphs**
([WilliamsonShmoys2011], Exercise 2.5(b)): `cost(kmbEdges) ≤ 2 · OPT`. -/
theorem sum_kmbEdges_le_two_mul_graphSteinerOpt {P : ∀ u v : V, G.Walk u v}
    (hP : IsShortestWalkOracle w G P) {R : List V} (hR : R.Nodup) :
    (kmbEdges w P R).sum w ≤ 2 * graphSteinerOpt w G R := by
  obtain ⟨F, hF, hc⟩ := exists_isSteinerSubgraph_sum_eq_graphSteinerOpt (w := w) P R
  rw [← hc]
  exact sum_kmbEdges_le_two_mul hP hR hF

end Cslib.Algorithms.Lean.SteinerTree
