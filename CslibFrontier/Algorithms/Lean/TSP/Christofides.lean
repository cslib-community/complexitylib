/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Euler.Handshake
public import CslibFrontier.Algorithms.Lean.TSP.PerfectMatching

/-!
# Christofides' 3/2-approximation for metric TSP

This module formalizes Christofides' algorithm for the metric traveling salesman problem
([Christofides1976]; [WilliamsonShmoys2011], Section 2.4, Theorem 2.13):

1. compute a minimum spanning tree `T` of the complete graph (Kruskal's algorithm, `kruskalEdges`);
2. compute a minimum-weight perfect matching `M` on the vertices of odd degree in `T`
   (`oddVertices`, `minPerfectMatching`);
3. compute an Euler circuit of the multigraph `T ⊎ M` (Hierholzer's algorithm, `eulerCircuit`);
4. shortcut it to a tour visiting every vertex once (`List.dedup`).

The tour costs at most `c(T) + c(M) ≤ OPT + OPT / 2`.

## Model

Vertices are `Fin n` and `δ : Fin n → Fin n → ℕ` is an arbitrary cost function; the cost of a tour
is `cycleCost δ`, as for the minimum-spanning-tree 2-approximation `mstTour`. The approximation
bound assumes that `δ` is symmetric and satisfies the triangle inequality for all triples; diagonal
entries need not be zero. The multigraph `T ⊎ M` is the edge list
`T.map WeightedEdge.endpoints ++ M`, so an edge of `T` that `M` repeats appears twice.

## Source mapping

[WilliamsonShmoys2011], Section 2.4:

* the handshake argument before Theorem 2.13 (`O` has even cardinality) is
  `even_length_oddVertices`, from `Cslib.Algorithms.Lean.Euler.even_length_filter_odd_degree`;
* "it is connected (since the spanning tree is connected) and has even degree" is
  `shortcutTour_perm` (via `Cslib.Algorithms.Lean.Euler.isEulerCircuit_eulerCircuit`);
* shortcutting (proof of Theorem 2.12) is `cycleCost_shortcutTour_le`;
* Lemma 2.10 (the tree costs at most `OPT`) is `totalWeight_kruskalEdges_le_cycleCost`;
* the matching costs at most `OPT / 2` (proof of Theorem 2.13) is `two_mul_sum_le_cycleCost`;
* Theorem 2.13 is `two_mul_cycleCost_shortcutTour_le_three_mul` for any minimum spanning tree and
  any minimum-weight perfect matching, and `two_mul_cycleCost_christofides_le_three_mul` for the
  algorithm `christofides`.

The textbook shortcut keeps the first visit to each city; `List.dedup` keeps the last. Both are
subsequences of the Euler circuit, which is all the bound uses.

## Limitations

The matching step is exhaustive search (`minPerfectMatching`), which takes exponential time;
Edmonds' polynomial-time weighted matching algorithm ([Edmonds1965]) is not formalized. These
results prove the approximation ratio of the construction, not a polynomial running time, and
no machine-level running time is certified.

## Main definitions

* `Cslib.Algorithms.Lean.TSP.oddVertices`: the odd-degree vertices of an edge list.
* `Cslib.Algorithms.Lean.TSP.shortcutTour`: the shortcut Euler circuit of a tree and a matching.
* `Cslib.Algorithms.Lean.TSP.christofides`: Christofides' tour.

## Main results

* `even_length_oddVertices`: an edge list has an even number of odd-degree vertices.
* `shortcutTour_perm`, `christofides_perm`: the tours visit every vertex exactly once.
* `cycleCost_shortcutTour_le`: the shortcut tour costs at most the tree plus the matching.
* `numComponents_edgePartition_completeEdges`: the complete graph is connected.
* `two_mul_cycleCost_shortcutTour_le_three_mul`: for any minimum spanning tree and any
  minimum-weight perfect matching on its odd-degree vertices, the tour costs at most `3/2` times
  any tour.
* `two_mul_cycleCost_christofides_le_three_mul`: Christofides' tour costs at most `3/2` times any
  tour.

## References

* [N. Christofides, *Worst-case analysis of a new heuristic for the travelling salesman
  problem*][Christofides1976]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
* [J. Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*][Edmonds1965]
-/

public section

namespace Cslib.Algorithms.Lean.TSP

open Cslib.DataStructure Cslib.DataStructure.DisjointSet Cslib.Algorithms.Lean.Kruskal
  Cslib.Algorithms.Lean.Euler Cslib.Algorithms.Lean.VertexCover

variable {n : ℕ}

/-! ### Odd-degree vertices -/

/-- The vertices of odd degree in the multigraph of the edges of `T`, in increasing order. -/
@[expose] def oddVertices {W : Type} (T : List (WeightedEdge n W)) : List (Fin n) :=
  (List.finRange n).filter fun x => Odd (degree (T.map WeightedEdge.endpoints) x)

theorem mem_oddVertices {W : Type} {T : List (WeightedEdge n W)} {x : Fin n} :
    x ∈ oddVertices T ↔ Odd (degree (T.map WeightedEdge.endpoints) x) := by
  simp [oddVertices]

theorem nodup_oddVertices {W : Type} (T : List (WeightedEdge n W)) : (oddVertices T).Nodup :=
  (List.nodup_finRange n).filter _

theorem length_oddVertices_le {W : Type} (T : List (WeightedEdge n W)) :
    (oddVertices T).length ≤ n :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

/-- **The handshake lemma** for `T`: it has an even number of odd-degree vertices. -/
theorem even_length_oddVertices {W : Type} (T : List (WeightedEdge n W)) :
    Even (oddVertices T).length :=
  even_length_filter_odd_degree (List.nodup_finRange n) fun _ _ =>
    ⟨List.mem_finRange _, List.mem_finRange _⟩

/-! ### The algorithm -/

/-- **The shortcut Euler tour** of `T` and `M`: Hierholzer's Euler circuit of the multigraph with
the edges of `T` and of `M`, from vertex `0`, keeping only the last visit to each vertex
(`List.dedup`). -/
@[expose] def shortcutTour {W : Type} (T : List (WeightedEdge n W)) (M : List (Fin n × Fin n)) :
    List (Fin n) :=
  if h : 0 < n then (eulerCircuit (T.map WeightedEdge.endpoints ++ M) ⟨0, h⟩).dedup else []

/-- **Christofides' algorithm** ([Christofides1976]; [WilliamsonShmoys2011], Section 2.4): compute
Kruskal's minimum spanning tree `T` of the complete graph weighted by `δ`, a minimum-weight perfect
matching `M` on the vertices of odd degree in `T` (by exhaustive search, `minPerfectMatching`), and
shortcut an Euler circuit of `T` together with `M`. -/
@[expose] def christofides (δ : Fin n → Fin n → ℕ) : List (Fin n) :=
  let T := kruskalEdges (completeEdges δ)
  shortcutTour T (minPerfectMatching δ n (oddVertices T))

/-! ### Feasibility and cost of the shortcut tour -/

private theorem even_degree_append {W : Type} {T : List (WeightedEdge n W)}
    {M : List (Fin n × Fin n)} (hM : (endpoints M).Perm (oddVertices T)) (x : Fin n) :
    Even (degree (T.map WeightedEdge.endpoints ++ M) x) := by
  rw [degree_append, degree_eq_count_endpoints M, hM.count_eq, (nodup_oddVertices T).count]
  by_cases h : Odd (degree (T.map WeightedEdge.endpoints) x)
  · rw [ite_eq_left (mem_oddVertices.2 h)]
    exact h.add_one
  · rw [ite_eq_right (mt mem_oddVertices.1 h), Nat.add_zero]
    exact Nat.not_odd_iff_even.1 h

private theorem eqvGen_append {W : Type} {T : List (WeightedEdge n W)}
    (hT : ∀ a b : Fin n, Relation.EqvGen (fun x y => ∃ e ∈ T, x = e.u ∧ y = e.v) a b)
    (M : List (Fin n × Fin n)) (a b : Fin n) :
    Relation.EqvGen (fun a b => (a, b) ∈ T.map WeightedEdge.endpoints ++ M) a b :=
  Relation.EqvGen.mono (fun x y ⟨e, he, hx, hy⟩ => List.mem_append_left _
    (List.mem_map.2 ⟨e, he, by rw [hx, hy]; rfl⟩)) _ _ (hT a b)

/-- **Feasibility.** If the edges of `T` connect all vertices and `M` is a perfect matching on the
odd-degree vertices of `T`, the shortcut Euler tour visits every vertex exactly once. -/
theorem shortcutTour_perm {W : Type} {T : List (WeightedEdge n W)}
    (hT : ∀ a b : Fin n, Relation.EqvGen (fun x y => ∃ e ∈ T, x = e.u ∧ y = e.v) a b)
    {M : List (Fin n × Fin n)} (hM : (endpoints M).Perm (oddVertices T)) :
    (shortcutTour T M).Perm (List.finRange n) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [shortcutTour]
  · have hw := isEulerCircuit_eulerCircuit (u := ⟨0, h⟩) (even_degree_append hM)
      fun e _ => eqvGen_append hT M e.1 _
    rw [shortcutTour, dite_eq_left h]
    refine (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_finRange n)).2 fun x => ?_
    simp only [List.mem_dedup, List.mem_finRange, iff_true]
    exact mem_of_isEulerCircuit hw (eqvGen_append hT M x _)

/-- **The upper bound** ([WilliamsonShmoys2011], proof of Theorem 2.13): for symmetric `δ` with the
triangle inequality and at least two vertices, if the edges of `T` connect all vertices and are
weighted by `δ`, and `M` is a perfect matching on the odd-degree vertices of `T`, the shortcut
Euler tour costs at most `T` and `M` together. -/
theorem cycleCost_shortcutTour_le {δ : Fin n → Fin n → ℕ} (hsymm : ∀ x y, δ x y = δ y x)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) (hn : 2 ≤ n) {T : List (WeightedEdge n ℕ)}
    (hTw : ∀ e ∈ T, e.weight = δ e.u e.v)
    (hT : ∀ a b : Fin n, Relation.EqvGen (fun x y => ∃ e ∈ T, x = e.u ∧ y = e.v) a b)
    {M : List (Fin n × Fin n)} (hM : (endpoints M).Perm (oddVertices T)) :
    cycleCost δ (shortcutTour T M) ≤ totalWeight T + (M.map fun e => δ e.1 e.2).sum := by
  have h : 0 < n := by omega
  have hw := isEulerCircuit_eulerCircuit (u := ⟨0, h⟩) (even_degree_append hM)
    fun e _ => eqvGen_append hT M e.1 _
  have hT0 : T ≠ [] := by
    rintro rfl
    have key : ∀ a b : Fin n,
        Relation.EqvGen (fun x y => ∃ e ∈ ([] : List (WeightedEdge n ℕ)), x = e.u ∧ y = e.v)
          a b → a = b := by
      intro a b hab
      induction hab with
      | rel _ _ h => simp at h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact absurd (key _ _ (hT ⟨0, h⟩ ⟨1, hn⟩)) (by simp [Fin.ext_iff])
  have hH : T.map WeightedEdge.endpoints ++ M ≠ [] := by simp [hT0]
  rw [shortcutTour, dite_eq_left h]
  refine (cycleCost_dedup_le_of_isEulerCircuit htri hsymm hw hH).trans (le_of_eq ?_)
  have hTsum : ((T.map WeightedEdge.endpoints).map fun e => δ e.1 e.2).sum = totalWeight T := by
    rw [totalWeight, List.map_map]
    congr 1
    exact List.map_congr_left fun e he => (hTw e he).symm
  simp only [List.map_append, List.sum_append, hTsum]

/-! ### Christofides' bound -/

private theorem eq_of_perm_of_length_le_one {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂)
    (hl : l₂.length ≤ 1) : l₁ = l₂ := by
  match l₂, h, hl with
  | [], h, _ => exact h.eq_nil
  | [_], h, _ => exact List.perm_singleton.1 h
  | _ :: _ :: _, _, hl => simp at hl

/-- With at most one vertex there is only one tour. -/
private theorem eq_of_perm_finRange {l₁ q : List (Fin n)} (hn : n < 2)
    (h : l₁.Perm (List.finRange n)) (hq : q.Nodup) (hcov : ∀ x, x ∈ q) : l₁ = q := by
  have hperm : q.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup hq (List.nodup_finRange n)).2 (by simp [hcov])
  rw [eq_of_perm_of_length_le_one h (by simp; omega),
    eq_of_perm_of_length_le_one hperm (by simp; omega)]

private theorem rel_eq_true_of_numComponents_eq_one {p : Partition n} (hp : p.numComponents = 1)
    (x y : Fin n) : p.rel x y = true := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hp
  have hx : p.classOf x = c := Finset.mem_singleton.mp (hc ▸ p.classOf_mem_components x)
  have hy : p.classOf y = c := Finset.mem_singleton.mp (hc ▸ p.classOf_mem_components y)
  exact Partition.classOf_eq_iff.mp (hx.trans hy.symm)

/-- The complete graph on at least one vertex is connected. -/
theorem numComponents_edgePartition_completeEdges (δ : Fin n → Fin n → ℕ) (hn : 0 < n) :
    (edgePartition (completeEdges δ)).numComponents = 1 := by
  set p := edgePartition (completeEdges δ)
  have hrel : ∀ x y : Fin n, p.rel x y = true := fun x y =>
    (rel_edgePartition_iff_eqvGen _ x y).2
      (.rel _ _ ⟨⟨x, y, δ x y⟩, mem_completeEdges.2 rfl, rfl, rfl⟩)
  have hcomp : p.components = {p.classOf ⟨0, hn⟩} := by
    ext c
    simp only [Partition.mem_components, Finset.mem_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      exact Partition.classOf_eq_iff.mpr (hrel x _)
    · rintro rfl
      exact ⟨_, rfl⟩
  unfold Partition.numComponents
  rw [hcomp, Finset.card_singleton]

/-- **Feasibility.** Christofides' tour visits every vertex exactly once. -/
theorem christofides_perm (δ : Fin n → Fin n → ℕ) : (christofides δ).Perm (List.finRange n) :=
  shortcutTour_perm (eqvGen_kruskalEdges_completeEdges δ) (endpoints_minPerfectMatching_perm δ
    (by have := length_oddVertices_le (kruskalEdges (completeEdges δ)); omega)
    (even_length_oddVertices _))

/-- **Christofides' bound for any minimum spanning tree and any minimum-weight perfect matching**
([Christofides1976]; [WilliamsonShmoys2011], Theorem 2.13): for symmetric `δ` with the triangle
inequality, let `T` be a minimum spanning tree of the complete graph weighted by `δ` and `M` a
minimum-weight perfect matching on the odd-degree vertices of `T`. Then the shortcut Euler tour of
`T` and `M` costs at most `3/2` times any closed walk visiting every vertex exactly once, in
particular an optimal tour. -/
theorem two_mul_cycleCost_shortcutTour_le_three_mul {δ : Fin n → Fin n → ℕ}
    (hsymm : ∀ x y, δ x y = δ y x) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {T : List (WeightedEdge n ℕ)} (hT : IsMinSpanningTree (completeEdges δ) T)
    {M : List (Fin n × Fin n)} (hM : (endpoints M).Perm (oddVertices T))
    (hmin : ∀ M' : List (Fin n × Fin n), (endpoints M').Perm (oddVertices T) →
      (M.map fun e => δ e.1 e.2).sum ≤ (M'.map fun e => δ e.1 e.2).sum)
    {q : List (Fin n)} (hq : q.Nodup) (hcov : ∀ x, x ∈ q) :
    2 * cycleCost δ (shortcutTour T M) ≤ 3 * cycleCost δ q := by
  obtain ⟨⟨hsub, -, hcomp⟩, hTmin⟩ := hT
  have hTw : ∀ e ∈ T, e.weight = δ e.u e.v := fun e he => mem_completeEdges.1 (hsub.subset he)
  have hconn : ∀ a b : Fin n, Relation.EqvGen (fun x y => ∃ e ∈ T, x = e.u ∧ y = e.v) a b :=
    fun a b =>
      (rel_edgePartition_iff_eqvGen T a b).1 (rel_eq_true_of_numComponents_eq_one hcomp a b)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [eq_of_perm_finRange hn (shortcutTour_perm hconn hM) hq hcov]
    omega
  · have h1 := cycleCost_shortcutTour_le hsymm htri hn hTw hconn hM
    have h2 : totalWeight T ≤ cycleCost δ q :=
      (hTmin _ (kruskalEdges_isMinSpanningTree
        (numComponents_edgePartition_completeEdges δ (by omega))).1).trans
        (totalWeight_kruskalEdges_le_cycleCost δ hq hcov)
    have h3 := two_mul_sum_le_cycleCost htri (nodup_oddVertices T) hM hmin hq fun x _ => hcov x
    omega

/-- **Christofides' `3/2`-approximation for metric TSP** ([Christofides1976];
[WilliamsonShmoys2011], Theorem 2.13): for symmetric `δ` with the triangle inequality,
Christofides' tour costs at most `3/2` times any closed walk visiting every vertex exactly once, in
particular an optimal tour. The matching step is exhaustive search, so this certifies the
approximation ratio, not a polynomial running time. -/
theorem two_mul_cycleCost_christofides_le_three_mul {δ : Fin n → Fin n → ℕ}
    (hsymm : ∀ x y, δ x y = δ y x) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) {q : List (Fin n)}
    (hq : q.Nodup) (hcov : ∀ x, x ∈ q) :
    2 * cycleCost δ (christofides δ) ≤ 3 * cycleCost δ q := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [christofides, shortcutTour, cycleCost]
  · have hk : (oddVertices (kruskalEdges (completeEdges δ))).length ≤ 2 * n := by
      have := length_oddVertices_le (kruskalEdges (completeEdges δ))
      omega
    exact two_mul_cycleCost_shortcutTour_le_three_mul hsymm htri
      (kruskalEdges_isMinSpanningTree (numComponents_edgePartition_completeEdges δ h))
      (endpoints_minPerfectMatching_perm δ hk (even_length_oddVertices _))
      (fun M' hM' => sum_minPerfectMatching_le hsymm hk hM') hq hcov

end Cslib.Algorithms.Lean.TSP
