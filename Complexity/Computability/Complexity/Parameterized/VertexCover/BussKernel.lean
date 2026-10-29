/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.VertexCover
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD

/-!
# Buss's kernel for vertex cover

Vertex cover, parameterized by the target size `k`, has a kernel with at most `k (k + 2)` vertices
[BussGoldsmith1993] [DowneyFellows1999] [FlumGrohe2006, Section 9.1]
[CyganEtAl2015, Section 2.2.1]. Degrees are counted among the distinct declared vertices
(`Cslib.Complexity.VertexCover.Buss.degree`), and `k` is capped at the number `n` of distinct
declared vertices (`Cslib.Complexity.VertexCover.cap`), which leaves the rules below unchanged.

1. A vertex of degree greater than `k` belongs to every cover of at most `k` vertices
   (`Cslib.Complexity.VertexCover.Buss.mem_of_isHigh`). If there are more than `k` such *high*
   vertices, there is no such cover; otherwise they are removed and the target is decreased by
   their number `h`.
2. Every remaining vertex has degree at most `k`, so a cover of at most `k` vertices leaves at most
   `k (k + 1)` remaining vertices with a remaining neighbour, the *active* vertices
   (`Cslib.Complexity.VertexCover.Buss.length_active_le`). With more active vertices there is no
   such cover.
3. Otherwise the kernel renames the `m` active vertices to `0, …, m - 1` and keeps the edges
   between them, so that its encoded length depends only on `k`, not on the vertex labels of the
   input. Since `VertexCover` asks for a cover of *exactly* the target size among the declared
   vertices (`Cslib.Complexity.mem_VertexCover_iff_exists_card_le`), isolated vertices are kept
   as padding: `min i (k - h)` of them, where `i` is the number of remaining isolated vertices.
   With this padding the kernel target `k - h` fits in the kernel exactly when `k ≤ n`.

The rejected instances, and those with `k > n`, are mapped to a fixed instance outside
`VertexCover` (`Cslib.Complexity.VertexCover.Buss.noInstance`). The output has encoded length at
most `40 (k + 1) ^ 6`: up to `k (k + 2)` vertices and `(k (k + 1)) ^ 2` listed edges, with labels
bounded crudely by their values. The kernel is computed in polynomial time from the encoded
instance, with degrees and the capped target in unary.

## Main definitions

* `Cslib.Complexity.VertexCover.bussKernel`: Buss's kernel.
* `Cslib.Complexity.VertexCover.Buss.high`, `Cslib.Complexity.VertexCover.Buss.active`: the high
  vertices and the remaining non-isolated vertices.

## Main results

* `Cslib.Complexity.VertexCover.Buss.mem_of_isHigh`: the high-degree rule.
* `Cslib.Complexity.VertexCover.bussKernel_mem_iff`: the kernel preserves membership.
* `Cslib.Complexity.VertexCover.length_bussKernel_vertices_le`,
  `Cslib.Complexity.VertexCover.length_encode_bussKernel_le`: at most `k (k + 2)` vertices and
  encoded length at most `40 (k + 1) ^ 6`.
* `Cslib.Complexity.VertexCover.computableInPolyTime_bussKernel`: the kernel is
  polynomial-time.
* `Cslib.Complexity.VertexCover.isKernelization_bussKernel`,
  `Cslib.Complexity.VertexCover_hasPolyKernel`: `VertexCover` has a polynomial kernel in the
  target size `k`.

## References

* [J. F. Buss, J. Goldsmith, *Nondeterminism within P*][BussGoldsmith1993]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace VertexCover.Buss

/-- The number of distinct declared vertices of `G` adjacent to `v`. -/
def degree (G : Graph) (v : ℕ) : ℕ :=
  G.distinctVertices.countP (G.adjBool v)

/-- A declared vertex is *high* when its degree exceeds the capped target `cap x = min n k`. -/
def isHigh (x : Graph × ℕ) (v : ℕ) : Bool :=
  decide (cap x < degree x.1 v)

/-- The distinct declared vertices of degree greater than `min n k`. -/
def high (x : Graph × ℕ) : List ℕ :=
  x.1.distinctVertices.filter (isHigh x)

/-- The distinct declared vertices of degree at most `min n k`. -/
def low (x : Graph × ℕ) : List ℕ :=
  x.1.distinctVertices.filter fun v => !isHigh x v

/-- Whether `v` has a neighbour among the low vertices. -/
def isActive (x : Graph × ℕ) (v : ℕ) : Bool :=
  (low x).any (x.1.adjBool v)

/-- The low vertices with a low neighbour: the non-isolated vertices once the high vertices are
removed. -/
def active (x : Graph × ℕ) : List ℕ :=
  (low x).filter (isActive x)

/-- The target of the kernel: the capped target minus the number of high vertices. -/
def param (x : Graph × ℕ) : ℕ :=
  cap x - (high x).length

/-- The number of vertices of the kernel: the active vertices, padded by isolated vertices up to
the number of low vertices but by no more than `param x`. -/
def numVertices (x : Graph × ℕ) : ℕ :=
  min (low x).length ((active x).length + param x)

/-- The edges of the kernel: the active vertices are renamed to their positions in `active x`. -/
def edges (x : Graph × ℕ) : List (ℕ × ℕ) :=
  (List.range (active x).length).flatMap fun i =>
    ((List.range (active x).length).filter fun j =>
      x.1.adjBool ((active x).getD i 0) ((active x).getD j 0)).map fun j => (i, j)

/-- The graph of the kernel, on the vertices `0, …, numVertices x - 1`. -/
def graph (x : Graph × ℕ) : Graph :=
  (List.range (numVertices x), edges x)

/-- Whether the kernel is the reduced graph: the target is at most the number of distinct declared
vertices, there are at most `k` high vertices, and at most `k (k + 1)` active vertices. -/
def accept (x : Graph × ℕ) : Bool :=
  decide (cap x = x.2) && decide ((high x).length ≤ cap x) &&
    decide ((active x).length ≤ cap x * (cap x + 1))

/-- A fixed instance outside `VertexCover`: one cover vertex in the empty graph. -/
def noInstance : Graph × ℕ := (([], []), 1)

/-! ### Correctness -/

theorem noInstance_notMem : noInstance ∉ VertexCover := by
  rw [noInstance, mem_VertexCover_iff_exists_card_le]
  simp

/-- The neighbours of `v` among the distinct declared vertices. -/
private def neighbors (G : Graph) (v : ℕ) : Finset ℕ :=
  (G.distinctVertices.filter (G.adjBool v)).toFinset

private theorem mem_neighbors {G : Graph} {u v : ℕ} :
    u ∈ neighbors G v ↔ u ∈ G.1 ∧ G.toSimpleGraph.Adj v u := by
  simp [neighbors, Graph.mem_distinctVertices]

private theorem card_neighbors (G : Graph) (v : ℕ) : (neighbors G v).card = degree G v := by
  rw [neighbors, List.toFinset_card_of_nodup ((Graph.nodup_distinctVertices G).filter _), degree,
    List.countP_eq_length_filter]

private theorem degree_le_card (G : Graph) (v : ℕ) : degree G v ≤ G.1.toFinset.card :=
  (List.countP_le_length).trans (Graph.length_distinctVertices G).le

variable (x : Graph × ℕ)

private theorem mem_high {v : ℕ} : v ∈ high x ↔ v ∈ x.1.1 ∧ isHigh x v = true := by
  simp [high, Graph.mem_distinctVertices]

private theorem mem_low {v : ℕ} : v ∈ low x ↔ v ∈ x.1.1 ∧ isHigh x v = false := by
  simp [low, Graph.mem_distinctVertices]

private theorem mem_active {v : ℕ} :
    v ∈ active x ↔ v ∈ low x ∧ ∃ u ∈ low x, x.1.toSimpleGraph.Adj v u := by
  simp [active, isActive]

private theorem nodup_high : (high x).Nodup := (Graph.nodup_distinctVertices _).filter _

private theorem nodup_low : (low x).Nodup := (Graph.nodup_distinctVertices _).filter _

private theorem nodup_active : (active x).Nodup := (nodup_low x).filter _

private theorem length_active_le_length_low : (active x).length ≤ (low x).length :=
  List.length_filter_le _ _

private theorem length_high_add_length_low :
    (high x).length + (low x).length = x.1.1.toFinset.card := by
  rw [← Graph.length_distinctVertices]
  exact (List.length_eq_length_filter_add _).symm

private theorem length_active_le_numVertices : (active x).length ≤ numVertices x :=
  le_min (length_active_le_length_low x) (Nat.le_add_right _ _)

variable {x}

/-- **The high-degree rule** [CyganEtAl2015, Section 2.2.1]: a vertex of degree greater than `k`
belongs to every vertex cover of at most `k` vertices. -/
theorem mem_of_isHigh {S : Finset ℕ}
    (hS : ∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S)
    (hcard : S.card ≤ x.2) {v : ℕ} (hv : v ∈ x.1.1) (hhigh : isHigh x v = true) : v ∈ S := by
  by_contra hvS
  have hsub : neighbors x.1 v ⊆ S := fun u hu => by
    obtain ⟨hu, hadj⟩ := mem_neighbors.1 hu
    exact (hS v hv u hu hadj).resolve_left hvS
  have h₁ := (Finset.card_le_card hsub).trans hcard
  rw [card_neighbors] at h₁
  have h₂ := degree_le_card x.1 v
  simp only [isHigh, decide_eq_true_eq, cap_eq] at hhigh
  omega

private theorem length_high_le_card {S : Finset ℕ}
    (hS : ∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S)
    (hcard : S.card ≤ x.2) : (high x).length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup (nodup_high x)]
  exact Finset.card_le_card fun v hv => by
    obtain ⟨hv, hhigh⟩ := (mem_high x).1 (List.mem_toFinset.1 hv)
    exact mem_of_isHigh hS hcard hv hhigh

/-- **The low-degree bound** [CyganEtAl2015, Section 2.2.1]: if every vertex outside the high
vertices has degree at most `k`, a vertex cover of at most `k` vertices leaves at most `k (k + 1)`
non-isolated low vertices. -/
theorem length_active_le {S : Finset ℕ}
    (hS : ∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S)
    (hcard : S.card ≤ x.2) : (active x).length ≤ x.2 * (x.2 + 1) := by
  classical
  set T := S.filter fun v => isHigh x v = false
  have hT : T.card ≤ x.2 := (Finset.card_filter_le _ _).trans hcard
  have hdeg : ∀ u ∈ T, (neighbors x.1 u).card ≤ x.2 := fun u hu => by
    have h := (Finset.mem_filter.1 hu).2
    simp only [isHigh, decide_eq_false_iff_not, not_lt, cap_eq] at h
    rw [card_neighbors]
    omega
  have hsub : (active x).toFinset ⊆ T ∪ T.biUnion (neighbors x.1) := fun v hv => by
    obtain ⟨hvlow, u, hulow, hadj⟩ := (mem_active x).1 (List.mem_toFinset.1 hv)
    obtain ⟨hv, hvhigh⟩ := (mem_low x).1 hvlow
    obtain ⟨hu, huhigh⟩ := (mem_low x).1 hulow
    rcases hS v hv u hu hadj with hvS | huS
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hvS, hvhigh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨u, Finset.mem_filter.2 ⟨huS, huhigh⟩, mem_neighbors.2 ⟨hv, hadj.symm⟩⟩)
  rw [← List.toFinset_card_of_nodup (nodup_active x)]
  calc (active x).toFinset.card ≤ (T ∪ T.biUnion (neighbors x.1)).card := Finset.card_le_card hsub
    _ ≤ T.card + ∑ u ∈ T, (neighbors x.1 u).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    _ ≤ T.card + T.card * x.2 := Nat.add_le_add_left (Finset.sum_le_card_nsmul _ _ _ hdeg) _
    _ ≤ x.2 * (x.2 + 1) := by nlinarith

/-- Every instance of `VertexCover` passes the tests of the kernel. -/
private theorem accept_of_mem (hx : x ∈ VertexCover) : accept x = true := by
  obtain ⟨G, k⟩ := x
  obtain ⟨hk, S, -, hS, hcard⟩ := mem_VertexCover_iff_exists_card_le.1 hx
  have hcap : cap (G, k) = k := by rw [cap_eq]; exact min_eq_right hk
  have h₁ := length_high_le_card (x := (G, k)) hS hcard
  have h₂ := length_active_le (x := (G, k)) hS hcard
  simp only [accept, hcap, Bool.and_eq_true, decide_eq_true_eq, true_and]
  exact ⟨h₁.trans hcard, h₂⟩

private theorem mem_edges {i j : ℕ} : (i, j) ∈ edges x ↔ i < (active x).length ∧ j <
    (active x).length ∧
    x.1.toSimpleGraph.Adj ((active x).getD i 0) ((active x).getD j 0) := by
  simp only [edges, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Graph.adjBool_eq_true_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩
    exact ⟨hi, hj, hadj⟩
  · rintro ⟨hi, hj, hadj⟩
    exact ⟨i, hi, j, ⟨hj, hadj⟩, rfl, rfl⟩

private theorem graph_adj {i j : ℕ} : (graph x).toSimpleGraph.Adj i j ↔ i ≠ j ∧
    ((i, j) ∈ edges x ∨ (j, i) ∈ edges x) := by
  simp [graph, Graph.toSimpleGraph_adj]

/-- **Correctness of the reduction rules**: once the high vertices fit in the target, the reduced
graph has a cover of the reduced target exactly when the original graph has one of the original
target. -/
theorem graph_mem_iff (hk : cap x = x.2) (hh : (high x).length ≤ cap x) :
    (graph x, param x) ∈ VertexCover ↔ x ∈ VertexCover := by
  classical
  obtain ⟨G, k⟩ := x
  have hm := length_active_le_numVertices (G, k)
  have hn := length_high_add_length_low (G, k)
  have hlow := length_active_le_length_low (G, k)
  set a := active (G, k) with ha
  have hparam : param (G, k) = k - (high (G, k)).length := by rw [param, hk]
  simp only at hk hn
  have hget : ∀ i < a.length, a.getD i 0 ∈ low (G, k) ∧
      ∃ u ∈ low (G, k), G.toSimpleGraph.Adj (a.getD i 0) u := fun i hi =>
    (mem_active _).1 (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  rw [mem_VertexCover_iff_exists_card_le, mem_VertexCover_iff_exists_card_le]
  refine and_congr ?_ ⟨?_, ?_⟩
  · simp only [graph, List.toFinset_range, Finset.card_range, numVertices, le_min_iff,
      Nat.le_add_left, and_true]
    omega
  · rintro ⟨S', -, hS', hcard'⟩
    refine ⟨(high (G, k)).toFinset ∪ (S'.filter (· < a.length)).image (a.getD · 0), ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.1 hv with hv | hv
      · exact ((mem_high _).1 (List.mem_toFinset.1 hv)).1
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
        exact ((mem_low _).1 (hget i (Finset.mem_filter.1 hi).2).1).1
    · intro u hu v hv hadj
      by_cases huh : isHigh (G, k) u = true
      · exact Or.inl (Finset.mem_union_left _ (List.mem_toFinset.2 ((mem_high _).2 ⟨hu, huh⟩)))
      by_cases hvh : isHigh (G, k) v = true
      · exact Or.inr (Finset.mem_union_left _ (List.mem_toFinset.2 ((mem_high _).2 ⟨hv, hvh⟩)))
      simp only [Bool.not_eq_true] at huh hvh
      have hul : u ∈ low (G, k) := (mem_low _).2 ⟨hu, huh⟩
      have hvl : v ∈ low (G, k) := (mem_low _).2 ⟨hv, hvh⟩
      have hua : u ∈ a := (mem_active _).2 ⟨hul, v, hvl, hadj⟩
      have hva : v ∈ a := (mem_active _).2 ⟨hvl, u, hul, hadj.symm⟩
      have hi := List.idxOf_lt_length_iff.2 hua
      have hj := List.idxOf_lt_length_iff.2 hva
      have hgi : a.getD (a.idxOf u) 0 = u := by
        rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf]
      have hgj : a.getD (a.idxOf v) 0 = v := by
        rw [List.getD_eq_getElem _ _ hj, List.getElem_idxOf]
      have hadj' : (graph (G, k)).toSimpleGraph.Adj (a.idxOf u) (a.idxOf v) := by
        refine graph_adj.2 ⟨fun h => hadj.ne (by rw [← hgi, ← hgj, h]), Or.inl ?_⟩
        rw [mem_edges, ← ha, hgi, hgj]
        exact ⟨hi, hj, hadj⟩
      have hmem : ∀ i < a.length, i ∈ (graph (G, k)).1 := fun i hi => by
        simp only [graph, List.mem_range]
        omega
      rcases hS' _ (hmem _ hi) _ (hmem _ hj) hadj' with h | h
      · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, ?_, hgi⟩))
        exact Finset.mem_filter.2 ⟨h, hi⟩
      · refine Or.inr (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, ?_, hgj⟩))
        exact Finset.mem_filter.2 ⟨h, hj⟩
    · calc _ ≤ (high (G, k)).toFinset.card + ((S'.filter (· < a.length)).image (a.getD · 0)).card :=
            Finset.card_union_le _ _
        _ ≤ (high (G, k)).length + S'.card := Nat.add_le_add (List.toFinset_card_le _)
            (Finset.card_image_le.trans (Finset.card_filter_le _ _))
        _ ≤ k := by omega
  · rintro ⟨S, -, hS, hcard⟩
    have hhS : ∀ v ∈ high (G, k), v ∈ S := fun v hv =>
      mem_of_isHigh (x := (G, k)) hS hcard ((mem_high _).1 hv).1 ((mem_high _).1 hv).2
    refine ⟨(Finset.range a.length).filter fun i => a.getD i 0 ∈ S, ?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [graph, List.mem_range]
      omega
    · intro i _ j _ hadj
      obtain ⟨-, hij⟩ := graph_adj.1 hadj
      simp only [Finset.mem_filter, Finset.mem_range]
      rcases hij with h | h
      · obtain ⟨hi, hj, hadj⟩ := mem_edges.1 h
        rcases hS _ ((mem_low _).1 (hget i hi).1).1 _ ((mem_low _).1 (hget j hj).1).1 hadj with
          h | h
        · exact Or.inl ⟨hi, h⟩
        · exact Or.inr ⟨hj, h⟩
      · obtain ⟨hj, hi, hadj⟩ := mem_edges.1 h
        rcases hS _ ((mem_low _).1 (hget j hj).1).1 _ ((mem_low _).1 (hget i hi).1).1 hadj with
          h | h
        · exact Or.inr ⟨hj, h⟩
        · exact Or.inl ⟨hi, h⟩
    · have hsub : (high (G, k)).toFinset ⊆ S := fun v hv => hhS v (List.mem_toFinset.1 hv)
      have hinj : Set.InjOn (a.getD · 0)
          ((Finset.range a.length).filter fun i => a.getD i 0 ∈ S : Finset ℕ) := by
        intro i hi j hj hij
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
        simp only [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
        exact (nodup_active _).getElem_inj_iff.1 hij
      have hmaps : ∀ i ∈ (Finset.range a.length).filter fun i => a.getD i 0 ∈ S,
          a.getD i 0 ∈ S \ (high (G, k)).toFinset := fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        refine Finset.mem_sdiff.2 ⟨hi.2, fun h => ?_⟩
        have h₁ := ((mem_high _).1 (List.mem_toFinset.1 h)).2
        have h₂ := ((mem_low _).1 (hget i hi.1).1).2
        rw [h₁] at h₂
        exact Bool.noConfusion h₂
      have := Finset.card_le_card_of_injOn _ hmaps hinj
      rw [Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup (nodup_high _)] at this
      omega

end VertexCover.Buss

namespace VertexCover.Buss

/-! ### Size of the kernel -/

variable (x : Graph × ℕ)

private theorem param_le_cap : param x ≤ cap x := Nat.sub_le _ _

private theorem numVertices_le_of_accept (h : accept x = true) : numVertices x ≤ x.2 *
    (x.2 + 2) := by
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, -⟩, ha⟩ := h
  have h₁ := param_le_cap x
  have h₂ : numVertices x ≤ (active x).length + param x := min_le_right _ _
  rw [hc] at h₁
  nlinarith

private theorem length_edges_le : (edges x).length ≤ (active x).length * (active x).length := by
  rw [edges, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ (active x).length fun n hn => ?_).trans ?_
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hn
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (List.length_range).le
  · simp

private theorem length_edges_le_of_accept (h : accept x = true) :
    (edges x).length ≤ (x.2 * (x.2 + 1)) * (x.2 * (x.2 + 1)) := by
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, -⟩, ha⟩ := h
  rw [hc] at ha
  exact (length_edges_le x).trans (Nat.mul_le_mul ha ha)

/-- The arithmetic of the size bound. -/
private theorem size_arith {k K : ℕ} (hK : K ≤ k * (k + 2)) :
    2 * (2 * (K * (2 * K + 1)) + 1 + K * K * (2 * (2 * K + 1 + K) + 1)) + 1 + k ≤
      40 * (k + 1) ^ 6 := by
  have ha : K ≤ (k + 1) ^ 2 := hK.trans (by nlinarith)
  have h1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos k)
  have h2 : K * K ≤ (k + 1) ^ 2 * (k + 1) ^ 2 := Nat.mul_le_mul ha ha
  have h3 : K * K * K ≤ (k + 1) ^ 2 * (k + 1) ^ 2 * (k + 1) ^ 2 := Nat.mul_le_mul h2 ha
  have h4 : (k + 1) ^ 2 ≤ (k + 1) ^ 2 * (k + 1) ^ 2 := Nat.le_mul_of_pos_left _ h1
  have h5 : (k + 1) ^ 2 * (k + 1) ^ 2 ≤ (k + 1) ^ 2 * (k + 1) ^ 2 * (k + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ h1
  have h6 : (k + 1) ^ 6 = (k + 1) ^ 2 * (k + 1) ^ 2 * (k + 1) ^ 2 := by ring
  have h7 : 2 * (2 * (K * (2 * K + 1)) + 1 + K * K * (2 * (2 * K + 1 + K) + 1)) + 1 + k =
      12 * (K * K * K) + 14 * (K * K) + 4 * K + 3 + k := by ring
  have h8 : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
  rw [h7, h6]
  omega

/-- The encoded kernel has length at most `40 (k + 1) ^ 6`. -/
private theorem length_encode_le_of_accept (h : accept x = true) :
    (encPair encGraph encNat (graph x, param x)).length ≤ 40 * (x.2 + 1) ^ 6 := by
  set K := x.2 * (x.2 + 2)
  have hV : numVertices x ≤ K := numVertices_le_of_accept x h
  have hE := length_edges_le_of_accept x h
  have hm := length_active_le_numVertices x
  have hp : param x ≤ x.2 := (param_le_cap x).trans (cap_le_snd x)
  have hvert : (encList encNat (List.range (numVertices x))).length ≤ K * (2 * K + 1) := by
    refine (length_encList_le encNat _ (b := K) fun i hi => ?_).trans ?_
    · exact (length_encNat_le_self i).trans ((List.mem_range.1 hi).le.trans hV)
    · rw [List.length_range]
      exact Nat.mul_le_mul_right _ hV
  have hedge : (encList (encPair encNat encNat) (edges x)).length ≤
      K * K * (2 * (2 * K + 1 + K) + 1) := by
    refine (length_encList_le _ _ (b := 2 * K + 1 + K) fun e he => ?_).trans ?_
    · obtain ⟨i, j⟩ := e
      obtain ⟨hi, hj, -⟩ := mem_edges.1 he
      have := length_encNat_le_self i
      have := length_encNat_le_self j
      rw [length_encPair]
      dsimp only
      omega
    · refine Nat.mul_le_mul_right _ (hE.trans ?_)
      simp only [K]
      have : x.2 * (x.2 + 1) ≤ x.2 * (x.2 + 2) := Nat.mul_le_mul_left _ (by omega)
      exact Nat.mul_le_mul this this
  have := length_encNat_le_self (param x)
  simp only [graph, encGraph, length_encPair]
  exact le_trans (by omega) (size_arith (k := x.2) (K := K) le_rfl)

end VertexCover.Buss

open VertexCover.Buss in
/-- **Buss's kernel for vertex cover.** -/
def VertexCover.bussKernel (x : Graph × ℕ) : Graph × ℕ :=
  if accept x then (graph x, param x) else noInstance

namespace VertexCover.Buss

/-! ### Running time -/

open ComputableInPolyTime

/-- Computing a degree is polynomial-time, with the degree in unary. -/
@[fun_prop]
theorem computableInPolyTime_degree :
    ComputableInPolyTime (fun p : Graph × ℕ => degree p.1 p.2)
      (encPair encGraph encNat) encUnary := by
  unfold degree
  fun_prop

/-- Testing for a high vertex is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isHigh :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => isHigh p.1 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool := by
  unfold isHigh
  fun_prop

/-- Listing the high vertices is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_high :
    ComputableInPolyTime high (encPair encGraph encNat) (encList encNat) := by
  unfold high
  fun_prop

/-- Listing the low vertices is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_low :
    ComputableInPolyTime low (encPair encGraph encNat) (encList encNat) := by
  unfold low
  fun_prop

/-- Testing for an active vertex is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isActive :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => isActive p.1 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool := by
  unfold isActive
  fun_prop

/-- Listing the active vertices is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_active :
    ComputableInPolyTime active (encPair encGraph encNat) (encList encNat) := by
  unfold active
  fun_prop

/-- The kernel target is computed in unary in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_param :
    ComputableInPolyTime param (encPair encGraph encNat) encUnary := by
  unfold param
  fun_prop

/-- The number of kernel vertices is computed in unary in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_numVertices :
    ComputableInPolyTime numVertices (encPair encGraph encNat) encUnary := by
  unfold numVertices
  fun_prop

/-- The tests of the kernel are polynomial-time. The capped target `cap x` is computed in unary
and converted to binary to compare it with the binary target. -/
@[fun_prop]
theorem computableInPolyTime_accept :
    ComputableInPolyTime accept (encPair encGraph encNat) encBool := by
  unfold accept
  refine bool_and' (bool_and' ?_ (by fun_prop)) (by fun_prop)
  exact ((unary_to_binary.comp computableInPolyTime_cap).beq (snd _ _)).of_enc_eq
    fun _ => by simp [beq_eq_decide]

/-- Listing the kernel edges is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_edges :
    ComputableInPolyTime edges (encPair encGraph encNat)
      (encList (encPair encNat encNat)) := by
  unfold edges
  refine flatMapWithInput (by fun_prop) ?_
  refine mapWithInput (filterWithInput (by fun_prop) ?_) (by fun_prop)
  exact Graph.computableInPolyTime_adjBool_comp (by fun_prop)
    (listGetDWithInput (by fun_prop) (by fun_prop) 0)
    (listGetDWithInput (by fun_prop) (by fun_prop) 0)

/-- Building the kernel graph is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_graph :
    ComputableInPolyTime graph (encPair encGraph encNat) encGraph := by
  have hV : ComputableInPolyTime (fun x : Graph × ℕ => List.range (numVertices x))
      (encPair encGraph encNat) (encList encNat) := by
    simpa only [Function.comp_def, List.map_id'] using
      (map unary_to_binary).comp (range.comp computableInPolyTime_numVertices)
  exact (hV.prod computableInPolyTime_edges).of_enc_eq fun _ => rfl

end VertexCover.Buss

namespace VertexCover

open Buss

/-- **Buss's kernel preserves membership.** -/
theorem bussKernel_mem_iff (x : Graph × ℕ) : bussKernel x ∈ VertexCover ↔ x ∈ VertexCover := by
  unfold bussKernel
  cases h : accept x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact iff_of_false noInstance_notMem fun hx => by
      rw [accept_of_mem hx] at h
      exact Bool.noConfusion h
  · simp only [↓reduceIte]
    simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at h
    exact graph_mem_iff h.1.1 h.1.2

/-- Buss's kernel has at most `k (k + 2)` vertices. -/
theorem length_bussKernel_vertices_le (x : Graph × ℕ) :
    (bussKernel x).1.1.length ≤ x.2 * (x.2 + 2) := by
  unfold bussKernel
  split_ifs with h
  · simpa [graph] using numVertices_le_of_accept x h
  · simp [noInstance]

/-- Buss's kernel lists at most `(k (k + 1)) ^ 2` edges. -/
theorem length_bussKernel_edges_le (x : Graph × ℕ) :
    (bussKernel x).1.2.length ≤ (x.2 * (x.2 + 1)) * (x.2 * (x.2 + 1)) := by
  unfold bussKernel
  split_ifs with h
  · exact length_edges_le_of_accept x h
  · simp [noInstance]

/-- Buss's kernel has encoded length at most `40 (k + 1) ^ 6`. -/
theorem length_encode_bussKernel_le (x : Graph × ℕ) :
    (encPair encGraph encNat (bussKernel x)).length ≤ 40 * (x.2 + 1) ^ 6 := by
  unfold bussKernel
  split_ifs with h
  · exact length_encode_le_of_accept x h
  · have : (encPair encGraph encNat noInstance).length = 4 := by decide
    rw [this]
    have : 1 ≤ (x.2 + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    omega

/-- **Buss's kernel is polynomial-time.** -/
@[fun_prop]
theorem computableInPolyTime_bussKernel :
    ComputableInPolyTime bussKernel (encPair encGraph encNat) (encPair encGraph encNat) := by
  unfold bussKernel
  exact ComputableInPolyTime.ite' computableInPolyTime_accept
    (computableInPolyTime_graph.prod
      (ComputableInPolyTime.unary_to_binary.comp computableInPolyTime_param))
    (ComputableInPolyTime.const _)

/-- Buss's kernel has target at most `k`, or `1`. -/
theorem bussKernel_snd_le (x : Graph × ℕ) : (bussKernel x).2 ≤ max x.2 1 := by
  unfold bussKernel
  split_ifs with h
  · exact le_max_of_le_left ((param_le_cap x).trans (cap_le_snd x))
  · exact le_max_right _ _

/-- **Buss's kernel** is a kernelization of `VertexCover` parameterized by the target `k`, with
size bound `40 (k + 1) ^ 6`. -/
theorem isKernelization_bussKernel :
    IsKernelization (encPair encGraph encNat) Prod.snd VertexCover bussKernel
      fun k => 40 * (k + 1) ^ 6 where
  polyTime := computableInPolyTime_bussKernel
  mem_iff := bussKernel_mem_iff
  length_le := length_encode_bussKernel_le
  parameter_le x := by
    have h := bussKernel_snd_le x
    have : 1 ≤ (x.2 + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have : x.2 + 1 ≤ (x.2 + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    omega

end VertexCover

/-- **`VertexCover` has a polynomial kernel** in the target cover size `k` [BussGoldsmith1993]
[FlumGrohe2006, Section 9.1] [CyganEtAl2015, Section 2.2.1]: Buss's kernel has at most
`k (k + 2)` vertices and encoded length at most `40 (k + 1) ^ 6`. -/
theorem VertexCover_hasPolyKernel : HasPolyKernel (encPair encGraph encNat) Prod.snd VertexCover :=
  ⟨VertexCover.bussKernel, fun k => 40 * (k + 1) ^ 6,
    polynomiallyBounded_iff_le.2 ⟨40, 6, fun _ => le_rfl⟩, VertexCover.isKernelization_bussKernel⟩

end Cslib.Complexity
