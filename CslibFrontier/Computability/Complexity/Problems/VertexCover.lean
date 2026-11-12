/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Vertex covers

`VertexCover` is the set of graphs, given by a list of vertices and a list of edges, together with
a number `k`, such that `k` of the declared vertices meet every edge between declared vertices
[Karp1972]. Graphs are read on their declared vertices through `Cslib.Complexity.Graph.induced`,
and covers through `SimpleGraph.IsVertexCover`. Edges with an undeclared endpoint and self-loops
are therefore ignored, and repeated vertex entries count once.

The cover has exactly `k` distinct vertices, matching `IndependentSet`. Since a set of declared
vertices containing a cover is a cover, this agrees with the textbook formulation "a cover of at
most `k` vertices" for every `k` up to the number `n` of distinct declared vertices, and
`VertexCover` rejects every `k > n` (`mem_VertexCover_iff_exists_card_le`). In particular a graph
without declared vertices belongs to `VertexCover` only with `k = 0`.

A set of declared vertices is a vertex cover exactly when the remaining declared vertices form an
independent set (`SimpleGraph.isIndepSet_compl_iff_isVertexCover`), so
`IndependentSet.toVertexCover` maps `(G, m)` to `(G, n - m)`, where `n` is the number of distinct
declared vertices; a target `m > n` is mapped to the unsatisfiable target `n + 1` [Karp1972].

The same problem as a class of finite structures, closed under isomorphism and without an
encoding, with the target size given by a unary relation, is
`Cslib.Logic.FO.sizedGraph.VertexCover`. There loops are ignored, edges need not be symmetric,
and the reductions between independent set, clique and vertex cover are quantifier-free
first-order interpretations.

## Main definitions

* `Cslib.Complexity.VertexCoverInstance`, `Cslib.Complexity.VertexCover`.
* `Cslib.Complexity.VertexCover.declaredEdges`: the listed edges between declared vertices.
* `Cslib.Complexity.VertexCover.isUncoveredEdge`, `Cslib.Complexity.VertexCover.uncoveredEdges`,
  `Cslib.Complexity.VertexCover.isCover`, `Cslib.Complexity.VertexCover.verifier`.
* `Cslib.Complexity.IndependentSet.toVertexCover`.
* `Cslib.Complexity.Graph.vertexCoverNum`: the vertex cover number.

## Main results

* `Cslib.Complexity.mem_VertexCover_iff_exists_card_le`: covers of exactly `k` vertices versus
  covers of at most `k` vertices.
* `Cslib.Complexity.IndependentSet.toVertexCover_mem_iff`:
  `toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet`.
* `Cslib.Complexity.Graph.vertexCoverNum_eq_card_sub_indepNum`: the vertex cover number is the
  number of distinct declared vertices minus the independence number.
* `Cslib.Complexity.IndependentSet.computableInPolyTime_toVertexCover`: the reduction is
  polynomial-time, with targets in binary.
* `Cslib.Complexity.VertexCover.isCover_eq_true_iff`,
  `Cslib.Complexity.VertexCover.isVerifier`, `Cslib.Complexity.VertexCover.mem_NP`:
  `VertexCover ∈ NP encVertexCoverInstance`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_VertexCover`,
  `Cslib.Complexity.VertexCover_npHard`, `Cslib.Complexity.VertexCover_npComplete`:
  `VertexCover` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(graph, k)` of **Vertex Cover**. -/
@[ext]
structure VertexCoverInstance where
  /-- The graph in which to find a vertex cover. -/
  graph : Graph
  /-- The target number of declared vertices. -/
  k : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed `encGraph` followed by binary target `encNat`, encoding `VertexCoverInstance`. -/
enc_structure encVertexCoverInstance : VertexCoverInstance where
  graph : encGraph,
  k : encNat

attribute [fun_prop] encVertexCoverInstance_graph_polyTime
  encVertexCoverInstance_k_polyTime encVertexCoverInstance_mk_polyTime

/-- The graphs with a vertex cover of `k` of their vertices: `k` declared vertices meeting every
edge between two declared vertices [Karp1972]. -/
def VertexCover : Set VertexCoverInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices}, x.graph.induced.IsVertexCover S ∧ S.card = x.k}

/-- Membership in `VertexCover` as a finite set of `k` declared vertices meeting every edge between
declared vertices. -/
theorem mem_VertexCover_iff {x : VertexCoverInstance} :
    x ∈ VertexCover ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      (∀ u ∈ x.graph.vertices, ∀ v ∈ x.graph.vertices,
        x.graph.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
        S.card = x.k := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    refine ⟨S.map (.subtype _),
      fun v hv => by obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hv; exact u.2,
      fun u hu v hv huv =>
        (@hS ⟨u, hu⟩ ⟨v, hv⟩ huv).imp (Finset.mem_map_of_mem _) (Finset.mem_map_of_mem _),
      (Finset.card_map _).trans hcard⟩
  · rintro ⟨S, hSV, hS, hcard⟩
    have hmap : (S.subtype (· ∈ x.graph.vertices)).map (.subtype _) = S :=
      (Finset.subtype_map _).trans (Finset.filter_eq_self.mpr hSV)
    refine ⟨S.subtype (· ∈ x.graph.vertices), fun u v huv => ?_,
      by rw [← Finset.card_map (.subtype _), hmap, hcard]⟩
    simpa [Finset.mem_subtype] using hS u.1 u.2 v.1 v.2 huv

@[simp]
theorem mem_VertexCover_iff_mk {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : VertexCoverInstance) ∈ VertexCover ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
      (∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
        S.card = k :=
  mem_VertexCover_iff

/-- `VertexCover` through covers of at most `k` vertices: `x ∈ VertexCover` exactly when `x.k`
is at most the number of distinct declared vertices and some cover has at most `x.k` vertices. -/
theorem mem_VertexCover_iff_exists_card_le {x : VertexCoverInstance} :
    x ∈ VertexCover ↔ x.k ≤ x.graph.vertices.toFinset.card ∧ ∃ S : Finset ℕ,
      (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      (∀ u ∈ x.graph.vertices, ∀ v ∈ x.graph.vertices,
        x.graph.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
        S.card ≤ x.k := by
  rw [mem_VertexCover_iff]
  constructor
  · rintro ⟨S, hSV, hS, hcard⟩
    exact ⟨hcard ▸ Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv), S, hSV, hS,
      hcard.le⟩
  · rintro ⟨hk, S, hSV, hS, hcard⟩
    obtain ⟨T, hST, hTV, hT⟩ := Finset.exists_subsuperset_card_eq
      (fun v hv => List.mem_toFinset.2 (hSV v hv)) hcard hk
    exact ⟨T, fun v hv => List.mem_toFinset.1 (hTV hv),
      fun u hu v hv huv => (hS u hu v hv huv).imp (@hST u) (@hST v), hT⟩

theorem mem_VertexCover_iff_exists_card_le_mk {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : VertexCoverInstance) ∈ VertexCover ↔ k ≤ G.vertices.toFinset.card ∧ ∃ S : Finset ℕ,
      (∀ v ∈ S, v ∈ G.vertices) ∧
      (∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧
        S.card ≤ k :=
  mem_VertexCover_iff_exists_card_le

namespace IndependentSet

/-! ### Reduction from independent sets -/

/-- The reduction from `IndependentSet` to `VertexCover`: keep the graph and replace the target
`m` by `n - m`, where `n` is the number of distinct declared vertices, or by `n + 1` when `m > n`.
-/
def toVertexCover (x : IndependentSetInstance) : VertexCoverInstance :=
  ⟨x.graph, if x.m ≤ x.graph.vertices.toFinset.card then x.graph.vertices.toFinset.card - x.m
    else x.graph.vertices.toFinset.card + 1⟩

/-- **Independent sets are complements of vertex covers.** -/
theorem toVertexCover_mem_iff (x : IndependentSetInstance) :
    toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet := by
  classical
  obtain ⟨G, m⟩ := x
  simp only [toVertexCover, mem_VertexCover_iff, mem_IndependentSet_iff]
  have hsub : ∀ {S : Finset ℕ}, (∀ v ∈ S, v ∈ G.vertices) → S ⊆ G.vertices.toFinset :=
    fun hS v hv => List.mem_toFinset.2 (hS v hv)
  split_ifs with hm
  · constructor
    · rintro ⟨T, hTV, hT, hcard⟩
      refine ⟨G.vertices.toFinset \ T, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
        ⟨fun u hu v hv huv hadj => ?_, ?_⟩⟩
      · simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, List.mem_toFinset] at hu hv
        rcases hT u hu.1 v hv.1 hadj with h | h
        · exact hu.2 h
        · exact hv.2 h
      · rw [Finset.card_sdiff_of_subset (hsub hTV), hcard]
        omega
    · rintro ⟨S, hSV, hS, hcard⟩
      refine ⟨G.vertices.toFinset \ S, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
        fun u hu v hv hadj => ?_, ?_⟩
      · by_contra h
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_or, not_and, not_not] at h
        exact hS (h.1 hu) (h.2 hv) hadj.ne hadj
      · rw [Finset.card_sdiff_of_subset (hsub hSV), hcard]
  · refine ⟨fun ⟨T, hTV, _, hcard⟩ => ?_, fun ⟨S, hSV, hS⟩ => ?_⟩
    · have := Finset.card_le_card (hsub hTV)
      omega
    · have := Finset.card_le_card (hsub hSV)
      rw [hS.card_eq] at this
      exact (hm this).elim

/-- The reduction `toVertexCover` is polynomial-time: the vertex count is computed in unary, and
the binary target is compared with it by saturating decoding. -/
@[fun_prop]
theorem computableInPolyTime_toVertexCover :
    ComputableInPolyTime toVertexCover encIndependentSetInstance
      encVertexCoverInstance := by
  have hn : ComputableInPolyTime (fun x : IndependentSetInstance => x.graph.vertices.toFinset.card)
      encIndependentSetInstance encUnary := by
    simp_rw [← Graph.length_distinctVertices]
    fun_prop
  -- `min n m`, decoded from the binary target under the unary cap `n`.
  have hmin : ComputableInPolyTime
      (fun x : IndependentSetInstance => Cslib.BitString.boundedBinaryValue
        x.graph.vertices.toFinset.card (encNat x.m).reverse) encIndependentSetInstance encUnary :=
    bitsBoundedBinaryValueWithInput hn
      (bitsReverse.comp (encoding_comp (by fun_prop)))
  have heq : toVertexCover = fun x : IndependentSetInstance =>
      ⟨x.graph, if decide (Cslib.BitString.boundedBinaryValue x.graph.vertices.toFinset.card
          (encNat x.m).reverse = x.m)
        then x.graph.vertices.toFinset.card -
          Cslib.BitString.boundedBinaryValue x.graph.vertices.toFinset.card (encNat x.m).reverse
        else x.graph.vertices.toFinset.card + 1⟩ := by
    funext x
    simp only [toVertexCover, Bool.decide_iff, encNat_apply,
      Cslib.BitString.boundedBinaryValue_eq, Cslib.BitString.binaryValue_reverse_bits,
      min_eq_right_iff]
    split_ifs with h
    · rw [min_eq_right h]
    · rfl
  rw [heq]
  refine encVertexCoverInstance_mk_polyTime (by fun_prop)
    (ite ((unary_to_binary.comp hmin).decide_eq' (by fun_prop))
      (unary_to_binary.comp (unary_sub.comp (hn.prod hmin)))
      (unary_to_binary.comp (unary_add.comp (hn.prod (const 1)))))

end IndependentSet

namespace VertexCover

/-- Whether both endpoints of `e` are declared vertices of `G`. -/
def isDeclaredEdge (G : Graph) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices)

/-- The listed edges of `G` between declared vertices. -/
def declaredEdges (G : Graph) : List (ℕ × ℕ) :=
  G.edges.filter (isDeclaredEdge G)

/-- An edge is declared when it is listed and both endpoints are declared vertices. -/
theorem mem_declaredEdges {G : Graph} {e : ℕ × ℕ} :
    e ∈ declaredEdges G ↔ e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices := by
  simp [declaredEdges, isDeclaredEdge]

/-- Testing whether an edge joins declared vertices is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_isDeclaredEdge :
    ComputableInPolyTime (fun p : Graph × (ℕ × ℕ) => isDeclaredEdge p.1 p.2)
      (encPair encGraph (encPair encNat encNat)) encBool := by
  unfold isDeclaredEdge encGraph
  fun_prop

/-- Listing the edges between declared vertices is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_declaredEdges :
    ComputableInPolyTime declaredEdges encGraph (encList (encPair encNat encNat)) := by
  have hE : ComputableInPolyTime (fun G : Graph => G.edges) encGraph
      (encList (encPair encNat encNat)) := by
    fun_prop
  exact filterWithInput hE computableInPolyTime_isDeclaredEdge

/-- Whether the edge `e` joins two distinct declared vertices of `G` and neither endpoint is in
`C`. -/
def isUncoveredEdge (G : Graph) (C : List ℕ) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices) &&
    decide (e.1 ≠ e.2) && !decide (e.1 ∈ C) && !decide (e.2 ∈ C)

/-- The edges of `G` between distinct declared vertices with neither endpoint in `C`. -/
def uncoveredEdges (G : Graph) (C : List ℕ) : List (ℕ × ℕ) :=
  G.edges.filter (isUncoveredEdge G C)

/-- Whether `C` covers every edge of `G` between declared vertices. -/
def isCover (G : Graph) (C : List ℕ) : Bool :=
  (uncoveredEdges G C).isEmpty

theorem isUncoveredEdge_eq_true_iff {G : Graph} {C : List ℕ} {e : ℕ × ℕ} :
    isUncoveredEdge G C e = true ↔
      e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices ∧ e.1 ≠ e.2 ∧ e.1 ∉ C ∧ e.2 ∉ C := by
  simp [isUncoveredEdge, and_assoc]

theorem mem_uncoveredEdges_iff {G : Graph} {C : List ℕ} {e : ℕ × ℕ} :
    e ∈ uncoveredEdges G C ↔
      e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices ∧ e.1 ≠ e.2 ∧ e.1 ∉ C ∧ e.2 ∉ C := by
  rw [uncoveredEdges, List.mem_filter, isUncoveredEdge_eq_true_iff]

/-- `isCover G C` holds exactly when every edge between declared vertices of `G` has an endpoint in
`C`. -/
theorem isCover_eq_true_iff {G : Graph} {C : List ℕ} :
    isCover G C = true ↔
      ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toSimpleGraph.Adj u v → u ∈ C ∨ v ∈ C := by
  simp only [isCover, uncoveredEdges, List.isEmpty_iff, List.filter_eq_nil_iff,
    isUncoveredEdge_eq_true_iff, Graph.toSimpleGraph_adj, not_and, not_not, Prod.forall]
  constructor
  · rintro h u hu v hv ⟨huv, he | he⟩
    · by_cases huC : u ∈ C
      · exact Or.inl huC
      · exact Or.inr (h u v he hu hv huv huC)
    · by_cases hvC : v ∈ C
      · exact Or.inr hvC
      · exact Or.inl (h v u he hv hu huv.symm hvC)
  · intro h u v he hu hv huv huC
    exact (h u hu v hv ⟨huv, Or.inl he⟩).resolve_left huC

/-- Testing whether an edge is uncovered is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_isUncoveredEdge :
    ComputableInPolyTime
      (fun p : (Graph × List ℕ) × (ℕ × ℕ) => isUncoveredEdge p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) (encPair encNat encNat)) encBool := by
  unfold isUncoveredEdge
  fun_prop

/-- Listing the uncovered edges is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_uncoveredEdges :
    ComputableInPolyTime (fun p : Graph × List ℕ => uncoveredEdges p.1 p.2)
      (encPair encGraph (encList encNat)) (encList (encPair encNat encNat)) := by
  have hE : ComputableInPolyTime (fun p : Graph × List ℕ => p.1.edges)
      (encPair encGraph (encList encNat)) (encList (encPair encNat encNat)) := by
    fun_prop
  exact filterWithInput hE computableInPolyTime_isUncoveredEdge

/-- Testing whether `C` is a cover of `G` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isCover :
    ComputableInPolyTime (fun p : Graph × List ℕ => isCover p.1 p.2)
      (encPair encGraph (encList encNat)) encBool := by
  unfold isCover
  fun_prop

/-- The verifier for `VertexCover`, a subset verifier (`Cslib.Complexity.subsetVerifier`): select
distinct declared vertices by the certificate mask, check that their count equals `k`, and check
that every edge between declared vertices has a selected endpoint (`isCover`). -/
def verifier : VertexCoverInstance × List Bool → Bool :=
  subsetVerifier (fun x => x.graph.vertices)
    fun y => decide (y.2.length = y.1.k) && isCover y.1.graph y.2

/-- `VertexCover.verifier` verifies `VertexCover` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier encVertexCoverInstance Polynomial.X verifier VertexCover := by
  have hset : VertexCover = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      (∀ u ∈ x.graph.vertices, ∀ v ∈ x.graph.vertices,
        x.graph.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = x.k} :=
    Set.ext fun _ => mem_VertexCover_iff
  rw [hset]
  refine isVerifier_subsetVerifier
    (fun x => by
      have := x.graph.length_vertices_le_encGraph
      rw [encVertexCoverInstance_apply]
      simp only [Polynomial.eval_X, length_encPair]
      omega)
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, isCover_eq_true_iff, List.mem_toFinset,
    List.toFinset_card_of_nodup hl, and_comm]

/-- The `VertexCover` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encVertexCoverInstance encBits) encBool := by
  refine computableInPolyTime_subsetVerifier (encγ := encNat)
    (by fun_prop)
    (bool_and' ?_ (computableInPolyTime_isCover.comp
      ((encVertexCoverInstance_graph_polyTime (fst _ _)).prod (snd _ _))))
  exact ((length_list_binary encNat).comp (snd _ _)).decide_eq' (by fun_prop)

/-- `VertexCover` belongs to `NP`. -/
theorem mem_NP : VertexCover ∈ NP encVertexCoverInstance :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end VertexCover

/-- `IndependentSet` reduces to `VertexCover` in polynomial time via
`IndependentSet.toVertexCover`. -/
theorem polyTimeReducible_IndependentSet_VertexCover :
    PolyTimeReducible encIndependentSetInstance encVertexCoverInstance IndependentSet
      VertexCover :=
  ⟨IndependentSet.toVertexCover, IndependentSet.computableInPolyTime_toVertexCover,
    fun x => (IndependentSet.toVertexCover_mem_iff x).symm⟩

/-- `VertexCover` is `NP`-hard. -/
theorem VertexCover_npHard : NPHard encVertexCoverInstance VertexCover :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_VertexCover

/-- **`VertexCover` is NP-complete** [Karp1972]. -/
theorem VertexCover_npComplete : NPComplete encVertexCoverInstance VertexCover :=
  ⟨VertexCover.mem_NP, VertexCover_npHard⟩

/-! ### The vertex cover number -/

namespace Graph

/-- The **vertex cover number** of a graph: the least number of declared vertices meeting every
edge between declared vertices. -/
noncomputable def vertexCoverNum (G : Graph) : ℕ := G.induced.vertexCoverNum.toNat

/-- The vertex cover number is the size of a vertex cover. -/
theorem vertexCoverNum_mem_VertexCover (G : Graph) :
    (⟨G, G.vertexCoverNum⟩ : VertexCoverInstance) ∈ VertexCover := by
  classical
  obtain ⟨s, hs_card, hs⟩ := G.induced.vertexCoverNum_exists
  refine ⟨s.toFinset, by simpa using hs, ?_⟩
  rw [← Set.coe_toFinset s, Set.encard_coe_eq_coe_finsetCard] at hs_card
  exact (ENat.toNat_natCast _).symm.trans (congrArg ENat.toNat hs_card)

/-- Every vertex cover has at least `G.vertexCoverNum` vertices. -/
theorem vertexCoverNum_le_of_mem_VertexCover {G : Graph} {k : ℕ}
    (h : (⟨G, k⟩ : VertexCoverInstance) ∈ VertexCover) :
    G.vertexCoverNum ≤ k := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  have hle := hS.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard, hcard] at hle
  exact ENat.toNat_le_of_le_natCast hle

/-- **A vertex cover is the complement of an independent set**: the vertex cover number is the
number of distinct declared vertices minus the independence number. -/
theorem vertexCoverNum_eq_card_sub_indepNum (G : Graph) :
    G.vertexCoverNum = G.vertices.toFinset.card - G.indepNum := by
  have hα := indepNum_mem_IndependentSet G
  have hαn := indepNum_le_card G
  have hvc : (⟨G, G.vertices.toFinset.card - G.indepNum⟩ : VertexCoverInstance) ∈
      VertexCover := by
    have := (IndependentSet.toVertexCover_mem_iff ⟨G, G.indepNum⟩).2 hα
    rwa [IndependentSet.toVertexCover, ite_eq_left hαn] at this
  refine le_antisymm (vertexCoverNum_le_of_mem_VertexCover hvc) ?_
  have hτ : (⟨G, G.vertexCoverNum⟩ : VertexCoverInstance) ∈ VertexCover :=
    vertexCoverNum_mem_VertexCover G
  have hτn : G.vertexCoverNum ≤ G.vertices.toFinset.card :=
    (mem_VertexCover_iff_exists_card_le.1 hτ).1
  have hIS : (⟨G, G.vertices.toFinset.card - G.vertexCoverNum⟩ : IndependentSetInstance) ∈
      IndependentSet := by
    refine (IndependentSet.toVertexCover_mem_iff _).1 ?_
    rwa [IndependentSet.toVertexCover, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hτn]
  have := le_indepNum_iff.2 hIS
  omega

end Graph

end Cslib.Complexity
