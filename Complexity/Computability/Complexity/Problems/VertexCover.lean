/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

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

* `Cslib.Complexity.VertexCover`.
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
  `VertexCover ∈ NP (encPair encGraph encNat)`.
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

/-- The graphs with a vertex cover of `k` of their vertices: `k` declared vertices meeting every
edge between two declared vertices [Karp1972]. -/
def VertexCover : Set (Graph × ℕ) :=
  {x | ∃ S : Finset {v // v ∈ x.1.1}, x.1.induced.IsVertexCover S ∧ S.card = x.2}

/-- Membership in `VertexCover` as a finite set of `k` declared vertices meeting every edge between
declared vertices. -/
theorem mem_VertexCover_iff {G : Graph} {k : ℕ} :
    (G, k) ∈ VertexCover ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = k := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    refine ⟨S.map (.subtype _),
      fun v hv => by obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hv; exact u.2,
      fun u hu v hv huv =>
        (@hS ⟨u, hu⟩ ⟨v, hv⟩ huv).imp (Finset.mem_map_of_mem _) (Finset.mem_map_of_mem _),
      (Finset.card_map _).trans hcard⟩
  · rintro ⟨S, hSV, hS, rfl⟩
    have hmap : (S.subtype (· ∈ G.1)).map (.subtype _) = S :=
      (Finset.subtype_map _).trans (Finset.filter_eq_self.mpr hSV)
    refine ⟨S.subtype (· ∈ G.1), fun u v huv => ?_,
      by rw [← Finset.card_map (.subtype _), hmap]⟩
    simpa [Finset.mem_subtype] using hS u.1 u.2 v.1 v.2 huv

/-- `VertexCover` through covers of at most `k` vertices: `(G, k) ∈ VertexCover` exactly when `k`
is at most the number of distinct declared vertices and some cover has at most `k` vertices. -/
theorem mem_VertexCover_iff_exists_card_le {G : Graph} {k : ℕ} :
    (G, k) ∈ VertexCover ↔ k ≤ G.1.toFinset.card ∧ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card ≤ k := by
  rw [mem_VertexCover_iff]
  constructor
  · rintro ⟨S, hSV, hS, rfl⟩
    exact ⟨Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv), S, hSV, hS, le_rfl⟩
  · rintro ⟨hk, S, hSV, hS, hcard⟩
    obtain ⟨T, hST, hTV, hT⟩ := Finset.exists_subsuperset_card_eq
      (fun v hv => List.mem_toFinset.2 (hSV v hv)) hcard hk
    exact ⟨T, fun v hv => List.mem_toFinset.1 (hTV hv),
      fun u hu v hv huv => (hS u hu v hv huv).imp (@hST u) (@hST v), hT⟩

namespace IndependentSet

/-! ### Reduction from independent sets -/

/-- The reduction from `IndependentSet` to `VertexCover`: keep the graph and replace the target
`m` by `n - m`, where `n` is the number of distinct declared vertices, or by `n + 1` when `m > n`.
-/
def toVertexCover (x : Graph × ℕ) : Graph × ℕ :=
  (x.1, if x.2 ≤ x.1.1.toFinset.card then x.1.1.toFinset.card - x.2 else x.1.1.toFinset.card + 1)

/-- **Independent sets are complements of vertex covers.** -/
theorem toVertexCover_mem_iff (x : Graph × ℕ) :
    toVertexCover x ∈ VertexCover ↔ x ∈ IndependentSet := by
  classical
  obtain ⟨G, m⟩ := x
  simp only [toVertexCover, mem_VertexCover_iff, mem_IndependentSet_iff]
  have hsub : ∀ {S : Finset ℕ}, (∀ v ∈ S, v ∈ G.1) → S ⊆ G.1.toFinset :=
    fun hS v hv => List.mem_toFinset.2 (hS v hv)
  split_ifs with hm
  · constructor
    · rintro ⟨T, hTV, hT, hcard⟩
      refine ⟨G.1.toFinset \ T, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
        ⟨fun u hu v hv huv hadj => ?_, ?_⟩⟩
      · simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, List.mem_toFinset] at hu hv
        rcases hT u hu.1 v hv.1 hadj with h | h
        · exact hu.2 h
        · exact hv.2 h
      · rw [Finset.card_sdiff_of_subset (hsub hTV), hcard]
        omega
    · rintro ⟨S, hSV, hS, hcard⟩
      refine ⟨G.1.toFinset \ S, fun v hv => List.mem_toFinset.1 (Finset.mem_sdiff.1 hv).1,
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
    ComputableInPolyTime toVertexCover (encPair encGraph encNat)
      (encPair encGraph encNat) := by
  have hn : ComputableInPolyTime (fun x : Graph × ℕ => x.1.1.toFinset.card)
      (encPair encGraph encNat) encUnary := by
    simp_rw [← Graph.length_distinctVertices]
    exact (length_list encNat).comp
      (Graph.computableInPolyTime_distinctVertices.comp (fst _ _))
  -- `min n m`, decoded from the binary target under the unary cap `n`.
  have hmin : ComputableInPolyTime
      (fun x : Graph × ℕ => Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card
        (encNat x.2).reverse) (encPair encGraph encNat) encUnary :=
    bitsBoundedBinaryValueWithInput hn (bitsReverse.comp (encoding_comp (snd _ _)))
  have heq : toVertexCover = fun x : Graph × ℕ =>
      (x.1, if decide (Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card
          (encNat x.2).reverse = x.2)
        then x.1.1.toFinset.card -
          Cslib.BitString.boundedBinaryValue x.1.1.toFinset.card (encNat x.2).reverse
        else x.1.1.toFinset.card + 1) := by
    funext x
    simp only [toVertexCover, Bool.decide_iff, encNat_apply, Cslib.BitString.boundedBinaryValue_eq,
      Cslib.BitString.binaryValue_reverse_bits, min_eq_right_iff]
    split_ifs with h
    · rw [min_eq_right h]
    · rfl
  rw [heq]
  refine (fst _ _).prod (ite ((unary_to_binary.comp hmin).decide_eq' (snd _ _))
    (unary_to_binary.comp (unary_sub.comp (hn.prod hmin)))
    (unary_to_binary.comp (unary_add.comp (hn.prod (const 1)))))

end IndependentSet

namespace VertexCover

/-- Whether the edge `e` joins two distinct declared vertices of `G` and neither endpoint is in
`C`. -/
def isUncoveredEdge (G : Graph) (C : List ℕ) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ∈ G.1) && decide (e.2 ∈ G.1) &&
    decide (e.1 ≠ e.2) && !decide (e.1 ∈ C) && !decide (e.2 ∈ C)

/-- The edges of `G` between distinct declared vertices with neither endpoint in `C`. -/
def uncoveredEdges (G : Graph) (C : List ℕ) : List (ℕ × ℕ) :=
  G.2.filter (isUncoveredEdge G C)

/-- Whether `C` covers every edge of `G` between declared vertices. -/
def isCover (G : Graph) (C : List ℕ) : Bool :=
  (uncoveredEdges G C).isEmpty

theorem isUncoveredEdge_eq_true_iff {G : Graph} {C : List ℕ} {e : ℕ × ℕ} :
    isUncoveredEdge G C e = true ↔
      e.1 ∈ G.1 ∧ e.2 ∈ G.1 ∧ e.1 ≠ e.2 ∧ e.1 ∉ C ∧ e.2 ∉ C := by
  simp [isUncoveredEdge, and_assoc]

theorem mem_uncoveredEdges_iff {G : Graph} {C : List ℕ} {e : ℕ × ℕ} :
    e ∈ uncoveredEdges G C ↔
      e ∈ G.2 ∧ e.1 ∈ G.1 ∧ e.2 ∈ G.1 ∧ e.1 ≠ e.2 ∧ e.1 ∉ C ∧ e.2 ∉ C := by
  rw [uncoveredEdges, List.mem_filter, isUncoveredEdge_eq_true_iff]

/-- `isCover G C` holds exactly when every edge between declared vertices of `G` has an endpoint in
`C`. -/
theorem isCover_eq_true_iff {G : Graph} {C : List ℕ} :
    isCover G C = true ↔
      ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ C ∨ v ∈ C := by
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
  unfold isUncoveredEdge encGraph
  fun_prop

/-- Listing the uncovered edges is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_uncoveredEdges :
    ComputableInPolyTime (fun p : Graph × List ℕ => uncoveredEdges p.1 p.2)
      (encPair encGraph (encList encNat)) (encList (encPair encNat encNat)) := by
  have hE : ComputableInPolyTime (fun p : Graph × List ℕ => p.1.2)
      (encPair encGraph (encList encNat)) (encList (encPair encNat encNat)) := by
    unfold encGraph
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
def verifier : (Graph × ℕ) × List Bool → Bool :=
  subsetVerifier (fun x => x.1.1) fun y => decide (y.2.length = y.1.2) && isCover y.1.1 y.2

/-- `VertexCover.verifier` verifies `VertexCover` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier VertexCover := by
  have hset : VertexCover = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1.1) ∧
      (∀ u ∈ x.1.1, ∀ v ∈ x.1.1, x.1.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = x.2} :=
    Set.ext fun _ => mem_VertexCover_iff
  rw [hset]
  refine isVerifier_subsetVerifier
    (fun x => by
      have := x.1.length_vertices_le_encGraph
      simp only [Polynomial.eval_X, length_encPair]
      omega)
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, isCover_eq_true_iff, List.mem_toFinset,
    List.toFinset_card_of_nodup hl, and_comm]

/-- The `VertexCover` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encPair encGraph encNat) encBits) encBool := by
  refine computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold encGraph; fun_prop)
    (bool_and' ?_ (computableInPolyTime_isCover.comp
      (((fst _ _).comp (fst _ _)).prod (snd _ _))))
  exact ((length_list_binary encNat).comp (snd _ _)).decide_eq' (by fun_prop)

/-- `VertexCover` belongs to `NP`. -/
theorem mem_NP : VertexCover ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end VertexCover

/-- `IndependentSet` reduces to `VertexCover` in polynomial time via
`IndependentSet.toVertexCover`. -/
theorem polyTimeReducible_IndependentSet_VertexCover :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet
      VertexCover :=
  ⟨IndependentSet.toVertexCover, IndependentSet.computableInPolyTime_toVertexCover,
    fun x => (IndependentSet.toVertexCover_mem_iff x).symm⟩

/-- `VertexCover` is `NP`-hard. -/
theorem VertexCover_npHard : NPHard (encPair encGraph encNat) VertexCover :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_VertexCover

/-- **`VertexCover` is NP-complete** [Karp1972]. -/
theorem VertexCover_npComplete : NPComplete (encPair encGraph encNat) VertexCover :=
  ⟨VertexCover.mem_NP, VertexCover_npHard⟩

/-! ### The vertex cover number -/

namespace Graph

/-- The **vertex cover number** of a graph: the least number of declared vertices meeting every
edge between declared vertices. -/
noncomputable def vertexCoverNum (G : Graph) : ℕ := G.induced.vertexCoverNum.toNat

/-- The vertex cover number is the size of a vertex cover. -/
theorem vertexCoverNum_mem_VertexCover (G : Graph) : (G, G.vertexCoverNum) ∈ VertexCover := by
  classical
  obtain ⟨s, hs_card, hs⟩ := G.induced.vertexCoverNum_exists
  refine ⟨s.toFinset, by simpa using hs, ?_⟩
  rw [← Set.coe_toFinset s, Set.encard_coe_eq_coe_finsetCard] at hs_card
  exact (ENat.toNat_natCast _).symm.trans (congrArg ENat.toNat hs_card)

/-- Every vertex cover has at least `G.vertexCoverNum` vertices. -/
theorem vertexCoverNum_le_of_mem_VertexCover {G : Graph} {k : ℕ} (h : (G, k) ∈ VertexCover) :
    G.vertexCoverNum ≤ k := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  have hle := hS.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard, hcard] at hle
  exact ENat.toNat_le_of_le_natCast hle

/-- **A vertex cover is the complement of an independent set**: the vertex cover number is the
number of distinct declared vertices minus the independence number. -/
theorem vertexCoverNum_eq_card_sub_indepNum (G : Graph) :
    G.vertexCoverNum = G.1.toFinset.card - G.indepNum := by
  have hα := indepNum_mem_IndependentSet G
  have hαn := indepNum_le_card G
  have hvc : (G, G.1.toFinset.card - G.indepNum) ∈ VertexCover := by
    have := (IndependentSet.toVertexCover_mem_iff (G, G.indepNum)).2 hα
    rwa [IndependentSet.toVertexCover, ite_eq_left hαn] at this
  refine le_antisymm (vertexCoverNum_le_of_mem_VertexCover hvc) ?_
  have hτ : (G, G.vertexCoverNum) ∈ VertexCover := vertexCoverNum_mem_VertexCover G
  have hτn : G.vertexCoverNum ≤ G.1.toFinset.card := (mem_VertexCover_iff_exists_card_le.1 hτ).1
  have hIS : (G, G.1.toFinset.card - G.vertexCoverNum) ∈ IndependentSet := by
    refine (IndependentSet.toVertexCover_mem_iff _).1 ?_
    rwa [IndependentSet.toVertexCover, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hτn]
  have := le_indepNum_iff.2 hIS
  omega

end Graph

end Cslib.Complexity
