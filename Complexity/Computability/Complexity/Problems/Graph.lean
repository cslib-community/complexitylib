/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sets
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Mathlib.Data.List.GetD
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Graphs given by vertex and edge lists

The graph problems (`IndependentSet`, `Clique`, `VertexCover`, `KColoring`, the Hamiltonian
problems, `GraphIsomorphism`, …) take a graph (`Cslib.Complexity.Graph`) as a list of declared
vertices, possibly with repetitions, and a list of edges, encoded in binary
(`Cslib.Complexity.encGraph`). Its mathematical reading is a Mathlib simple graph on `ℕ`
(`Cslib.Complexity.Graph.toSimpleGraph`), or the simple graph induced on the subtype of declared
vertices (`Cslib.Complexity.Graph.induced`): two distinct vertices are adjacent when an edge joins
them in either direction.

This module holds the tools these problems share:

* adjacency is tested in polynomial time (`Cslib.Complexity.Graph.adjBool`);
* a vertex subset problem with a pairwise condition, such as independent set or clique, is
  verified by selecting distinct declared vertices with a certificate mask
  (`Cslib.Complexity.Graph.verifySubset`, an instance of `Cslib.Complexity.subsetVerifier`);
* the distinct declared vertices (`Cslib.Complexity.Graph.distinctVertices`) are listed in
  polynomial time by selecting every first occurrence (`Cslib.Complexity.selectDistinct`), and
  their positions enumerate the declared vertices (`Cslib.Complexity.Graph.vertexEquiv`);
* explicit verifiers with fixed certificate lengths write numbers in unary blocks of a certificate
  (`Cslib.Complexity.unaryBlocks`): each number, at most `m`, gets its own block of `m` bits, and
  it is read back by counting the set bits of its block (`Cslib.Complexity.countP_unaryBlocks`);
* a vertex ordering problem, such as Hamiltonian path/cycle, TSP or graph isomorphism, is verified
  by decoding a list of vertices from unary blocks of a certificate
  (`Cslib.Complexity.Graph.decodeVertexList`) and checking that it lists every vertex of the target
  list without repetitions (`Cslib.Complexity.Graph.enumeratesBool`,
  `Cslib.Complexity.Graph.verifyOrdering`).

## Main definitions

* `Cslib.Complexity.Graph`, `Cslib.Complexity.encGraph`, `Cslib.Complexity.Graph.toSimpleGraph`,
  `Cslib.Complexity.Graph.induced`.
* `Cslib.Complexity.Graph.adjBool`: executable adjacency.
* `Cslib.Complexity.Graph.verifySubset`: the verifier of a vertex subset problem.
* `Cslib.Complexity.Graph.distinctVertices`, `Cslib.Complexity.Graph.vertexEquiv`: the declared
  vertices without repetitions and their enumeration by positions.
* `Cslib.Complexity.unaryBlocks`: numbers written in unary blocks of a certificate.
* `Cslib.Complexity.Graph.enumeratesBool`, `Cslib.Complexity.Graph.decodeVertexList`,
  `Cslib.Complexity.Graph.verifyOrdering`: verifying orderings of a vertex list.

## Main results

* `Cslib.Complexity.Graph.toSimpleGraph_adj`, `Cslib.Complexity.Graph.induced_adj`,
  `Cslib.Complexity.Graph.adjBool_eq_true_iff`: adjacency.
* `Cslib.Complexity.Graph.computableInPolyTime_adjBool`,
  `Cslib.Complexity.Graph.computableInPolyTime_adjBool_comp`: testing adjacency is polynomial-time.
* `Cslib.Complexity.Graph.isVerifier_verifySubset`,
  `Cslib.Complexity.Graph.computableInPolyTime_verifySubset`: the subset verifier is a
  polynomial-time verifier.
* `Cslib.Complexity.Graph.length_vertices_le_encGraph`: a graph has no more declared vertices than
  the length of its encoding.
* `Cslib.Complexity.countP_unaryBlocks`: counting the set bits of a block reads its number.
* `Cslib.Complexity.Graph.exists_decodeVertexList_eq`,
  `Cslib.Complexity.Graph.isVerifier_verifyOrdering`,
  `Cslib.Complexity.Graph.computableInPolyTime_verifyOrdering`: the ordering verifier is a
  polynomial-time verifier with quadratic certificate length.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- A graph on natural numbers, given by its vertices and its edges. -/
abbrev Graph : Type := List ℕ × List (ℕ × ℕ)

/-- Graphs encoded by framed lists of binary vertex labels and binary edge pairs. -/
def encGraph : Graph ↪ List Bool :=
  encPair (encList encNat) (encList (encPair encNat encNat))

/-- The simple graph of an edge list: two distinct vertices are adjacent when an edge joins them,
in either direction. -/
def Graph.toSimpleGraph (G : Graph) : SimpleGraph ℕ := SimpleGraph.fromRel fun u v => (u, v) ∈ G.2


/-- Adjacency in the simple graph of an edge list: two distinct vertices joined by an edge in
either direction. It is not a `simp` lemma, so that the adjacency stays folded until a proof
unfolds it. -/
theorem Graph.toSimpleGraph_adj {G : Graph} {u v : ℕ} :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ((u, v) ∈ G.2 ∨ (v, u) ∈ G.2) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The simple graph induced by `G` on its declared vertices. -/
def Graph.induced (G : Graph) : SimpleGraph {v // v ∈ G.1} :=
  G.toSimpleGraph.induce {v | v ∈ G.1}

@[simp]
theorem Graph.induced_adj {G : Graph} {u v : {v // v ∈ G.1}} :
    G.induced.Adj u v ↔ G.toSimpleGraph.Adj u v :=
  Iff.rfl

namespace Graph

/-! ### Declared vertices -/

/-- A graph has no more declared vertices than the length of its encoding. -/
theorem length_vertices_le_encGraph (G : Graph) : G.1.length ≤ (encGraph G).length := by
  calc G.1.length ≤ (encList encNat G.1).length := length_le_length_encList encNat G.1
    _ ≤ (encGraph G).length := by
        simp only [encGraph, length_encPair]
        omega

/-- The declared vertices of `G` without repetitions, in the order of their first occurrences. -/
def distinctVertices (G : Graph) : List ℕ := selectDistinct G.1 (List.replicate G.1.length true)

/-- The distinct declared vertices are the declared vertices. -/
theorem mem_distinctVertices {G : Graph} {v : ℕ} : v ∈ G.distinctVertices ↔ v ∈ G.1 :=
  mem_selectDistinct_replicate

/-- The distinct declared vertices are listed without repetitions. -/
theorem nodup_distinctVertices (G : Graph) : G.distinctVertices.Nodup := nodup_selectDistinct _ _

/-- The distinct declared vertices are as many as the elements of the vertex list. -/
theorem length_distinctVertices (G : Graph) : G.distinctVertices.length = G.1.toFinset.card :=
  length_selectDistinct_replicate G.1

/-- A graph has no more distinct vertices than the length of its encoding. -/
theorem length_distinctVertices_le (G : Graph) :
    G.distinctVertices.length ≤ (encGraph G).length := by
  rw [length_distinctVertices]
  exact G.1.toFinset_card_le.trans G.length_vertices_le_encGraph

/-- Positions in `G.distinctVertices` enumerate the declared vertices. -/
def vertexEquiv (G : Graph) : Fin G.distinctVertices.length ≃ {v // v ∈ G.1} :=
  (G.nodup_distinctVertices.getEquiv _).trans
    (Equiv.subtypeEquivRight fun _ => mem_distinctVertices)

theorem vertexEquiv_apply (G : Graph) (i : Fin G.distinctVertices.length) :
    (G.vertexEquiv i : ℕ) = G.distinctVertices.getD i 0 := by
  simp [vertexEquiv, List.Nodup.getEquiv, List.getD_eq_getElem?_getD]

@[simp]
theorem card_vertexSubtype (G : Graph) :
    Fintype.card {v // v ∈ G.1} = G.1.toFinset.card := by
  rw [← Fintype.card_of_bijective G.vertexEquiv.bijective, Fintype.card_fin,
    length_distinctVertices]

theorem natCard_vertexSubtype (G : Graph) :
    Nat.card {v // v ∈ G.1} = G.1.toFinset.card := by
  rw [Nat.card_eq_fintype_card, card_vertexSubtype]

/-- Listing the distinct vertices is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_distinctVertices :
    ComputableInPolyTime distinctVertices encGraph (encList encNat) := by
  unfold distinctVertices encGraph
  fun_prop

/-! ### Subset verification on encoded graphs -/

/-- Executable adjacency test on an edge list: two distinct vertices are adjacent when an edge
joins them in either direction. -/
def adjBool (G : Graph) (u v : ℕ) : Bool :=
  decide (u ≠ v) &&
    (G.2.any (fun e => decide (e = (u, v))) || G.2.any (fun e => decide (e = (v, u))))

@[simp]
theorem adjBool_eq_true_iff (G : Graph) (u v : ℕ) :
    G.adjBool u v = true ↔ G.toSimpleGraph.Adj u v := by
  simp [adjBool, toSimpleGraph_adj]

@[simp]
theorem adjBool_eq_false_iff (G : Graph) (u v : ℕ) :
    G.adjBool u v = false ↔ ¬G.toSimpleGraph.Adj u v := by
  rw [← Bool.not_eq_true, ← adjBool_eq_true_iff, Bool.not_eq_true]

/-- Testing adjacency in an encoded graph is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_adjBool :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.adjBool p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool := by
  unfold adjBool encGraph
  fun_prop

/-- Testing adjacency between computed vertices of a computed graph is polynomial-time. This is
`Cslib.Complexity.Graph.computableInPolyTime_adjBool` in the compositional form that `fun_prop`
uses. -/
@[fun_prop]
theorem computableInPolyTime_adjBool_comp {γ : Type} {enc : γ ↪ List Bool}
    {G : γ → Graph} {u v : γ → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hu : ComputableInPolyTime u enc encNat) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun c => (G c).adjBool (u c) (v c)) enc encBool :=
  computableInPolyTime_adjBool.comp ((hG.prod hu).prod hv)

/-- Verify a cardinality-`m` vertex subset problem with pairwise relation `rel`: select distinct
declared vertices from `G.1` by the certificate mask, compare the selected count with `m` in
binary, and test `rel` on all distinct selected pairs. -/
def verifySubset (rel : Graph → ℕ → ℕ → Bool) : (Graph × ℕ) × List Bool → Bool :=
  subsetVerifier (fun x => x.1.1) fun y =>
    decide (y.2.length = y.1.2) && y.2.all fun u => y.2.all fun v => decide (u = v) || rel y.1.1 u v

/-- A finite subset of declared vertices with a pairwise property corresponds to a finite subset of
`ℕ` contained in `G.1` with the same pairwise property and cardinality. -/
theorem exists_subtype_pairwise_iff {G : Graph} {P : ℕ → ℕ → Prop} {m : ℕ} :
    (∃ S : Finset {v // v ∈ G.1},
        (S : Set {v // v ∈ G.1}).Pairwise (fun u v => P u v) ∧ S.card = m) ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧ (S : Set ℕ).Pairwise P ∧ S.card = m := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    refine ⟨S.map (.subtype _),
      fun v hv => by obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hv; exact u.2,
      ?_, Finset.card_map _⟩
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_map] at hu hv
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨v, hv, rfl⟩ := hv
    exact hS hu hv (Subtype.coe_ne_coe.1 huv)
  · rintro ⟨S, hSV, hS, rfl⟩
    have hmap : (S.subtype (· ∈ G.1)).map (.subtype _) = S :=
      (Finset.subtype_map _).trans (Finset.filter_eq_self.mpr hSV)
    refine ⟨S.subtype (· ∈ G.1), ?_, by rw [← Finset.card_map (.subtype _), hmap]⟩
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_subtype] at hu hv
    exact hS hu hv (Subtype.ext_iff.not.1 huv)

/-- `verifySubset` is a polynomial-length verifier for any graph subset problem whose pairwise
relation agrees with `rel` on distinct vertices. -/
theorem isVerifier_verifySubset {rel : Graph → ℕ → ℕ → Bool} {P : Graph → ℕ → ℕ → Prop}
    (hrel : ∀ G u v, u ≠ v → (rel G u v = true ↔ P G u v)) :
    IsVerifier (encPair encGraph encNat) Polynomial.X (verifySubset rel)
      {x | ∃ S : Finset {v // v ∈ x.1.1},
        (S : Set {v // v ∈ x.1.1}).Pairwise (fun u v => P x.1 u v) ∧ S.card = x.2} := by
  have hset :
      {x : Graph × ℕ | ∃ S : Finset {v // v ∈ x.1.1},
        (S : Set {v // v ∈ x.1.1}).Pairwise (fun u v => P x.1 u v) ∧ S.card = x.2} =
      {x : Graph × ℕ | ∃ S : Finset ℕ,
        (∀ v ∈ S, v ∈ x.1.1) ∧ (S : Set ℕ).Pairwise (P x.1) ∧ S.card = x.2} :=
    Set.ext fun _ => exists_subtype_pairwise_iff
  rw [hset]
  refine isVerifier_subsetVerifier
    (fun x => by
      have := x.1.length_vertices_le_encGraph
      simp only [Polynomial.eval_X, length_encPair]
      omega)
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.toFinset_card_of_nodup hl, List.coe_toFinset]
  refine ⟨fun ⟨hlen, h⟩ => ⟨fun u hu v hv huv => ?_, hlen⟩,
    fun ⟨h, hlen⟩ => ⟨hlen, fun u hu v hv => ?_⟩⟩
  · exact (hrel x.1 u v huv).1 ((h u hu v hv).resolve_left huv)
  · by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ((hrel x.1 u v huv).2 (h hu hv huv))

/-- `verifySubset` is computable in polynomial time whenever the pairwise test `rel` is. -/
@[fun_prop]
theorem computableInPolyTime_verifySubset {rel : Graph → ℕ → ℕ → Bool}
    (hrel : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => rel p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encBool) :
    ComputableInPolyTime (verifySubset rel)
      (encPair (encPair encGraph encNat) encBits) encBool := by
  refine computableInPolyTime_subsetVerifier (encγ := encNat)
    (by unfold encGraph; fun_prop) (bool_and' ?_ ?_)
  · exact ((length_list_binary encNat).comp (snd _ _)).decide_eq' (by fun_prop)
  · apply allWithInput (snd _ _)
    apply allWithInput ((snd _ _).comp (fst _ _))
    have hproj : ComputableInPolyTime
        (fun p : (((Graph × ℕ) × List ℕ) × ℕ) × ℕ => ((p.1.1.1.1, p.1.2), p.2))
        (encPair (encPair (encPair (encPair encGraph encNat) (encList encNat)) encNat) encNat)
        (encPair (encPair encGraph encNat) encNat) := by fun_prop
    exact bool_or.comp ((by fun_prop : ComputableInPolyTime _ _ encBool).prod (hrel.comp hproj))

end Graph

/-! ### Unary blocks -/

/-- The certificate of `N` bits writing the numbers `f a` in unary blocks of width `m`: bit
`m * a + c` is set when `c < f a`. -/
def unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : List Bool :=
  (List.range N).map fun j => decide (j % m < f (j / m))

@[simp]
theorem length_unaryBlocks (m N : ℕ) (f : ℕ → ℕ) : (unaryBlocks m N f).length = N := by
  simp [unaryBlocks]

/-- Counting the set bits of block `a` of `unaryBlocks m N f` reads `f a`, when `f a` fits in the
block and the block fits in the certificate. -/
theorem countP_unaryBlocks {m N a : ℕ} {f : ℕ → ℕ} (hf : f a ≤ m) (hN : m * (a + 1) ≤ N) :
    ((List.range m).countP fun c => (unaryBlocks m N f).getD (m * a + c) false) = f a := by
  have hcount : ∀ k, (List.range k).countP (fun c => decide (c < f a)) = min (f a) k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.range_succ, List.countP_append, ih, List.countP_singleton,
        decide_eq_true_eq]
      split_ifs <;> omega
  rw [← min_eq_left hf, ← hcount]
  refine List.countP_congr fun c hc => ?_
  rw [List.mem_range] at hc
  have hm : 0 < m := by omega
  have hlt : m * a + c < N := by
    calc m * a + c < m * (a + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ N := hN
  have hdiv : (m * a + c) / m = a := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hc, Nat.add_zero]
  have hmod : (m * a + c) % m = c := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  simp only [unaryBlocks, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some, hdiv, hmod]

/-! ### Ordering verification -/

namespace Graph

/-- Executable test that `p` lists every vertex of `V` exactly once and nothing else. -/
def enumeratesBool (V p : List ℕ) : Bool :=
  (V.all fun v => p.any fun u => decide (u = v)) &&
    (p.all fun u => V.any fun v => decide (v = u)) &&
    p.zipIdx.all fun e => decide (p.idxOf e.1 = e.2)

/-- `enumeratesBool V p` holds exactly when `p` lists the members of `V` without repetition. -/
theorem enumeratesBool_eq_true_iff {V p : List ℕ} :
    enumeratesBool V p = true ↔ p.Nodup ∧ ∀ v, v ∈ p ↔ v ∈ V := by
  have hnodup : (∀ e ∈ p.zipIdx, p.idxOf e.1 = e.2) ↔ p.Nodup := by
    constructor
    · intro h
      rw [List.nodup_iff_injective_get]
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [List.get_eq_getElem] at hij
      have hi' : p.idxOf p[i] = i := h (p[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      have hj' : p.idxOf p[j] = j := h (p[j], j) (List.mem_zipIdx_iff_getElem?.2 (by simp))
      rw [hij] at hi'
      exact Fin.ext (hi'.symm.trans hj')
    · intro hnd e he
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 he)
      rw [← heq, hnd.idxOf_getElem]
  simp only [enumeratesBool, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, hnodup]
  constructor
  · rintro ⟨⟨hV, hp⟩, hnd⟩
    refine ⟨hnd, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨u, hu, rfl⟩ := hp v hv
      exact hu
    · obtain ⟨u, hu, rfl⟩ := hV v hv
      exact hu
  · rintro ⟨hnd, hmem⟩
    exact ⟨⟨fun v hv => ⟨v, (hmem v).2 hv, rfl⟩, fun u hu => ⟨u, (hmem u).1 hu, rfl⟩⟩, hnd⟩

/-- The list of vertices described by a certificate `w`, for a vertex list `V` of length `m`: `w`
is read as blocks of `m` bits, one for each distinct vertex of `V`, and the block numbered `a`
names the entry of `V` whose position is its number of set bits, or `0` if there is none. -/
def decodeVertexList (V : List ℕ) (w : List Bool) : List ℕ :=
  (List.range V.dedup.length).map fun a =>
    V.getD ((List.range V.length).countP fun c => w.getD (V.length * a + c) false) 0

/-- Every list of the distinct vertices of `V`, each listed once, is described by a certificate
of length `n ^ 2`, for every `n` at least the length of `V`. -/
theorem exists_decodeVertexList_eq {V p : List ℕ} (hp : p.Nodup) (hpV : ∀ v, v ∈ p ↔ v ∈ V)
    {n : ℕ} (hn : V.length ≤ n) : ∃ w : List Bool, w.length = n ^ 2 ∧ decodeVertexList V w = p := by
  have hlen : p.length = V.dedup.length :=
    ((List.perm_ext_iff_of_nodup hp (List.nodup_dedup V)).2 fun v => by
      rw [List.mem_dedup]
      exact hpV v).length_eq
  have hle : V.dedup.length ≤ V.length := (List.dedup_sublist V).length_le
  refine ⟨unaryBlocks V.length (n ^ 2) fun a => V.idxOf (p.getD a 0), length_unaryBlocks ..,
    List.ext_getElem (by simp [decodeVertexList, hlen]) fun a ha ha' => ?_⟩
  have hidx : V.idxOf p[a] < V.length := List.idxOf_lt_length_iff.2 ((hpV _).1 (List.getElem_mem _))
  have hcount := countP_unaryBlocks (N := n ^ 2) (f := fun a => V.idxOf (p.getD a 0)) (a := a)
    (by rw [List.getD_eq_getElem _ _ ha']; exact hidx.le)
    (calc V.length * (a + 1) ≤ n * n := Nat.mul_le_mul hn (by omega)
      _ = n ^ 2 := (sq n).symm)
  simp only [decodeVertexList, List.getElem_map, List.getElem_range]
  rw [hcount, List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hidx,
    List.getElem_idxOf hidx]

/-- Verify a vertex ordering problem: decode a list of vertices from the certificate
(`decodeVertexList`), check that it lists every vertex of `V x` exactly once, and test it with
`check`. -/
def verifyOrdering {α : Type} (V : α → List ℕ) (check : α → List ℕ → Bool)
    (x : α × List Bool) : Bool :=
  let p := decodeVertexList (V x.1) x.2
  enumeratesBool (V x.1) p && check x.1 p

/-- `verifyOrdering` verifies the existence of an ordering of the vertices satisfying `P`, with
certificates of length `n ^ 2` for instances of encoded length `n`, as long as `check` decides
`P` and the vertex list is not longer than the encoded instance. -/
theorem isVerifier_verifyOrdering {α : Type} {enc : α ↪ List Bool} {V : α → List ℕ}
    {check : α → List ℕ → Bool} {P : α → List ℕ → Prop}
    (hV : ∀ a, (V a).length ≤ (enc a).length) (hcheck : ∀ a p, check a p = true ↔ P a p) :
    IsVerifier enc (Polynomial.X ^ 2) (verifyOrdering V check)
      {a | ∃ p, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ V a) ∧ P a p} := by
  intro a
  simp only [Set.mem_ofPred_eq, Polynomial.eval_pow, Polynomial.eval_X, verifyOrdering,
    Bool.and_eq_true, enumeratesBool_eq_true_iff, hcheck]
  constructor
  · rintro ⟨p, hnd, hmem, hP⟩
    obtain ⟨w, hw, hdec⟩ := exists_decodeVertexList_eq hnd hmem (hV a)
    exact ⟨w, hw, by rw [hdec]; exact ⟨⟨hnd, hmem⟩, hP⟩⟩
  · rintro ⟨w, -, ⟨hnd, hmem⟩, hP⟩
    exact ⟨_, hnd, hmem, hP⟩

/-- Testing whether a list lists every vertex of another exactly once is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_enumeratesBool :
    ComputableInPolyTime (fun x : List ℕ × List ℕ => enumeratesBool x.1 x.2)
      (encPair (encList encNat) (encList encNat)) encBool := by
  unfold enumeratesBool
  fun_prop

/-- Decoding a list of vertices from a certificate is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_decodeVertexList :
    ComputableInPolyTime (fun x : List ℕ × List Bool => decodeVertexList x.1 x.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  have hn : ComputableInPolyTime (fun x : List ℕ × List Bool => x.1.dedup.length)
      (encPair (encList encNat) encBits) encUnary := by
    simp only [← List.card_toFinset, ← length_selectDistinct_replicate]
    have := bitsReplicate true
    exact (length_list encNat).comp (by fun_prop)
  have hblock : ComputableInPolyTime
      (fun q : (List ℕ × List Bool) × ℕ =>
        (List.range q.1.1.length).countP fun c => q.1.2.getD (q.1.1.length * q.2 + c) false)
      (encPair (encPair (encList encNat) encBits) encUnary) encUnary := by
    fun_prop
  unfold decodeVertexList
  fun_prop

/-- `verifyOrdering` is polynomial-time whenever the vertex list and the test `check` are. -/
@[fun_prop]
theorem computableInPolyTime_verifyOrdering {α : Type} {enc : α ↪ List Bool}
    {V : α → List ℕ} {check : α → List ℕ → Bool}
    (hV : ComputableInPolyTime V enc (encList encNat))
    (hcheck : ComputableInPolyTime (fun q : α × List ℕ => check q.1 q.2)
      (encPair enc (encList encNat)) encBool) :
    ComputableInPolyTime (verifyOrdering V check) (encPair enc encBits) encBool := by
  have hV' : ComputableInPolyTime (fun x : α × List Bool => V x.1) (encPair enc encBits)
      (encList encNat) := hV.comp (fst _ _)
  have hp : ComputableInPolyTime (fun x : α × List Bool => decodeVertexList (V x.1) x.2)
      (encPair enc encBits) (encList encNat) :=
    computableInPolyTime_decodeVertexList.comp (hV'.prod (snd _ _))
  exact (computableInPolyTime_enumeratesBool.comp (hV'.prod hp)).bool_and'
    (hcheck.comp ((fst _ _).prod hp))

end Graph

end Cslib.Complexity
