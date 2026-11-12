/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Graph isomorphism

`GraphIsomorphism` is the set of pairs of graphs (`Cslib.Complexity.GraphIsomorphismInstance`,
encoded by `Cslib.Complexity.encGraphIsomorphism`), that are isomorphic: the simple graphs
induced on their declared vertices (`Cslib.Complexity.Graph.induced`) are isomorphic in the sense
of Mathlib's `SimpleGraph.Iso`. Repeated vertex entries are ignored, and so are edges with an
endpoint outside the declared vertices. `GraphNonIsomorphism` is its complement
[Arora and Barak, Section 8.1.3][AroraBarak09].

Positions in the list `Graph.distinctVertices` of declared vertices without repetitions enumerate
the vertices (`Cslib.Complexity.Graph.vertexEquiv`), and `Graph.adjIndex` reads adjacency through
positions. Two graphs are isomorphic exactly when a bijection of positions preserves `adjIndex`
(`mem_GraphIsomorphism_iff`).

`GraphIsomorphism ∈ NP`: a certificate encodes an ordering of the second graph's declared vertices
in unary blocks (`Cslib.Complexity.Graph.decodeVertexList`), and the verifier checks that it lists
every declared vertex of the second graph once (`Cslib.Complexity.Graph.verifyOrdering`), has as
many vertices as the first graph, and preserves adjacency.

## Main definitions

* `Cslib.Complexity.Graph.adjIndex`.
* `Cslib.Complexity.GraphIsomorphismInstance`, `Cslib.Complexity.encGraphIsomorphism`.
* `Cslib.Complexity.GraphIsomorphism`, `Cslib.Complexity.GraphNonIsomorphism`.
* `Cslib.Complexity.GraphIsomorphism.verifier`.

## Main results

* `Cslib.Complexity.mem_GraphIsomorphism_iff`: isomorphism through positions.
* `Cslib.Complexity.length_distinctVertices_eq_of_mem_GraphIsomorphism`,
  `Cslib.Complexity.mem_GraphIsomorphism_iff_exists_perm`: isomorphic graphs have equally many
  vertices, and are then related by a permutation of positions.
* `Cslib.Complexity.GraphIsomorphism.isVerifier`, `Cslib.Complexity.GraphIsomorphism.mem_NP`:
  `GraphIsomorphism ∈ NP encGraphIsomorphism`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace Graph

/-- Adjacency of the vertices at positions `i` and `j` of `G.distinctVertices`. -/
@[expose]
def adjIndex (G : Graph) (i j : ℕ) : Bool :=
  G.adjBool (G.distinctVertices.getD i 0) (G.distinctVertices.getD j 0)

theorem induced_adj_vertexEquiv (G : Graph) (i j : Fin G.distinctVertices.length) :
    G.induced.Adj (G.vertexEquiv i) (G.vertexEquiv j) ↔ G.adjIndex i j = true := by
  rw [induced_adj, adjIndex, adjBool_eq_true_iff, vertexEquiv_apply, vertexEquiv_apply]

/-- Adjacency of computed positions in a computed graph is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_adjIndex {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    {i j : γ → ℕ} (hG : ComputableInPolyTime G input encGraph)
    (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => (G x).adjIndex (i x) (j x)) input encBool := by
  have hV := computableInPolyTime_distinctVertices.comp hG
  exact computableInPolyTime_adjBool.comp ((hG.prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hi))).prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hj)))

end Graph

/-- An instance `(first, second)` of **Graph Isomorphism** and **Graph Non-Isomorphism**. -/
@[ext]
structure GraphIsomorphismInstance where
  /-- The first graph in the pair. -/
  first : Graph
  /-- The second graph in the pair. -/
  second : Graph
  deriving DecidableEq, Repr

/-- Encoding of `GraphIsomorphismInstance` as a pair `(first, second)`. -/
enc_structure encGraphIsomorphism : GraphIsomorphismInstance where
  first : encGraph,
  second : encGraph

attribute [fun_prop] encGraphIsomorphism_first_polyTime encGraphIsomorphism_second_polyTime
  encGraphIsomorphism_mk_polyTime

/-- The pairs of isomorphic graphs: the graphs induced on the declared vertices are isomorphic
[Arora and Barak, Section 8.1.3][AroraBarak09]. -/
@[expose]
def GraphIsomorphism : Set GraphIsomorphismInstance :=
  {x | Nonempty (x.first.induced ≃g x.second.induced)}

/-- The pairs of non-isomorphic graphs [Arora and Barak, Section 8.1.3][AroraBarak09]. -/
@[expose]
def GraphNonIsomorphism : Set GraphIsomorphismInstance := GraphIsomorphismᶜ

/-- Two graphs are isomorphic exactly when a bijection between the positions of their distinct
vertices preserves adjacency. -/
theorem mem_GraphIsomorphism_iff {x : GraphIsomorphismInstance} : x ∈ GraphIsomorphism ↔
    ∃ σ : Fin x.first.distinctVertices.length ≃ Fin x.second.distinctVertices.length,
      ∀ i j, x.second.adjIndex (σ i) (σ j) = x.first.adjIndex i j := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨x.first.vertexEquiv.trans (φ.toEquiv.trans x.second.vertexEquiv.symm), fun i j => ?_⟩
    rw [Bool.eq_iff_iff, ← Graph.induced_adj_vertexEquiv, ← Graph.induced_adj_vertexEquiv]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact φ.map_adj_iff
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨x.first.vertexEquiv.symm.trans (σ.trans x.second.vertexEquiv), fun {u v} => ?_⟩⟩
    obtain ⟨i, rfl⟩ := x.first.vertexEquiv.surjective u
    obtain ⟨j, rfl⟩ := x.first.vertexEquiv.surjective v
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj_vertexEquiv, hσ]

/-- Isomorphic graphs have equally many distinct vertices. -/
theorem length_distinctVertices_eq_of_mem_GraphIsomorphism {G₀ G₁ : Graph}
    (h : (⟨G₀, G₁⟩ : GraphIsomorphismInstance) ∈ GraphIsomorphism) :
    G₁.distinctVertices.length = G₀.distinctVertices.length := by
  obtain ⟨σ, -⟩ := mem_GraphIsomorphism_iff.1 h
  exact (Fin.equiv_iff_eq.1 ⟨σ⟩).symm

/-- Graphs with equally many distinct vertices are isomorphic exactly when a permutation of the
positions of the first carries its adjacency to the adjacency of the second. -/
theorem mem_GraphIsomorphism_iff_exists_perm {G₀ G₁ : Graph}
    (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
    (⟨G₀, G₁⟩ : GraphIsomorphismInstance) ∈ GraphIsomorphism ↔
      ∃ τ : Equiv.Perm (Fin G₀.distinctVertices.length),
        ∀ i j, G₁.adjIndex (τ i) (τ j) = G₀.adjIndex i j := by
  rw [mem_GraphIsomorphism_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.trans (finCongr h), fun i j => hσ i j⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ.trans (finCongr h.symm), fun i j => hτ i j⟩

namespace GraphIsomorphism

/-! ### Verification -/

/-- Accept a certificate when the decoded ordering of the second graph's declared vertices has as
many vertices as the first graph and preserves adjacency. -/
@[expose]
def verifier : GraphIsomorphismInstance × List Bool → Bool :=
  Graph.verifyOrdering (fun x => x.second.vertices) fun x p =>
    decide (p.length = x.first.distinctVertices.length) &&
      (List.range x.first.distinctVertices.length).all fun i =>
        (List.range x.first.distinctVertices.length).all fun j =>
          x.second.adjBool (p.getD i 0) (p.getD j 0) == x.first.adjIndex i j

/-- The verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encGraphIsomorphism encBits) encBool := by
  have hlen : ComputableInPolyTime
      (fun x : GraphIsomorphismInstance × List ℕ => x.1.first.distinctVertices.length)
      (encPair encGraphIsomorphism (encList encNat)) encUnary :=
    (length_list encNat).comp (by fun_prop)
  refine Graph.computableInPolyTime_verifyOrdering (by fun_prop)
    (bool_and' (((length_list encNat).comp (snd _ _)).decide_eq' hlen) ?_)
  refine allWithInput (range.comp hlen)
    (allWithInput (range.comp (hlen.comp (fst _ _))) ?_)
  exact (Graph.computableInPolyTime_adjBool_comp (by fun_prop) (by fun_prop) (by fun_prop)).beq
    (Graph.computableInPolyTime_adjIndex (by fun_prop) (by fun_prop) (by fun_prop))

/-- `verifier` is a verifier for `GraphIsomorphism` with certificates whose length is the square
of the length of the encoded pair of graphs. -/
theorem isVerifier :
    IsVerifier encGraphIsomorphism (Polynomial.X ^ 2) verifier GraphIsomorphism := by
  have hset : GraphIsomorphism =
      {x : GraphIsomorphismInstance | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ x.second.vertices) ∧
        p.length = x.first.distinctVertices.length ∧
        ∀ i < x.first.distinctVertices.length, ∀ j < x.first.distinctVertices.length,
          x.second.adjBool (p.getD i 0) (p.getD j 0) = x.first.adjIndex i j} := by
    ext ⟨G, H⟩
    rw [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨φ⟩
      let f : Fin G.distinctVertices.length → ℕ := fun i => φ (G.vertexEquiv i)
      have hf : Function.Injective f :=
        Subtype.val_injective.comp (φ.injective.comp G.vertexEquiv.injective)
      refine ⟨List.ofFn f, List.nodup_ofFn.2 hf, fun v => ⟨?_, ?_⟩, List.length_ofFn,
        fun i hi j hj => ?_⟩
      · rintro hv
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
        exact (φ (G.vertexEquiv i)).2
      · intro hv
        exact List.mem_ofFn.2 ⟨G.vertexEquiv.symm (φ.symm ⟨v, hv⟩), by simp [f]⟩
      · rw [List.getD_ofFn_of_lt _ hi, List.getD_ofFn_of_lt _ hj]
        rw [Bool.eq_iff_iff, H.adjBool_eq_true_iff,
          ← Graph.induced_adj_vertexEquiv G ⟨i, hi⟩ ⟨j, hj⟩]
        exact φ.map_adj_iff
    · rintro ⟨p, hnd, hcov, hlen, hadj⟩
      let e : Fin G.distinctVertices.length ≃ {v // v ∈ H.vertices} :=
        (finCongr hlen.symm).trans ((hnd.getEquiv _).trans (Equiv.subtypeEquivRight hcov))
      refine ⟨⟨G.vertexEquiv.symm.trans e, fun {u v} => ?_⟩⟩
      obtain ⟨i, rfl⟩ := G.vertexEquiv.surjective u
      obtain ⟨j, rfl⟩ := G.vertexEquiv.surjective v
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj, ← H.adjBool_eq_true_iff,
        ← hadj i i.isLt j j.isLt, List.getD_eq_getElem _ _ (i.isLt.trans_eq hlen.symm),
        List.getD_eq_getElem _ _ (j.isLt.trans_eq hlen.symm)]
      rfl
  rw [hset]
  refine Graph.isVerifier_verifyOrdering (fun x => x.second.length_vertices_le_encGraph.trans
      (by simp only [encGraphIsomorphism_apply, length_encPair]; omega))
    fun x p => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]

/-- **`GraphIsomorphism ∈ NP`.** -/
theorem mem_NP : GraphIsomorphism ∈ NP encGraphIsomorphism :=
  ⟨Polynomial.X ^ 2, verifier, computableInPolyTime_verifier, isVerifier⟩

end GraphIsomorphism

end Cslib.Complexity
