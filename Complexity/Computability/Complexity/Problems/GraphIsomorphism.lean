/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Graph isomorphism

`GraphIsomorphism` is the set of pairs of graphs, in the encoding of `IndependentSet`, that are
isomorphic: the simple graphs induced on their declared vertices (`Cslib.Complexity.Graph.induced`)
are isomorphic in the sense of Mathlib's `SimpleGraph.Iso`. Repeated vertex entries are ignored,
and so are edges with an endpoint outside the declared vertices. `GraphNonIsomorphism` is its
complement [Arora and Barak, Section 8.1.3][AroraBarak09].

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
* `Cslib.Complexity.GraphIsomorphism`, `Cslib.Complexity.GraphNonIsomorphism`.
* `Cslib.Complexity.GraphIsomorphism.verifier`.

## Main results

* `Cslib.Complexity.mem_GraphIsomorphism_iff`: isomorphism through positions.
* `Cslib.Complexity.length_distinctVertices_eq_of_mem_GraphIsomorphism`,
  `Cslib.Complexity.mem_GraphIsomorphism_iff_exists_perm`: isomorphic graphs have equally many
  vertices, and are then related by a permutation of positions.
* `Cslib.Complexity.GraphIsomorphism.isVerifier`, `Cslib.Complexity.GraphIsomorphism.mem_NP`:
  `GraphIsomorphism ∈ NP (encPair encGraph encGraph)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace Graph

/-- Adjacency of the vertices at positions `i` and `j` of `G.distinctVertices`. -/
def adjIndex (G : Graph) (i j : ℕ) : Bool :=
  G.adjBool (G.distinctVertices.getD i 0) (G.distinctVertices.getD j 0)

private theorem induced_adj_vertexEquiv (G : Graph) (i j : Fin G.distinctVertices.length) :
    G.induced.Adj (G.vertexEquiv i) (G.vertexEquiv j) ↔ G.adjIndex i j = true := by
  rw [induced_adj, adjIndex, adjBool_eq_true_iff, vertexEquiv_apply, vertexEquiv_apply]

/-- Adjacency of computed positions in a computed graph is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_adjIndex {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    {i j : γ → ℕ} (hG : ComputableInPolyTime G input encGraph)
    (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => (G x).adjIndex (i x) (j x)) input encBool := by
  have hG := hG.tidy
  have hi := hi.tidy
  have hj := hj.tidy
  refine .of_tidy ?_
  have hV := computableInPolyTime_distinctVertices.tidy.comp hG
  exact computableInPolyTime_adjBool.tidy.comp ((hG.prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hi))).prod
    ((listGetD (encA := encNat) 0).comp (hV.prod hj)))

end Graph

/-- The pairs of isomorphic graphs: the graphs induced on the declared vertices are isomorphic
[Arora and Barak, Section 8.1.3][AroraBarak09]. -/
def GraphIsomorphism : Set (Graph × Graph) := {x | Nonempty (x.1.induced ≃g x.2.induced)}

/-- The pairs of non-isomorphic graphs [Arora and Barak, Section 8.1.3][AroraBarak09]. -/
def GraphNonIsomorphism : Set (Graph × Graph) := GraphIsomorphismᶜ

/-- Two graphs are isomorphic exactly when a bijection between the positions of their distinct
vertices preserves adjacency. -/
theorem mem_GraphIsomorphism_iff {x : Graph × Graph} : x ∈ GraphIsomorphism ↔
    ∃ σ : Fin x.1.distinctVertices.length ≃ Fin x.2.distinctVertices.length,
      ∀ i j, x.2.adjIndex (σ i) (σ j) = x.1.adjIndex i j := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨x.1.vertexEquiv.trans (φ.toEquiv.trans x.2.vertexEquiv.symm), fun i j => ?_⟩
    rw [Bool.eq_iff_iff, ← Graph.induced_adj_vertexEquiv, ← Graph.induced_adj_vertexEquiv]
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact φ.map_adj_iff
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨x.1.vertexEquiv.symm.trans (σ.trans x.2.vertexEquiv), fun {u v} => ?_⟩⟩
    obtain ⟨i, rfl⟩ := x.1.vertexEquiv.surjective u
    obtain ⟨j, rfl⟩ := x.1.vertexEquiv.surjective v
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj_vertexEquiv, hσ]

/-- Isomorphic graphs have equally many distinct vertices. -/
theorem length_distinctVertices_eq_of_mem_GraphIsomorphism {G₀ G₁ : Graph}
    (h : (G₀, G₁) ∈ GraphIsomorphism) :
    G₁.distinctVertices.length = G₀.distinctVertices.length := by
  obtain ⟨σ, -⟩ := mem_GraphIsomorphism_iff.1 h
  exact (Fin.equiv_iff_eq.1 ⟨σ⟩).symm

/-- Graphs with equally many distinct vertices are isomorphic exactly when a permutation of the
positions of the first carries its adjacency to the adjacency of the second. -/
theorem mem_GraphIsomorphism_iff_exists_perm {G₀ G₁ : Graph}
    (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
    (G₀, G₁) ∈ GraphIsomorphism ↔ ∃ τ : Equiv.Perm (Fin G₀.distinctVertices.length),
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
def verifier : (Graph × Graph) × List Bool → Bool :=
  Graph.verifyOrdering (fun x => x.2.1) fun x p =>
    decide (p.length = x.1.distinctVertices.length) &&
      (List.range x.1.distinctVertices.length).all fun i =>
        (List.range x.1.distinctVertices.length).all fun j =>
          x.2.adjBool (p.getD i 0) (p.getD j 0) == x.1.adjIndex i j

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encPair encGraph encGraph) encBits) encBool := by
  refine .of_tidy ?_
  have hadj : ∀ {γ : Type} {enc : γ ↪ List Bool} {H : γ → Graph} {u v : γ → ℕ},
      ComputableTidilyInPolyTime H enc encGraph →
      ComputableTidilyInPolyTime u enc encNat →
      ComputableTidilyInPolyTime v enc encNat →
      ComputableTidilyInPolyTime (fun x => (H x).adjBool (u x) (v x)) enc encBool :=
    fun hH hu hv => Graph.computableInPolyTime_adjBool.tidy.comp ((hH.prod hu).prod hv)
  refine (Graph.computableInPolyTime_verifyOrdering (.of_tidy (by unfold encGraph; fun_prop))
    (.of_tidy (bool_and'
      (((length_list encNat).comp (snd _ _)).decide_eq'
        ((length_list encNat).comp (by fun_prop))) ?_))).tidy
  refine allWithInput (by fun_prop) (allWithInput (by fun_prop) ?_)
  exact bool_beq.comp ((hadj (by fun_prop) (by fun_prop) (by fun_prop)).prod
    (Graph.computableInPolyTime_adjIndex (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
      (.of_tidy (by fun_prop))).tidy)

/-- `verifier` is a verifier for `GraphIsomorphism` with certificates whose length is the square
of the length of the encoded pair of graphs. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encGraph) (Polynomial.X ^ 2) verifier GraphIsomorphism := by
  have hmem (x : Graph × Graph) : x ∈ GraphIsomorphism ↔
      ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ x.2.1) ∧
        p.length = x.1.distinctVertices.length ∧
        ∀ i < x.1.distinctVertices.length, ∀ j < x.1.distinctVertices.length,
          x.2.adjBool (p.getD i 0) (p.getD j 0) = x.1.adjIndex i j := by
    obtain ⟨G, H⟩ := x
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
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn, List.getElem_ofFn]
        rw [Bool.eq_iff_iff, H.adjBool_eq_true_iff,
          ← Graph.induced_adj_vertexEquiv G ⟨i, hi⟩ ⟨j, hj⟩]
        exact φ.map_adj_iff
    · rintro ⟨p, hnd, hcov, hlen, hadj⟩
      let e : Fin G.distinctVertices.length ≃ {v // v ∈ H.1} :=
        (finCongr hlen.symm).trans ((hnd.getEquiv _).trans (Equiv.subtypeEquivRight hcov))
      refine ⟨⟨G.vertexEquiv.symm.trans e, fun {u v} => ?_⟩⟩
      obtain ⟨i, rfl⟩ := G.vertexEquiv.surjective u
      obtain ⟨j, rfl⟩ := G.vertexEquiv.surjective v
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [Graph.induced_adj_vertexEquiv, Graph.induced_adj, ← H.adjBool_eq_true_iff,
        ← hadj i i.isLt j j.isLt, List.getD_eq_getElem _ _ (i.isLt.trans_eq hlen.symm),
        List.getD_eq_getElem _ _ (j.isLt.trans_eq hlen.symm)]
      rfl
  have hset : GraphIsomorphism =
      {x : Graph × Graph | ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ x.2.1) ∧
        p.length = x.1.distinctVertices.length ∧
        ∀ i < x.1.distinctVertices.length, ∀ j < x.1.distinctVertices.length,
          x.2.adjBool (p.getD i 0) (p.getD j 0) = x.1.adjIndex i j} :=
    Set.ext hmem
  rw [hset]
  refine Graph.isVerifier_verifyOrdering
    (fun x => x.2.length_vertices_le_encGraph.trans (by simp only [length_encPair]; omega))
    fun x p => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- **`GraphIsomorphism ∈ NP`.** -/
theorem mem_NP : GraphIsomorphism ∈ NP (encPair encGraph encGraph) :=
  ⟨Polynomial.X ^ 2, verifier, computableInPolyTime_verifier, isVerifier⟩

end GraphIsomorphism

end Cslib.Complexity
