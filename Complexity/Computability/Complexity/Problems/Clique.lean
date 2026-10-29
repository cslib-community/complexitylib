/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.IndependentSet
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Cliques

`Clique` is the set of graphs with a clique of a given number of their vertices [Arora and Barak,
Section 2.4][AroraBarak09]. A set of vertices is independent in a graph exactly when it is a clique
in the complement of the graph on its vertices (`Graph.compl`), so complementing the graph reduces
`IndependentSet` to `Clique` [Karp1972]. The verifier is `Cslib.Complexity.Graph.verifySubset` for
adjacency, an instance of the subset-witness verifier `Cslib.Complexity.subsetVerifier`.

The same problem as a class of finite structures, closed under isomorphism and without an
encoding, with the target size given by a unary relation, is
`Cslib.Logic.FO.sizedGraph.Clique`. There loops are ignored, edges need not be symmetric,
and the reductions between independent set, clique and vertex cover are quantifier-free
first-order interpretations.

## Main definitions

* `Cslib.Complexity.Clique`, `Cslib.Complexity.Graph.compl`.
* `Cslib.Complexity.Graph.cliqueNum`: the clique number (`G.induced.cliqueNum`).
* `Cslib.Complexity.Clique.verifier`.

## Main results

* `Cslib.Complexity.mem_Clique_iff`: cliques as subsets of `ℕ` contained in the declared vertices.
* `Cslib.Complexity.Graph.induced_compl`, `Cslib.Complexity.Graph.compl_mem_Clique_iff`:
  `G.compl.induced = G.inducedᶜ` and `(G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet`.
* `Cslib.Complexity.Graph.le_cliqueNum_iff`, `Cslib.Complexity.Graph.cliqueNum_compl`: the clique
  number is the largest target of `Clique`, and that of the complement is the independence number.
* `Cslib.Complexity.Graph.computableInPolyTime_compl`: complementing a graph on its declared
  vertices is polynomial-time.
* `Cslib.Complexity.Clique.mem_NP`: `Clique ∈ NP (encPair encGraph encNat)`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_Clique`: `IndependentSet` reduces to `Clique`
  in polynomial time.
* `Cslib.Complexity.Clique_npHard`: `Clique` is `NP`-hard.
* `Cslib.Complexity.Clique_npComplete`: `Clique` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The graphs with a clique of `m` of their vertices. -/
def Clique : Set (Graph × ℕ) :=
  {x | ∃ S : Finset {v // v ∈ x.1.1}, x.1.induced.IsNClique x.2 S}

/-- Membership in `Clique` as a finite set of `m` declared vertices that is a clique in
`G.toSimpleGraph`. -/
theorem mem_Clique_iff {G : Graph} {m : ℕ} :
    (G, m) ∈ Clique ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧ G.toSimpleGraph.IsNClique m S := by
  simp only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff, SimpleGraph.IsClique]
  exact Graph.exists_subtype_pairwise_iff (P := G.toSimpleGraph.Adj)

namespace Graph

/-- The complement of a graph on its vertices: an edge between any two distinct vertices that are
not adjacent. -/
def compl (G : Graph) : Graph :=
  (G.1, G.1.flatMap fun u =>
    (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map fun v => (u, v))

/-- On the vertices of a graph, adjacency in the complement is non-adjacency in the graph. -/
theorem compl_adj_iff {G : Graph} {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    G.compl.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ¬G.toSimpleGraph.Adj u v := by
  have hedge : ∀ {a b}, (a, b) ∈ G.compl.2 ↔ a ∈ G.1 ∧ b ∈ G.1 ∧
      (a ≠ b ∧ (a, b) ∉ G.2 ∧ (b, a) ∉ G.2) := by
    intro a b
    simp only [compl, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a', ha', b', ⟨hb', hne⟩, rfl, rfl⟩
      exact ⟨ha', hb', hne⟩
    · rintro ⟨ha, hb, hne⟩
      exact ⟨a, ha, b, ⟨hb, hne⟩, rfl, rfl⟩
  simp only [toSimpleGraph_adj, ne_eq, hedge]
  constructor
  · rintro ⟨huv, ⟨-, -, -, h₁, h₂⟩ | ⟨-, -, -, h₁, h₂⟩⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₁ h₂⟩
    · exact ⟨huv, fun ⟨_, h⟩ => h.elim h₂ h₁⟩
  · rintro ⟨huv, h⟩
    refine ⟨huv, Or.inl ⟨hu, hv, huv, fun h₁ => h ⟨huv, Or.inl h₁⟩, fun h₂ => h ⟨huv, Or.inr h₂⟩⟩⟩

/-- The induced graph of the complement is the complement of the induced graph. -/
@[simp]
theorem induced_compl (G : Graph) :
    (G.compl.induced : SimpleGraph {v // v ∈ G.1}) = G.inducedᶜ := by
  ext u v
  exact (compl_adj_iff (G := G) u.2 v.2).trans
    ((and_congr_left' Subtype.ext_iff.not.symm).trans (G.induced.compl_adj u v).symm)

/-- **Independent sets are cliques of the complement.** -/
theorem compl_mem_Clique_iff (G : Graph) (m : ℕ) :
    (G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet := by
  simp_rw [IndependentSet, Set.mem_ofPred_eq, ← SimpleGraph.isNClique_compl, ← induced_compl]
  rfl

/-- Complementing a graph on its declared vertices is polynomial-time with the graph encoding. -/
@[fun_prop]
theorem computableInPolyTime_compl :
    ComputableInPolyTime compl encGraph encGraph := by
  unfold compl encGraph
  have hne : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide (x.1.2 ≠ x.2))
      (encPair (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encNat)
      encBool := by
    simpa only [ne_eq, decide_not, Function.comp_def] using
      ComputableInPolyTime.bool_not.comp
        (ComputableInPolyTime.decide_eq' (by fun_prop) (by fun_prop))
  have h1 : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide ((x.1.2, x.2) ∉ x.1.1.2))
      (encPair (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encNat)
      encBool := by fun_prop
  have h2 : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide ((x.2, x.1.2) ∉ x.1.1.2))
      (encPair (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encNat)
      encBool := by fun_prop
  have hpred : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ =>
        decide (x.1.2 ≠ x.2 ∧ (x.1.2, x.2) ∉ x.1.1.2 ∧ (x.2, x.1.2) ∉ x.1.1.2))
      (encPair (encPair (encPair (encList encNat) (encList (encPair encNat encNat))) encNat) encNat)
      encBool := by
    simpa only [Bool.decide_and, Function.comp_def] using
      ComputableInPolyTime.bool_and.comp
        (hne.prod (ComputableInPolyTime.bool_and.comp (h1.prod h2)))
  exact (ComputableInPolyTime.fst _ _).prod
    (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.mapWithInput
        (ComputableInPolyTime.filterWithInput
          ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)) hpred)
        (by fun_prop)))

/-- Complementing a graph on its declared vertices is polynomial-time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_compl :
    ComputableTidilyInPolyTime compl encGraph encGraph :=
  computableInPolyTime_compl.tidy

end Graph

namespace Clique

/-- The verifier for `Clique`: select distinct declared vertices from the certificate mask, check
that their count equals `m`, and check that every two distinct selected vertices are adjacent. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  Graph.verifySubset Graph.adjBool

/-- `Clique.verifier` verifies `Clique` with certificates as long as the encoded instance. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) Polynomial.X verifier Clique := by
  have h := Graph.isVerifier_verifySubset (rel := Graph.adjBool)
    (P := fun G u v => G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Graph.adjBool_eq_true_iff])
  intro x
  simp only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, verifier]
  exact h x

/-- The `Clique` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier
      (encPair (encPair encGraph encNat) encBits) encBool :=
  Graph.computableInPolyTime_verifySubset Graph.computableInPolyTime_adjBool

/-- `Clique` belongs to `NP`. -/
theorem mem_NP : Clique ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, verifier, by fun_prop, isVerifier⟩

end Clique

/-- `IndependentSet` reduces to `Clique` in polynomial time by complementing the graph on its
declared vertices. -/
theorem polyTimeReducible_IndependentSet_Clique :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet Clique :=
  ⟨fun x => (x.1.compl, x.2), by fun_prop, fun ⟨G, m⟩ => (Graph.compl_mem_Clique_iff G m).symm⟩

/-- `Clique` is `NP`-hard. -/
theorem Clique_npHard : NPHard (encPair encGraph encNat) Clique :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_Clique

/-- **`Clique` is NP-complete.** -/
theorem Clique_npComplete : NPComplete (encPair encGraph encNat) Clique :=
  ⟨Clique.mem_NP, Clique_npHard⟩

/-! ### The clique number -/

namespace Graph

/-- The **clique number** of a graph: the largest number of declared vertices that are pairwise
adjacent. -/
noncomputable def cliqueNum (G : Graph) : ℕ := G.induced.cliqueNum

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of a clique form a clique. -/
theorem mem_Clique_of_le (h : (G, k) ∈ Clique) (hk : k' ≤ k) : (G, k') ∈ Clique := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hk)
  exact ⟨T, hS.subset (Finset.coe_subset.2 hTS), hT⟩

/-- **The clique number is the largest target of `Clique`.** -/
theorem le_cliqueNum_iff : k ≤ G.cliqueNum ↔ (G, k) ∈ Clique :=
  ⟨mem_Clique_of_le G.induced.exists_isNClique_cliqueNum,
    fun ⟨_, hS, (hcard : _ = k)⟩ => hcard ▸ hS.card_le_cliqueNum⟩

/-- A clique has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_Clique (h : (G, k) ∈ Clique) : k ≤ G.1.toFinset.card :=
  (le_cliqueNum_iff.2 h).trans (G.natCard_vertexSubtype ▸ G.induced.cliqueNum_le_natCard)

/-- **Cliques of the complement are independent sets**: the clique number of the complement on
the declared vertices is the independence number. -/
theorem cliqueNum_compl (G : Graph) : G.compl.cliqueNum = G.indepNum := by
  rw [indepNum, ← G.induced.cliqueNum_compl, ← induced_compl]
  rfl

end Graph

end Cslib.Complexity
