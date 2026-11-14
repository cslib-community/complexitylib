/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

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

* `Cslib.Complexity.CliqueInstance`, `Cslib.Complexity.Clique`, `Cslib.Complexity.Graph.compl`.
* `Cslib.Complexity.Graph.cliqueNum`: the clique number (`G.induced.cliqueNum`).
* `Cslib.Complexity.Clique.verifier`.

## Main results

* `Cslib.Complexity.mem_Clique_iff`: cliques as subsets of `ℕ` contained in the declared vertices.
* `Cslib.Complexity.Graph.induced_compl`, `Cslib.Complexity.Graph.compl_mem_Clique_iff`:
  `G.compl.induced = G.inducedᶜ` and `(G.compl, m) ∈ Clique ↔ (G, m) ∈ IndependentSet`.
* `Cslib.Complexity.Graph.compl_mem_IndependentSet_iff`:
  `(G.compl, m) ∈ IndependentSet ↔ (G, m) ∈ Clique`.
* `Cslib.Complexity.Graph.le_cliqueNum_iff`, `Cslib.Complexity.Graph.cliqueNum_compl`: the clique
  number is the largest target of `Clique`, and that of the complement is the independence number.
* `Cslib.Complexity.Graph.computableInPolyTime_compl`: complementing a graph on its declared
  vertices is polynomial-time.
* `Cslib.Complexity.Clique.mem_NP`: `Clique ∈ NP encCliqueInstance`.
* `Cslib.Complexity.polyTimeReducible_IndependentSet_Clique`,
  `Cslib.Complexity.polyTimeReducible_Clique_IndependentSet`: `IndependentSet` and `Clique` reduce
  to each other in polynomial time.
* `Cslib.Complexity.Clique_npHard`: `Clique` is `NP`-hard.
* `Cslib.Complexity.Clique_npComplete`: `Clique` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- An instance `(graph, m)` of **Clique**. -/
@[ext]
structure CliqueInstance where
  /-- The graph in which to find a clique. -/
  graph : Graph
  /-- The target number of declared vertices. -/
  m : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed `encGraph` followed by binary target `encNat`, encoding `CliqueInstance`. -/
enc_structure encCliqueInstance : CliqueInstance where
  graph : encGraph,
  m : encNat

attribute [fun_prop] encCliqueInstance_graph_polyTime
  encCliqueInstance_m_polyTime encCliqueInstance_mk_polyTime

/-- The graphs with a clique of `m` of their vertices. -/
def Clique : Set CliqueInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices}, x.graph.induced.IsNClique x.m S}

/-- Membership in `Clique` as a finite set of `m` declared vertices that is a clique in
`x.graph.toSimpleGraph`. -/
theorem mem_Clique_iff {x : CliqueInstance} :
    x ∈ Clique ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        x.graph.toSimpleGraph.IsNClique x.m S := by
  simp only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff, SimpleGraph.IsClique]
  exact Graph.exists_subtype_pairwise_iff (P := x.graph.toSimpleGraph.Adj)

@[simp]
theorem mem_Clique_iff_mk {G : Graph} {m : ℕ} :
    (⟨G, m⟩ : CliqueInstance) ∈ Clique ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧ G.toSimpleGraph.IsNClique m S :=
  mem_Clique_iff

namespace Graph

/-- The complement of a graph on its vertices: an edge between any two distinct vertices that are
not adjacent. -/
def compl (G : Graph) : Graph :=
  ⟨G.vertices, G.vertices.flatMap fun u =>
    (G.vertices.filter fun v =>
      decide (u ≠ v ∧ (u, v) ∉ G.edges ∧ (v, u) ∉ G.edges)).map fun v => (u, v)⟩

/-- On the vertices of a graph, adjacency in the complement is non-adjacency in the graph. -/
theorem compl_adj_iff {G : Graph} {u v : ℕ} (hu : u ∈ G.vertices) (hv : v ∈ G.vertices) :
    G.compl.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ¬G.toSimpleGraph.Adj u v := by
  have hedge : ∀ {a b}, (a, b) ∈ G.compl.edges ↔ a ∈ G.vertices ∧ b ∈ G.vertices ∧
      (a ≠ b ∧ (a, b) ∉ G.edges ∧ (b, a) ∉ G.edges) := by
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
    (G.compl.induced : SimpleGraph {v // v ∈ G.vertices}) = G.inducedᶜ := by
  ext u v
  exact (compl_adj_iff (G := G) u.2 v.2).trans
    ((and_congr_left' Subtype.ext_iff.not.symm).trans (G.induced.compl_adj u v).symm)

/-- **Independent sets are cliques of the complement.** -/
theorem compl_mem_Clique_iff (G : Graph) (m : ℕ) :
    (⟨G.compl, m⟩ : CliqueInstance) ∈ Clique ↔
      (⟨G, m⟩ : IndependentSetInstance) ∈ IndependentSet := by
  simp_rw [IndependentSet, Set.mem_ofPred_eq, ← SimpleGraph.isNClique_compl, ← induced_compl]
  rfl

/-- **Cliques are independent sets of the complement.** -/
theorem compl_mem_IndependentSet_iff (G : Graph) (m : ℕ) :
    (⟨G.compl, m⟩ : IndependentSetInstance) ∈ IndependentSet ↔
      (⟨G, m⟩ : CliqueInstance) ∈ Clique := by
  simp_rw [Clique, Set.mem_ofPred_eq, ← SimpleGraph.isNIndepSet_compl, ← induced_compl]
  rfl

/-- Complementing a graph on its declared vertices is polynomial-time with the graph encoding. -/
@[fun_prop]
theorem computableInPolyTime_compl :
    ComputableInPolyTime compl encGraph encGraph := by
  have hne : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide (x.1.2 ≠ x.2))
      (encPair (encPair encGraph encNat) encNat)
      encBool := by
    simpa only [ne_eq, decide_not, Function.comp_def] using
      ComputableInPolyTime.bool_not.comp
        (ComputableInPolyTime.decide_eq' (by fun_prop) (by fun_prop))
  have h1 : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide ((x.1.2, x.2) ∉ x.1.1.edges))
      (encPair (encPair encGraph encNat) encNat)
      encBool := by fun_prop
  have h2 : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ => decide ((x.2, x.1.2) ∉ x.1.1.edges))
      (encPair (encPair encGraph encNat) encNat)
      encBool := by fun_prop
  have hpred : ComputableInPolyTime
      (fun x : (Graph × ℕ) × ℕ =>
        decide (x.1.2 ≠ x.2 ∧ (x.1.2, x.2) ∉ x.1.1.edges ∧ (x.2, x.1.2) ∉ x.1.1.edges))
      (encPair (encPair encGraph encNat) encNat)
      encBool := by
    simpa only [Bool.decide_and, Function.comp_def] using
      ComputableInPolyTime.bool_and.comp
        (hne.prod (ComputableInPolyTime.bool_and.comp (h1.prod h2)))
  have hV : ComputableInPolyTime (fun G : Graph => G.vertices) encGraph (encList encNat) := by
    fun_prop
  have hE : ComputableInPolyTime
      (fun G : Graph => G.vertices.flatMap fun u =>
        (G.vertices.filter fun v =>
          decide (u ≠ v ∧ (u, v) ∉ G.edges ∧ (v, u) ∉ G.edges)).map fun v => (u, v))
      encGraph (encList (encPair encNat encNat)) := by
    exact ComputableInPolyTime.flatMapWithInput (by fun_prop)
      (ComputableInPolyTime.mapWithInput
        (ComputableInPolyTime.filterWithInput (by fun_prop) hpred)
        (by fun_prop))
  unfold compl
  fun_prop

end Graph

namespace Clique

/-- The verifier for `Clique`: select distinct declared vertices from the certificate mask, check
that their count equals `m`, and check that every two distinct selected vertices are adjacent. -/
def verifier : CliqueInstance × List Bool → Bool :=
  fun (x, w) => Graph.verifySubset Graph.adjBool ((x.graph, x.m), w)

/-- `Clique.verifier` verifies `Clique` with certificates as long as the encoded instance. -/
theorem isVerifier :
    IsVerifier encCliqueInstance Polynomial.X verifier Clique := by
  have h := Graph.isVerifier_verifySubset (rel := Graph.adjBool)
    (P := fun G u v => G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Graph.adjBool_eq_true_iff])
  intro x
  have hx := h (x.graph, x.m)
  simp only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, verifier]
  rw [encCliqueInstance_apply]
  exact hx

/-- The `Clique` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier
      (encPair encCliqueInstance encBits) encBool := by
  have h1 : ComputableInPolyTime
      (fun p : CliqueInstance × List Bool => ((p.1.graph, p.1.m), p.2))
      (encPair encCliqueInstance encBits)
      (encPair (encPair encGraph encNat) encBits) := by
    fun_prop
  exact (Graph.computableInPolyTime_verifySubset Graph.computableInPolyTime_adjBool).comp h1

/-- `Clique` belongs to `NP`. -/
theorem mem_NP : Clique ∈ NP encCliqueInstance :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end Clique

/-- Complementing the graph reduces `IndependentSet` to `Clique`. -/
def independentSetToClique (x : IndependentSetInstance) : CliqueInstance :=
  ⟨x.graph.compl, x.m⟩

@[fun_prop]
theorem computableInPolyTime_independentSetToClique :
    ComputableInPolyTime independentSetToClique encIndependentSetInstance encCliqueInstance := by
  unfold independentSetToClique
  fun_prop

theorem independentSetToClique_mem_iff (x : IndependentSetInstance) :
    independentSetToClique x ∈ Clique ↔ x ∈ IndependentSet := by
  obtain ⟨G, m⟩ := x
  exact Graph.compl_mem_Clique_iff G m

/-- Complementing the graph reduces `Clique` to `IndependentSet`. -/
def cliqueToIndependentSet (x : CliqueInstance) : IndependentSetInstance :=
  ⟨x.graph.compl, x.m⟩

@[fun_prop]
theorem computableInPolyTime_cliqueToIndependentSet :
    ComputableInPolyTime cliqueToIndependentSet encCliqueInstance encIndependentSetInstance := by
  unfold cliqueToIndependentSet
  fun_prop

theorem cliqueToIndependentSet_mem_iff (x : CliqueInstance) :
    cliqueToIndependentSet x ∈ IndependentSet ↔ x ∈ Clique := by
  obtain ⟨G, m⟩ := x
  exact Graph.compl_mem_IndependentSet_iff G m

/-- `IndependentSet` reduces to `Clique` in polynomial time by complementing the graph on its
declared vertices. -/
theorem polyTimeReducible_IndependentSet_Clique :
    PolyTimeReducible encIndependentSetInstance encCliqueInstance IndependentSet Clique :=
  ⟨independentSetToClique, computableInPolyTime_independentSetToClique,
    fun x => (independentSetToClique_mem_iff x).symm⟩

/-- `Clique` reduces to `IndependentSet` in polynomial time by complementing the graph on its
declared vertices. -/
theorem polyTimeReducible_Clique_IndependentSet :
    PolyTimeReducible encCliqueInstance encIndependentSetInstance Clique IndependentSet :=
  ⟨cliqueToIndependentSet, computableInPolyTime_cliqueToIndependentSet,
    fun x => (cliqueToIndependentSet_mem_iff x).symm⟩

/-- `Clique` is `NP`-hard. -/
theorem Clique_npHard : NPHard encCliqueInstance Clique :=
  IndependentSet_npHard.trans polyTimeReducible_IndependentSet_Clique

/-- **`Clique` is NP-complete.** -/
theorem Clique_npComplete : NPComplete encCliqueInstance Clique :=
  ⟨Clique.mem_NP, Clique_npHard⟩

/-! ### The clique number -/

namespace Graph

/-- The **clique number** of a graph: the largest number of declared vertices that are pairwise
adjacent. -/
noncomputable def cliqueNum (G : Graph) : ℕ := G.induced.cliqueNum

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of a clique form a clique. -/
theorem mem_Clique_of_le (h : (⟨G, k⟩ : CliqueInstance) ∈ Clique) (hk : k' ≤ k) :
    (⟨G, k'⟩ : CliqueInstance) ∈ Clique := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hk)
  exact ⟨T, hS.subset (Finset.coe_subset.2 hTS), hT⟩

/-- **The clique number is the largest target of `Clique`.** -/
theorem le_cliqueNum_iff : k ≤ G.cliqueNum ↔ (⟨G, k⟩ : CliqueInstance) ∈ Clique :=
  ⟨mem_Clique_of_le G.induced.exists_isNClique_cliqueNum,
    fun ⟨_, hS, (hcard : _ = k)⟩ => hcard ▸ hS.card_le_cliqueNum⟩

/-- A clique has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_Clique (h : (⟨G, k⟩ : CliqueInstance) ∈ Clique) :
    k ≤ G.vertices.toFinset.card :=
  (le_cliqueNum_iff.2 h).trans (G.natCard_vertexSubtype ▸ G.induced.cliqueNum_le_natCard)

/-- **Cliques of the complement are independent sets**: the clique number of the complement on
the declared vertices is the independence number. -/
theorem cliqueNum_compl (G : Graph) : G.compl.cliqueNum = G.indepNum := by
  rw [indepNum, ← G.induced.cliqueNum_compl, ← induced_compl]
  rfl

end Graph

end Cslib.Complexity
