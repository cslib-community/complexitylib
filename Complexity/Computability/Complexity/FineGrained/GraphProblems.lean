/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Reduction
public import Complexity.Computability.Complexity.Problems.Clique
public import Complexity.Computability.Complexity.Problems.Coloring
public import Complexity.Computability.Complexity.Problems.Hamiltonian.Sparse
public import Complexity.Computability.Complexity.Problems.IndependentSet.Sparse
public import Complexity.Computability.Complexity.Problems.VertexCover

/-!
# Exponential lower bounds for graph problems under the exponential time hypothesis

Under the exponential time hypothesis, 3-coloring, independent set, vertex cover and Hamiltonian
paths and cycles, directed or undirected, are not decidable in time `2 ^ o(|V| + |E|)`, and
independent set and clique are not decidable in time `2 ^ o(|V|)` [ImpagliazzoPaturiZane2001]
[CyganEtAl2015, Chapter 14]
[LokshtanovMarxSaurabh2011]. Each follows from a polynomial-time reduction from 3SAT whose graph
has `O(m)` vertices and edges on formulas with `m` clauses
(`Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`), together with the sparsification
lemma, which rules out subexponential time in `m` under the exponential time hypothesis:

* for 3-coloring, the gadget reduction `Cslib.Complexity.SAT.toThreeColoring`, whose graph has at
  most `(24 k + 12) m + 9` vertices and edges on clauses of at most `k` literals
  (`Cslib.Complexity.SAT.length_toThreeColoring_le`);
* for independent set, the reduction with variable edges
  `Cslib.Complexity.SAT.toSparseIndependentSet`, with at most `(k ^ 2 + 5 k) m`
  (`Cslib.Complexity.SAT.length_toSparseIndependentSet_le`). Karp's reduction
  `Cslib.Complexity.SAT.toIndependentSet` has at most `3 m` vertices on formulas with clauses of
  at most three literals, but can have quadratically many edges;
* for vertex cover, the same graph with the complementary target
  (`Cslib.Complexity.IndependentSet.toVertexCover`);
* for clique, the complement of the same graph on its vertices (`Cslib.Complexity.Graph.compl`),
  which has as many vertices but can have quadratically many edges;
* for Hamiltonian paths and cycles, the diamond construction with one slot for each occurrence of
  a variable (`Cslib.Complexity.SAT.toSparseDirHamPath`), with at most `(23 k + 1) m + 1`
  vertices and arcs (`Cslib.Complexity.SAT.length_sparseDiamondGraph_le`), closed into a cycle
  and split into an undirected graph (`Cslib.Complexity.SAT.toSparseHamCycle`); for undirected
  paths, the vertex splitting of the path instance (`Cslib.Complexity.DirHamPath.toHamPath`).
  Sipser's construction `Cslib.Complexity.SAT.toDirHamPath` gives every row a pair of nodes for
  each clause, so it has up to `Θ(m ^ 2)` vertices and arcs.

A graph (`Cslib.Complexity.Graph`) is a list of declared vertices and a list of edges, and the
measures `|V|` and `|E|` are the lengths of these lists. They are at least the numbers of distinct
vertices and edges, so the lower bounds for them imply the lower bounds for the distinct counts
(`Cslib.Complexity.DecidableInSubexpTime.mono_measure`). As for `ETH` itself, time is measured up
to a polynomial in the length of the encoded instance, and a lower bound says: for some `δ > 0`, no
decider runs within time `2 ^ (δ μ)` times a polynomial.

**The hypothesis is refuted.** `Cslib.Complexity.CountingNativeEndpoint.not_ETH` proves that `ETH`
is false, so the `ETH`-conditional lower bounds below hold vacuously. They are kept as conditional
statements; the reductions and size bounds behind them are unconditional.

## Main results

* `Cslib.Complexity.ETH.not_decidableInSubexpTime_ThreeColoring`: no `2 ^ o(|V| + |E|)` algorithm
  for 3-coloring.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_IndependentSet`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_IndependentSet_vertices`: no `2 ^ o(|V| + |E|)`
  and no `2 ^ o(|V|)` algorithm for independent set.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_VertexCover`: no `2 ^ o(|V| + |E|)` algorithm
  for vertex cover.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_Clique`: no `2 ^ o(|V|)` algorithm for clique.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_HamCycle`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_HamPath`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_DirHamCycle`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_DirHamPath`: no `2 ^ o(|V| + |E|)` algorithm
  for Hamiltonian cycles and paths, undirected or directed.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Lower bounds based on the Exponential Time
  Hypothesis*][LokshtanovMarxSaurabh2011]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Lower bounds -/

/-- **No `2 ^ o(|V| + |E|)` algorithm for 3-coloring under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `ThreeColoring` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded graph, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_ThreeColoring (h : ETH) :
    ¬DecidableInSubexpTime ThreeColoring encGraph fun G => G.1.length + G.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toThreeColoring
    -- `(24 * 3 + 12) m + 9 ≤ 93 m + 93`
    (fun φ _ => SAT.toThreeColoring_mem_iff φ) (k := 93) fun φ hφ => by
      have := SAT.length_toThreeColoring_le hφ
      nlinarith

/-- **No `2 ^ o(|V| + |E|)` algorithm for independent set under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `IndependentSet` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded instance, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_IndependentSet (h : ETH) :
    ¬DecidableInSubexpTime IndependentSet (encPair encGraph encNat)
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **No `2 ^ o(|V|)` algorithm for independent set under ETH** [CyganEtAl2015, Chapter 14]: for
some `δ > 0`, `IndependentSet` is not decidable within time `2 ^ (δ |V|)` times any polynomial in
the length of the encoded instance, for graphs with `|V|` declared vertices. -/
theorem ETH.not_decidableInSubexpTime_IndependentSet_vertices (h : ETH) :
    ¬DecidableInSubexpTime IndependentSet (encPair encGraph encNat) fun x => x.1.1.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toSparseIndependentSet
    (fun φ _ => SAT.toSparseIndependentSet_mem_iff φ) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for vertex cover under ETH** [CyganEtAl2015, Chapter 14]:
for some `δ > 0`, `VertexCover` is not decidable within time `2 ^ (δ (|V| + |E|))` times any
polynomial in the length of the encoded instance, for graphs with `|V|` declared vertices and `|E|`
edges. -/
theorem ETH.not_decidableInSubexpTime_VertexCover (h : ETH) :
    ¬DecidableInSubexpTime VertexCover (encPair encGraph encNat)
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction
    (IndependentSet.computableInPolyTime_toVertexCover.comp
      SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => (IndependentSet.toVertexCover_mem_iff _).trans
      (SAT.toSparseIndependentSet_mem_iff φ)) (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Function.comp_apply, IndependentSet.toVertexCover] at this ⊢
      omega

/-- **No `2 ^ o(|V|)` algorithm for clique under ETH** [CyganEtAl2015, Chapter 14]: for some
`δ > 0`, `Clique` is not decidable within time `2 ^ (δ |V|)` times any polynomial in the length of
the encoded instance, for graphs with `|V|` declared vertices. -/
theorem ETH.not_decidableInSubexpTime_Clique (h : ETH) :
    ¬DecidableInSubexpTime Clique (encPair encGraph encNat) fun x => x.1.1.length :=
  h.not_decidableInSubexpTime_of_reduction (f := fun φ =>
      ((SAT.toSparseIndependentSet φ).1.compl, (SAT.toSparseIndependentSet φ).2))
    ((show ComputableInPolyTime (fun x : Graph × ℕ => (x.1.compl, x.2))
      (encPair encGraph encNat) (encPair encGraph encNat) by fun_prop).comp
        SAT.computableInPolyTime_toSparseIndependentSet)
    (fun φ _ => (Graph.compl_mem_Clique_iff _ _).trans (SAT.toSparseIndependentSet_mem_iff φ))
    (k := 24) fun φ hφ => by
      have := SAT.length_toSparseIndependentSet_le hφ
      simp only [Graph.compl] at this ⊢
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for Hamiltonian cycles under ETH** [CyganEtAl2015,
Chapter 14]: for some `δ > 0`, `HamCycle` is not decidable within time `2 ^ (δ (|V| + |E|))` times
any polynomial in the length of the encoded graph, for graphs with `|V|` declared vertices and
`|E|` edges. -/
theorem ETH.not_decidableInSubexpTime_HamCycle (h : ETH) :
    ¬DecidableInSubexpTime HamCycle encGraph fun G => G.1.length + G.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toSparseHamCycle
    (fun φ _ => SAT.toSparseHamCycle_mem_iff φ) (k := 350) fun φ hφ => by
      have := SAT.length_toSparseHamCycle_le hφ
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for directed Hamiltonian cycles under ETH**
[CyganEtAl2015, Chapter 14]: for some `δ > 0`, `DirHamCycle` is not decidable within time
`2 ^ (δ (|V| + |E|))` times any polynomial in the length of the encoded graph, for graphs with
`|V|` declared vertices and `|E|` arcs. -/
theorem ETH.not_decidableInSubexpTime_DirHamCycle (h : ETH) :
    ¬DecidableInSubexpTime DirHamCycle encGraph fun G => G.1.length + G.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toSparseDirHamCycle
    (fun φ _ => SAT.toSparseDirHamCycle_mem_iff φ) (k := 70) fun φ hφ => by
      have := SAT.length_toSparseDirHamCycle_le hφ
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for directed Hamiltonian paths under ETH**
[CyganEtAl2015, Chapter 14]: for some `δ > 0`, `DirHamPath` is not decidable within time
`2 ^ (δ (|V| + |E|))` times any polynomial in the length of the encoded instance, for graphs with
`|V|` declared vertices and `|E|` arcs. -/
theorem ETH.not_decidableInSubexpTime_DirHamPath (h : ETH) :
    ¬DecidableInSubexpTime DirHamPath (encPair encGraph (encPair encNat encNat))
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toSparseDirHamPath
    (fun φ _ => SAT.toSparseDirHamPath_mem_iff φ) (k := 70) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [SAT.toSparseDirHamPath]
      omega

/-- **No `2 ^ o(|V| + |E|)` algorithm for Hamiltonian paths under ETH** [CyganEtAl2015,
Chapter 14]: for some `δ > 0`, `HamPath` is not decidable within time `2 ^ (δ (|V| + |E|))` times
any polynomial in the length of the encoded instance, for graphs with `|V|` declared vertices and
`|E|` edges. -/
theorem ETH.not_decidableInSubexpTime_HamPath (h : ETH) :
    ¬DecidableInSubexpTime HamPath (encPair encGraph (encPair encNat encNat))
      fun x => x.1.1.length + x.1.2.length :=
  h.not_decidableInSubexpTime_of_reduction
    (DirHamPath.computableInPolyTime_toHamPath.comp
      SAT.computableInPolyTime_toSparseDirHamPath)
    (fun φ _ => (DirHamPath.toHamPath_mem_iff _).trans (SAT.toSparseDirHamPath_mem_iff φ))
    (k := 350) fun φ hφ => by
      have := SAT.length_sparseDiamondGraph_le hφ
      simp only [Function.comp_apply, DirHamPath.toHamPath, SAT.toSparseDirHamPath,
        Graph.length_split_fst, Graph.length_split_snd]
      omega

end Cslib.Complexity
