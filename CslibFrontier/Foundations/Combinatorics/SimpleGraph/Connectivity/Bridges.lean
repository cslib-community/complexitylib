/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Connectivity/Bridges.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Spanning subgraphs of bridges

A preconnected spanning subgraph whose edges are all bridges of the ambient graph equals that
graph. An additional ambient edge would close a subgraph path to a cycle containing a bridge.
The statement requires neither finiteness nor a nonempty vertex type.

## Main results

* `SimpleGraph.Preconnected.eq_of_forall_isBridge`: a preconnected spanning subgraph of
  ambient bridges is the entire graph.
-/

public section

namespace SimpleGraph

/-- A preconnected spanning subgraph consisting of bridges of the ambient graph
is the whole ambient graph. No finiteness or nonemptiness hypothesis is needed. -/
theorem Preconnected.eq_of_forall_isBridge
    {V : Type*} {H G : SimpleGraph V}
    (hH : H.Preconnected) (hHG : H ≤ G)
    (hbridge : ∀ e ∈ H.edgeSet, G.IsBridge e) : H = G := by
  classical
  apply le_antisymm hHG
  intro u v huv
  by_contra hnot
  obtain ⟨p, hp⟩ := hH.exists_isPath u v
  have hmiss : s(v, u) ∉ (p.mapLe hHG).edges := by
    rw [Walk.edges_mapLe_eq_edges]
    intro he
    exact hnot (H.mem_edgeSet.mp (p.edges_subset_edgeSet he)).symm
  have hc : (Walk.cons huv.symm (p.mapLe hHG)).IsCycle :=
    Path.cons_isCycle ⟨p.mapLe hHG, hp.mapLe hHG⟩ huv.symm hmiss
  obtain ⟨e, he⟩ := p.edges.exists_mem_of_ne_nil (by
    intro hempty
    exact huv.ne (Walk.Nil.eq (Walk.edges_eq_nil.mp hempty)))
  apply (hbridge e (p.edges_subset_edgeSet he)).notMem_edges_of_isCycle hc
  simp only [Walk.edges_cons, List.mem_cons, Walk.edges_mapLe_eq_edges]
  exact Or.inr he

end SimpleGraph
