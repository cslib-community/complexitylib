/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Sym.Card

/-!
# Graphs encoded by edge bits

A simple graph on `n` labelled vertices is encoded by one Boolean coordinate for each unordered
pair of distinct vertices. `edgeEquiv` numbers these coordinates without changing the layout
formerly used by the clique function. The common encoding supports graph properties such as
clique containment and connectivity without importing either application.

## Main definitions

* `Cslib.BitString.Graph.Edge`, `edgeCount`, `edgeEquiv`: the possible edges and their numbering.
* `Cslib.BitString.Graph.graph`, `ofGraph`: graph/edge-word conversion.

## Main results

* `Cslib.BitString.Graph.edgeCount_eq_choose`: the coordinate count is `n.choose 2`.
* `Cslib.BitString.Graph.graph_adj`: adjacency is the corresponding edge bit.
* `Cslib.BitString.Graph.graph_ofGraph`, `ofGraph_graph`: both conversions are inverse.

The encoding and its original lemmas were extracted from Samuel Schlesinger's clique module.
-/

public section

namespace Cslib.BitString.Graph

variable {n : ℕ}

/-- The possible edges of a graph on `n` vertices: unordered pairs of distinct vertices. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- The number of possible edges of a graph on `n` vertices. -/
abbrev edgeCount (n : ℕ) : ℕ := Fintype.card (Edge n)

/-- A graph on `n` vertices has `n.choose 2` possible edges. -/
theorem edgeCount_eq_choose (n : ℕ) : edgeCount n = n.choose 2 := by
  rw [edgeCount, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- A numbering of the possible edges by the inputs of a circuit. -/
noncomputable def edgeEquiv (n : ℕ) : Edge n ≃ Fin (edgeCount n) := Fintype.equivFin _

/-- The graph of an input: its edges are the possible edges set to `true`. -/
@[expose] def graph (x : Fin (edgeCount n) → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬e.IsDiag, x (edgeEquiv n ⟨e, h⟩) = true}

/-- The edge between two distinct vertices. -/
@[expose] def edge {u v : Fin n} (h : u ≠ v) : Edge n := ⟨s(u, v), by simpa using h⟩

/-- The endpoints of `edge h` are `{u, v}`. -/
@[simp] theorem toFinset_edge {u v : Fin n} (h : u ≠ v) : (edge h).1.toFinset = {u, v} :=
  Sym2.toFinset_mk_eq

/-- The edge between `u` and `v` is the edge between `v` and `u`. -/
theorem edge_comm {u v : Fin n} (h : u ≠ v) : edge h = edge (Ne.symm h) :=
  Subtype.ext Sym2.eq_swap

/-- Two distinct vertices are adjacent in the graph of an input exactly when the input sets the
edge between them. -/
theorem graph_adj {x : Fin (edgeCount n) → Bool} {u v : Fin n} (h : u ≠ v) :
    (graph x).Adj u v ↔ x (edgeEquiv n (edge h)) = true := by
  rw [graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨fun ⟨⟨_, hx⟩, _⟩ => hx, fun hx => ⟨⟨_, hx⟩, h⟩⟩

/-- A possible edge belongs to the encoded graph exactly when its bit is set. -/
@[simp] theorem mem_edgeSet_graph (x : Fin (edgeCount n) → Bool) (e : Edge n) :
    e.1 ∈ (graph x).edgeSet ↔ x (edgeEquiv n e) = true := by
  simp [graph, SimpleGraph.edgeSet_fromEdgeSet, e.property]

/-- Distinct edge words encode distinct graphs. -/
theorem graph_injective : Function.Injective (graph (n := n)) := by
  intro x y h
  funext i
  have hi : x i = true ↔ y i = true := by
    simpa only [Equiv.apply_symm_apply] using
      (mem_edgeSet_graph x ((edgeEquiv n).symm i)).symm.trans
        ((congrArg (fun G : SimpleGraph (Fin n) =>
          ((edgeEquiv n).symm i).1 ∈ G.edgeSet) h).to_iff.trans
          (mem_edgeSet_graph y ((edgeEquiv n).symm i)))
  cases hx : x i <;> cases hy : y i <;> simp_all

/-- Setting more edge bits preserves graph inclusion. -/
theorem graph_mono {x y : Fin (edgeCount n) → Bool}
    (h : ∀ i, x i = true → y i = true) : graph x ≤ graph y := by
  intro u v huv
  exact (graph_adj huv.ne).2 (h _ ((graph_adj huv.ne).1 huv))

@[simp] theorem graph_false : graph (n := n) (fun _ => false) = ⊥ := by
  ext u v
  by_cases h : u = v
  · subst v; simp
  · simp [graph_adj h]

@[simp] theorem graph_true : graph (n := n) (fun _ => true) = ⊤ := by
  ext u v
  by_cases h : u = v
  · subst v; simp
  · simp [graph_adj h, h]

/-- Clearing a coordinate deletes precisely that edge. -/
theorem graph_update_false (x : Fin (edgeCount n) → Bool) (i : Fin (edgeCount n)) :
    graph (Function.update x i false) =
      (graph x).deleteEdges {((edgeEquiv n).symm i).1} := by
  apply SimpleGraph.edgeSet_injective
  ext e
  by_cases he : e.IsDiag
  · simp [he]
  · rw [mem_edgeSet_graph _ ⟨e, he⟩, SimpleGraph.edgeSet_deleteEdges]
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, mem_edgeSet_graph x ⟨e, he⟩]
    by_cases hi : edgeEquiv n ⟨e, he⟩ = i
    · have hei : e = ((edgeEquiv n).symm i).1 :=
        congrArg Subtype.val ((edgeEquiv n).injective (hi.trans (Equiv.apply_symm_apply _ _).symm))
      simp [hei]
    · have hei : e ≠ ((edgeEquiv n).symm i).1 := by
        intro hh
        apply hi
        rw [show (⟨e, he⟩ : Edge n) = (edgeEquiv n).symm i from Subtype.ext hh,
          Equiv.apply_symm_apply]
      simp [hi, hei]

/-- The edge word of a labelled simple graph, in the same numbering as `graph`. -/
noncomputable def ofGraph (G : SimpleGraph (Fin n)) : BitString (edgeCount n) :=
  fun i => @decide (((edgeEquiv n).symm i).1 ∈ G.edgeSet) (Classical.propDecidable _)

/-- Encoding a graph and reading its edge word recovers the graph. -/
@[simp] theorem graph_ofGraph (G : SimpleGraph (Fin n)) : graph (ofGraph G) = G := by
  ext u v
  by_cases huv : u = v
  · subst v; simp
  · rw [graph_adj huv]
    simp only [ofGraph, Equiv.symm_apply_apply, decide_eq_true_eq]
    exact G.mem_edgeSet

/-- Encoding an edge word's graph recovers the edge word. -/
@[simp] theorem ofGraph_graph (x : BitString (edgeCount n)) : ofGraph (graph x) = x :=
  graph_injective (graph_ofGraph (graph x))

end Cslib.BitString.Graph
