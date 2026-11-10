/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat

/-!
# Finite multigraphs given by their ends

A multigraph on the vertices `V` with edges `E`, parallel edges and self-loops allowed, is given
here by the map `ends : E → Sym2 V` sending each edge to its unordered pair of ends; a self-loop
has equal ends. Assignments of values to the edges are then functions on `E`, as in Tseitin
formulas (`Cslib.Logic.PL.CNF.tseitinFormula`), and relabelling the edges along an
equivalence changes none of the quantities below (`Multigraph.card_incidence_comp`,
`Multigraph.minBalancedCut_comp`, ...).

The multigraph is connected when its underlying simple graph (`Multigraph.toSimpleGraph`) is, that
is, exactly when it has a vertex and an edge leaves every nonempty set of vertices other than the
set of all vertices
(`Multigraph.connected_toSimpleGraph_iff`). The least number of edges between a set of between a
third and two thirds of the vertices and its complement (`Multigraph.minBalancedCut`) is the
*expansion* `e(G)` of [Ben-Sasson and Wigderson][BenSassonWigderson2001], which bounds the width
of resolution refutations of Tseitin formulas.

## Main definitions

* `Cslib.Multigraph.toGraph`: the multigraph as a Mathlib `Graph`.
* `Cslib.Multigraph.toSimpleGraph`: the simple graph underlying a multigraph.
* `Cslib.Multigraph.incidence`: the edges at a vertex other than self-loops.
* `Cslib.Multigraph.edgeCut`: the edges between a set of vertices and its complement.
* `Cslib.Multigraph.minBalancedCut`: the expansion `e(G)` of Ben-Sasson and Wigderson.

## Main results

* `Cslib.Multigraph.incidenceSet_toGraph`, `Cslib.Multigraph.coe_edgeCut_eq_toGraph_edgeCut`:
  incidence sets and edge cuts match those of Mathlib's `Graph`.
* `Cslib.Multigraph.coe_incidence_eq_incidenceSet_toGraph`: the edges at a vertex other than
  self-loops are the non-loop incident edges of `toGraph ends`.
* `Cslib.Multigraph.edgeSet_toSimpleGraph`: the edges of the underlying simple graph.
* `Cslib.Multigraph.connected_toSimpleGraph_iff`: connectivity as a cut condition.
* `Cslib.Multigraph.le_minBalancedCut_iff`: the characterization of `e(G)`.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
-/

@[expose] public section

namespace Cslib.Multigraph

open Finset

variable {V E E' : Type*} (ends : E → Sym2 V)

/-- A multigraph given by `ends : E → Sym2 V` as a Mathlib `Graph` whose vertex set and edge set
are everything. -/
def toGraph : Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := ends e = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ h => h.trans Sym2.eq_swap⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    rcases Sym2.eq_iff.mp (h.symm.trans h') with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e :=
    iff_of_true (Set.mem_univ e) (by obtain ⟨x, y⟩ := ends e; exact ⟨x, y, rfl⟩)
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

variable {ends} in
/-- An edge `e` links `x` and `y` in `toGraph ends` iff its unordered endpoints are `s(x, y)`. -/
@[simp] theorem toGraph_isLink {e : E} {x y : V} :
    (toGraph ends).IsLink e x y ↔ ends e = s(x, y) :=
  Iff.rfl

/-- The incident edges of `v` in `toGraph ends` are those having `v` as an endpoint. -/
@[simp] theorem incidenceSet_toGraph (v : V) :
    (toGraph ends).incidenceSet v = {e | v ∈ ends e} := by
  ext e
  obtain ⟨x, y, he⟩ : ∃ x y, ends e = s(x, y) := by obtain ⟨x, y⟩ := ends e; exact ⟨x, y, rfl⟩
  simp only [Graph.incidenceSet, Graph.Inc, toGraph_isLink, he, Sym2.eq_iff, Sym2.mem_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩

/-- The simple graph underlying the multigraph `ends`: distinct vertices are adjacent when an edge
joins them. Self-loops are dropped and parallel edges merged. -/
def toSimpleGraph : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range ends)

variable {ends} in
/-- `u` and `v` are adjacent in the underlying simple graph exactly when they are distinct and
some edge has ends `u` and `v`. -/
theorem toSimpleGraph_adj {u v : V} :
    (toSimpleGraph ends).Adj u v ↔ u ≠ v ∧ ∃ e, ends e = s(u, v) := by
  rw [toSimpleGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_range, and_comm]

/-- The edges of the underlying simple graph are the ends of edges other than self-loops. -/
theorem edgeSet_toSimpleGraph : (toSimpleGraph ends).edgeSet = Set.range ends \ {e | e.IsDiag} :=
  SimpleGraph.edgeSet_fromEdgeSet _

/-- Relabelling the edges does not change the underlying simple graph. -/
theorem toSimpleGraph_comp (f : E' ≃ E) : toSimpleGraph (ends ∘ f) = toSimpleGraph ends := by
  rw [toSimpleGraph, toSimpleGraph, Set.range_comp, f.range_eq_univ, Set.image_univ]

variable [Fintype E] [DecidableEq V]

/-- The edges at `v` other than self-loops. A self-loop at `v` is left out: it would count twice
towards the parity of the edges at `v`, as in Tseitin formulas, and so not at all. -/
def incidence (v : V) : Finset E :=
  {e | v ∈ ends e ∧ ¬(ends e).IsDiag}

variable {ends} in
/-- An edge is at `v`, and not a self-loop, exactly when `v` is one of its ends and its ends are
distinct. -/
@[simp] theorem mem_incidence {v : V} {e : E} :
    e ∈ incidence ends v ↔ v ∈ ends e ∧ ¬(ends e).IsDiag := by
  simp [incidence]

variable {ends} in
/-- An edge with ends `a` and `b` is at `v`, and not a self-loop, when `v` is one of its ends and
`a ≠ b`. -/
theorem mem_incidence_of_ends_eq {v a b : V} {e : E} (h : ends e = s(a, b)) :
    e ∈ incidence ends v ↔ (v = a ∨ v = b) ∧ a ≠ b := by
  rw [mem_incidence, h, Sym2.mem_iff, Sym2.mk_isDiag_iff]

/-- Relabelling the edges does not change the number of edges at a vertex. -/
theorem card_incidence_comp [Fintype E'] (f : E' ≃ E) (v : V) :
    #(incidence (ends ∘ f) v) = #(incidence ends v) :=
  card_equiv f fun _ => by simp

/-- The edges at `v` other than self-loops are the non-loop incident edges of `toGraph ends`. -/
theorem coe_incidence_eq_incidenceSet_toGraph (v : V) :
    (incidence ends v : Set E) = (toGraph ends).incidenceSet v \ {e | (ends e).IsDiag} := by
  ext e
  simp [incidenceSet_toGraph]

/-- Every non-loop incident edge of `v` is in the incidence set of `toGraph ends`. -/
theorem coe_incidence_subset_toGraph_incidenceSet (v : V) :
    (incidence ends v : Set E) ⊆ (toGraph ends).incidenceSet v := by
  rw [coe_incidence_eq_incidenceSet_toGraph]
  exact Set.sdiff_subset

variable [Fintype V]

/-- The edges between `S` and its complement. -/
def edgeCut (S : Finset V) : Finset E :=
  {e | ∃ v ∈ S, ∃ w ∈ Sᶜ, ends e = s(v, w)}

variable {ends} in
/-- An edge is in the edge cut of `S` exactly when it joins a vertex of `S` to a vertex of `Sᶜ`. -/
theorem mem_edgeCut {S : Finset V} {e : E} :
    e ∈ edgeCut ends S ↔ ∃ v ∈ S, ∃ w ∈ Sᶜ, ends e = s(v, w) := by
  simp only [edgeCut, mem_filter, mem_univ, true_and]

/-- The edge cuts of `ends` are those of Mathlib's `Graph`. -/
theorem coe_edgeCut_eq_toGraph_edgeCut (S : Finset V) :
    (edgeCut ends S : Set E) = (toGraph ends).edgeCut S := by
  ext e
  obtain ⟨x, y, he⟩ : ∃ x y, ends e = s(x, y) := by obtain ⟨x, y⟩ := ends e; exact ⟨x, y, rfl⟩
  rw [Finset.mem_coe, mem_edgeCut, (show (toGraph ends).IsLink e x y from he).mem_edgeCut_iff]
  simp only [he, Sym2.eq_iff, Finset.mem_coe, Finset.mem_compl]
  constructor
  · rintro ⟨v, hv, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> tauto
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact ⟨x, hx, y, hy, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨y, hy, x, hx, Or.inr ⟨rfl, rfl⟩⟩

/-- The edges between a set and its complement are those between the complement and the set. -/
theorem edgeCut_compl (S : Finset V) : edgeCut ends Sᶜ = edgeCut ends S := by
  ext e
  simp only [mem_edgeCut, compl_compl]
  exact ⟨fun ⟨v, hv, w, hw, h⟩ => ⟨w, hw, v, hv, h.trans Sym2.eq_swap⟩,
    fun ⟨v, hv, w, hw, h⟩ => ⟨w, hw, v, hv, h.trans Sym2.eq_swap⟩⟩

/-- Relabelling the edges does not change the number of edges leaving a set. -/
theorem card_edgeCut_comp [Fintype E'] (f : E' ≃ E) (S : Finset V) :
    #(edgeCut (ends ∘ f) S) = #(edgeCut ends S) :=
  card_equiv f fun _ => by simp [mem_edgeCut]

/-- The **expansion** `e(G)` of the multigraph `ends`
[Ben-Sasson and Wigderson][BenSassonWigderson2001]: the least number of edges between a set `S`
of vertices with `|V| / 3 ≤ |S| ≤ 2 |V| / 3` and its complement, that is the least edge cut of a
balanced partition of the vertices. With one vertex there is no such set; then `e(G) = 0` by
convention. -/
noncomputable def minBalancedCut : ℕ :=
  sInf {k | ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧ 3 * #S ≤ 2 * Fintype.card V ∧
    #(edgeCut ends S) = k}

/-- `e(G)` is at most the number of edges leaving any set of between a third and two thirds of
the vertices. -/
theorem minBalancedCut_le_card_edgeCut {S : Finset V} (h₁ : Fintype.card V ≤ 3 * #S)
    (h₂ : 3 * #S ≤ 2 * Fintype.card V) : minBalancedCut ends ≤ #(edgeCut ends S) :=
  Nat.sInf_le ⟨S, h₁, h₂, rfl⟩

/-- With at least two vertices, `e(G)` is the number of edges leaving some set of between a third
and two thirds of the vertices. -/
theorem exists_card_edgeCut_eq_minBalancedCut (hV : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧ 3 * #S ≤ 2 * Fintype.card V ∧
      #(edgeCut ends S) = minBalancedCut ends := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (n := (Fintype.card V + 2) / 3) (by rw [card_univ]; omega)
  exact Nat.sInf_mem (s := {k | ∃ S : Finset V, Fintype.card V ≤ 3 * #S ∧
    3 * #S ≤ 2 * Fintype.card V ∧ #(edgeCut ends S) = k}) ⟨_, S, by omega, by omega, rfl⟩

/-- With at least two vertices, `k ≤ e(G)` exactly when at least `k` edges leave every set of
between a third and two thirds of the vertices. -/
theorem le_minBalancedCut_iff (hV : 2 ≤ Fintype.card V) {k : ℕ} :
    k ≤ minBalancedCut ends ↔ ∀ S : Finset V, Fintype.card V ≤ 3 * #S →
      3 * #S ≤ 2 * Fintype.card V → k ≤ #(edgeCut ends S) := by
  refine ⟨fun h S h₁ h₂ => h.trans (minBalancedCut_le_card_edgeCut ends h₁ h₂), fun h => ?_⟩
  obtain ⟨S, h₁, h₂, hS⟩ := exists_card_edgeCut_eq_minBalancedCut ends hV
  exact hS ▸ h S h₁ h₂

/-- With at most one vertex, `e(G) = 0` by convention. -/
theorem minBalancedCut_eq_zero_of_subsingleton [Subsingleton V] : minBalancedCut ends = 0 := by
  have hV : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 ‹_›
  rw [minBalancedCut, Nat.sInf_eq_zero]
  rcases Nat.lt_or_ge (Fintype.card V) 1 with h0 | h1
  · exact Or.inl ⟨∅, by omega, by simp, by simp [edgeCut]⟩
  · refine Or.inr (Set.eq_empty_of_forall_notMem fun k ⟨S, h₁, h₂, _⟩ => ?_)
    have := (card_le_univ S).trans hV
    omega

/-- Relabelling the edges does not change `e(G)`. -/
theorem minBalancedCut_comp [Fintype E'] (f : E' ≃ E) :
    minBalancedCut (ends ∘ f) = minBalancedCut ends := by
  simp only [minBalancedCut, card_edgeCut_comp]

/-- **Connectivity as a cut condition**: a multigraph is connected exactly when it has a vertex
and an edge leaves every nonempty set of vertices other than the set of all vertices. -/
theorem connected_toSimpleGraph_iff :
    (toSimpleGraph ends).Connected ↔
      Nonempty V ∧ ∀ S : Finset V, S.Nonempty → S ≠ univ → (edgeCut ends S).Nonempty := by
  classical
  refine ⟨fun hG => ⟨hG.nonempty, fun S ⟨u, hu⟩ hS => ?_⟩, fun ⟨hV, h⟩ => ?_⟩
  · -- a walk from inside `S` to outside crosses the edge cut
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra! h'
      exact hS (eq_univ_of_forall h')
    obtain ⟨p⟩ := hG.preconnected u w
    obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart (S : Set V) hu hw
    obtain ⟨-, e, he⟩ := toSimpleGraph_adj.1 d.adj
    exact ⟨e, mem_edgeCut.2 ⟨_, hd₁, _, mem_compl.2 hd₂, he⟩⟩
  · -- the vertices reachable from a vertex have no edge leaving them
    obtain ⟨u⟩ := hV
    refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨u, fun w => ?_⟩
    let R : Finset V := {w | (toSimpleGraph ends).Reachable u w}
    suffices hR : R = univ by
      have hw : w ∈ R := by rw [hR]; exact mem_univ w
      simpa [R] using hw
    by_contra hR
    obtain ⟨e, he⟩ := h R ⟨u, by simp [R]⟩ hR
    obtain ⟨a, ha, b, hb, hab⟩ := mem_edgeCut.1 he
    have ha' : (toSimpleGraph ends).Reachable u a := by simpa [R] using ha
    have hne : a ≠ b := fun h => mem_compl.1 hb (h ▸ ha)
    exact mem_compl.1 hb
      (by simpa [R] using ha'.trans (toSimpleGraph_adj.2 ⟨hne, e, hab⟩).reachable)

end Cslib.Multigraph
