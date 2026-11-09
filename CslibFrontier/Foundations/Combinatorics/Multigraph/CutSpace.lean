/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph

/-!
# The cut space of a multigraph

Taking edge cuts turns symmetric differences of sets of vertices into symmetric differences of sets
of edges (`Cslib.Multigraph.edgeCut_symmDiff`): an edge leaves `S ∆ T` exactly when it leaves one of
`S` and `T` but not both. This and `Cslib.Multigraph.mem_edgeCut_of_ends_eq` are the `Finset` forms
of Mathlib's `Graph.edgeCut_symmDiff` and `Graph.IsLink.mem_edgeCut_iff`, through
`Cslib.Multigraph.coe_edgeCut_eq_toGraph_edgeCut`. The edge cut of a single vertex consists of the
edges at it other than self-loops (`Cslib.Multigraph.edgeCut_singleton`). So, informally, the edge
cuts form an `𝔽₂`-vector space, the *cut space*, spanned by the sets of edges at the vertices; this
structure is not formalized here. On a connected
multigraph the only sets with no edge leaving them are `∅` and the set of all vertices
(`Cslib.Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty`).

A set `S` that fewer than `e(G)` edges leave (`Cslib.Multigraph.minBalancedCut`) is not balanced,
so it has fewer than a third or more than two thirds of the vertices. If moreover `S` has at most
two thirds of the vertices, it has fewer than a third of them
(`Cslib.Multigraph.three_mul_card_lt_of_card_edgeCut_lt`). This dichotomy is how expansion enters
degree lower bounds for Tseitin formulas in algebraic proof systems such as polynomial calculus.

## Main results

* `Cslib.Multigraph.edgeCut_symmDiff`: edge cuts turn symmetric differences into symmetric
  differences.
* `Cslib.Multigraph.edgeCut_empty`, `Cslib.Multigraph.edgeCut_singleton`: the edge cuts of `∅` and
  of a single vertex.
* `Cslib.Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty`: on a connected multigraph, only `∅`
  and the set of all vertices have empty edge cuts.
* `Cslib.Multigraph.three_mul_card_lt_of_card_edgeCut_lt`: a set of at most two thirds of the
  vertices that fewer than `e(G)` edges leave has fewer than a third of the vertices.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
-/

public section

namespace Cslib.Multigraph

open Finset

variable {V E : Type*} (ends : E → Sym2 V) [Fintype V] [Fintype E] [DecidableEq V]

variable {ends} in
/-- An edge with ends `a` and `b` leaves `S` exactly when one of its ends is in `S` and the other
is not. -/
theorem mem_edgeCut_of_ends_eq {S : Finset V} {e : E} {a b : V} (h : ends e = s(a, b)) :
    e ∈ edgeCut ends S ↔ (a ∈ S ↔ b ∉ S) := by
  rw [← Finset.mem_coe, coe_edgeCut_eq_toGraph_edgeCut,
    (show (toGraph ends).IsLink e a b from h).mem_edgeCut_iff]
  simp only [Finset.mem_coe]
  tauto

/-- **Edge cuts turn symmetric differences into symmetric differences**: an edge leaves `S ∆ T`
exactly when it leaves one of `S` and `T` but not both. -/
theorem edgeCut_symmDiff [DecidableEq E] (S T : Finset V) :
    edgeCut ends (symmDiff S T) = symmDiff (edgeCut ends S) (edgeCut ends T) := by
  apply Finset.coe_injective
  rw [Finset.coe_symmDiff, coe_edgeCut_eq_toGraph_edgeCut, coe_edgeCut_eq_toGraph_edgeCut,
    coe_edgeCut_eq_toGraph_edgeCut, Finset.coe_symmDiff, Graph.edgeCut_symmDiff]

/-- No edge leaves the empty set. -/
@[simp] theorem edgeCut_empty : edgeCut ends (∅ : Finset V) = ∅ := by
  ext e
  simp [mem_edgeCut]

/-- The edges leaving a single vertex are the edges at it other than self-loops. -/
theorem edgeCut_singleton (v : V) : edgeCut ends {v} = incidence ends v := by
  ext e
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (ends e)
  rw [mem_edgeCut_of_ends_eq hab, mem_incidence_of_ends_eq hab, mem_singleton, mem_singleton]
  by_cases ha : a = v <;> by_cases hb : b = v <;> subst_vars <;> simp_all [eq_comm]

variable {ends}

/-- On a connected multigraph, **only `∅` and the set of all vertices have no edge leaving
them**. -/
theorem eq_empty_or_eq_univ_of_edgeCut_eq_empty (hG : (toSimpleGraph ends).Connected)
    {S : Finset V} (hS : edgeCut ends S = ∅) : S = ∅ ∨ S = univ := by
  by_contra! h
  obtain ⟨e, he⟩ := ((connected_toSimpleGraph_iff ends).1 hG).2 S h.1 h.2
  rw [hS] at he
  exact notMem_empty e he

/-- **The expansion dichotomy.** A set of at most two thirds of the vertices that fewer than
`e(G)` edges leave has fewer than a third of the vertices. -/
theorem three_mul_card_lt_of_card_edgeCut_lt {S : Finset V}
    (hS : #(edgeCut ends S) < minBalancedCut ends) (h₂ : 3 * #S ≤ 2 * Fintype.card V) :
    3 * #S < Fintype.card V := by
  by_contra! h₁
  exact absurd (minBalancedCut_le_card_edgeCut ends h₁ h₂) (not_le.2 hS)

end Cslib.Multigraph
