/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Graph

/-!
# Canonical graph semifilters

A canonical semifilter is the upward closure of a complementary row and complementary column
at an edge. Both complementary sets must be nonempty. This restricted witness class gives a
lower bound on unrestricted graph cover complexity.

## Main definitions

* `Cslib.Circuits.Fusion.Graph.outsideRow`, `Cslib.Circuits.Fusion.Graph.outsideColumn`: the parts
  of a row and column outside the graph.
* `Cslib.Circuits.Fusion.Graph.CanonicalEdge`: edges with nonempty complementary row and column.
* `Cslib.Circuits.Fusion.Graph.canonicalFilter`: the corresponding semifilter.
* `Cslib.Circuits.Fusion.Graph.canonicalClass`: the class of canonical semifilters.

## Main results

* `Cslib.Circuits.Fusion.Graph.canonicalWitness`: a canonical semifilter is a graph witness.
* `Cslib.Circuits.Fusion.Graph.canonical_pairCoverComplexity_le`: restricting witnesses lowers
  cover complexity.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Section 4.2.
* Adapted from LowerBound/Fusion/Graph/Canonical.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.Graph

variable {V : Type*} [Fintype V] (graph : Set (V × V))

/-- The part of a row outside the graph. -/
def outsideRow (v : V) : Set ↥(graphᶜ) := {x | x.val.1 = v}

/-- The part of a column outside the graph. -/
def outsideColumn (v : V) : Set ↥(graphᶜ) := {x | x.val.2 = v}

/-- Edges whose complementary row and column are both nonempty. -/
def CanonicalEdge :=
  {e : V × V // e ∈ graph ∧ (outsideRow graph e.1).Nonempty ∧
    (outsideColumn graph e.2).Nonempty}

/-- Upward closure of the complementary row and column at an edge. -/
def canonicalFilter (e : CanonicalEdge graph) : Semifilter ↥(graphᶜ) where
  toFun s := outsideRow graph e.val.1 ⊆ s ∨ outsideColumn graph e.val.2 ⊆ s
  monotone' _ _ h := Or.imp (fun hs => hs.trans h) (fun hs => hs.trans h)
  map_top' := propext ⟨fun _ => trivial, fun _ => Or.inl (Set.subset_univ _)⟩
  map_bot' := propext ⟨fun h => h.elim
    (fun hs => e.property.2.1.ne_empty (Set.eq_empty_iff_forall_notMem.mpr
      (fun _ hx => hs hx)))
    (fun hs => e.property.2.2.ne_empty (Set.eq_empty_iff_forall_notMem.mpr
      (fun _ hx => hs hx))), False.elim⟩

/-- Restrict witnesses to canonical graph semifilters. -/
def canonicalClass (F : Semifilter ↥(graphᶜ)) : Prop :=
  ∃ e : CanonicalEdge graph, F = canonicalFilter graph e

/-- A canonical semifilter lies above the edge defining it. -/
def canonicalWitness (e : CanonicalEdge graph) :
    SemifilterWitness graph sources (canonicalClass graph) where
  point := ⟨e.val, e.property.1⟩
  filter := canonicalFilter graph e
  admissible_filter := ⟨e, rfl⟩
  above i := by
    refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) i
    · simp only [sources, Fin.addCases_left, Set.mem_ofPred_eq] at hj
      left
      intro x hx
      simp only [Set.mem_preimage, sources, Fin.addCases_left, Set.mem_ofPred_eq]
      exact (show x.val.1 = e.val.1 from hx).trans hj
    · simp only [sources, Fin.addCases_right, Set.mem_ofPred_eq] at hj
      right
      intro x hx
      simp only [Set.mem_preimage, sources, Fin.addCases_right, Set.mem_ofPred_eq]
      exact (show x.val.2 = e.val.2 from hx).trans hj

/-- Canonical witnesses form a subclass of unrestricted graph witnesses. -/
theorem canonical_pairCoverComplexity_le :
    pairCoverComplexity graph sources (canonicalClass graph) ≤
      pairCoverComplexity graph sources := by
  apply le_iInf
  intro c
  let d : PairCover graph sources (canonicalClass graph) := {
    pairs := c.pairs
    isCover w := c.isCover {
      point := w.point
      filter := w.filter
      admissible_filter := trivial
      above := w.above } }
  exact pairCoverComplexity_le d

end Cslib.Circuits.Fusion.Graph
