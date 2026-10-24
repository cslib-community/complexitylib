/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Complexity.Tactic.PolyTime

/-!
# Adding trivial edges to encoded constraint graphs

Adding universally accepting constraints is a step of Dinur's preprocessing. These programs
append supplied edges or construct a loop at every vertex. Their interpretation is exactly
the existing union of constraint graphs, with its proved satisfiability and value laws.

## Main definitions

* `Cslib.PCP.Encoded.Graph.addTrivial`: append constraints at supplied endpoints.
* `Cslib.PCP.Encoded.Graph.addLoops`: append one self-loop per declared vertex.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_addTrivial`,
  `Cslib.PCP.Encoded.Graph.isPolyTime_addLoops`: uniform machine-backed certificates.
* `Cslib.PCP.Encoded.Graph.satisfiable_addTrivial_iff`,
  `Cslib.PCP.Encoded.Graph.unsatVal_addTrivial`: exact correctness of adding trivial edges.
* `Cslib.PCP.Encoded.Graph.satisfiable_addLoops_iff`,
  `Cslib.PCP.Encoded.Graph.unsatVal_addLoops`: exact correctness of adding self-loops.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C α : Type}

/-- Append edges carrying a specified constraint descriptor. In applications `truth` is a
constraint that accepts every pair of labels. -/
def addTrivial (truth : C) (g : Graph C) (extra : List (ℕ × ℕ)) : Graph C :=
  ⟨g.vertices, g.edges ++ extra.map (fun p => ⟨p.1, p.2, truth⟩)⟩

/-- Add one edge with constraint `truth` from each declared vertex to itself. -/
def addLoops (truth : C) (g : Graph C) : Graph C :=
  g.addTrivial truth ((List.range g.vertices).map fun v => (v, v))

/-- Appending explicitly listed trivial edges is uniformly polynomial-time in both lists. -/
@[fun_prop]
theorem isPolyTime_addTrivial (enc : C ↪ List Bool) (truth : C) :
    ComputableInPolyTime (fun p : Graph C × List (ℕ × ℕ) =>
      p.1.addTrivial truth p.2)
      (encPair (encoding enc) (encList (encPair encUnary encUnary))) (encoding enc) := by
  unfold addTrivial
  polytime

/-- Constructing all self-loops, including enumerating their endpoints, is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_addLoops (enc : C ↪ List Bool) (truth : C) :
    ComputableInPolyTime (addLoops truth) (encoding enc) (encoding enc) := by
  unfold addLoops
  polytime

/-- An appended edge list has the declared number of old and new edges. -/
@[simp]
theorem length_edges_addTrivial (truth : C) (g : Graph C) (extra : List (ℕ × ℕ)) :
    (g.addTrivial truth extra).edges.length = g.edges.length + extra.length := by
  simp [addTrivial]

/-- Adding one self-loop per declared vertex adds exactly that many edges. -/
@[simp]
theorem length_edges_addLoops (truth : C) (g : Graph C) :
    (g.addLoops truth).edges.length = g.edges.length + g.vertices := by
  simp [addLoops]

/-- Adding edges within the declared vertex set preserves well-formedness. -/
theorem WellFormed.addTrivial {g : Graph C} (hg : g.WellFormed) (truth : C)
    {extra : List (ℕ × ℕ)} (hextra : ∀ p ∈ extra, p.1 < g.vertices ∧ p.2 < g.vertices) :
    (g.addTrivial truth extra).WellFormed := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hg e he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hextra p hp

/-- Self-loops stay in the declared vertex set, including when it is empty. -/
theorem WellFormed.addLoops {g : Graph C} (hg : g.WellFormed) (truth : C) :
    (g.addLoops truth).WellFormed := by
  apply hg.addTrivial truth
  intro p hp
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  exact ⟨List.mem_range.mp hv, List.mem_range.mp hv⟩

/-- The ordered concatenation of edge lists numbers their disjoint union. -/
def appendEdgeEquiv (left right : List (Edge C)) :
    Fin left.length ⊕ Fin right.length ≃ Fin (left ++ right).length :=
  finSumFinEquiv.trans (finCongr (List.length_append ..).symm)

/-- Appending edge records interprets as the union of the corresponding constraint graphs,
with the canonical enumeration of their disjoint edge sets. -/
theorem toGraph_append (vertices : ℕ) (left right : List (Edge C))
    (eval : C → α → α → Bool) :
    ((Graph.mk vertices (left ++ right)).toGraph eval).comap (appendEdgeEquiv left right) =
      ((Graph.mk vertices left).toGraph eval).union ((Graph.mk vertices right).toGraph eval) := by
  ext (i | i) <;>
    simp [toGraph, ConstraintGraph.comap, ConstraintGraph.union, appendEdgeEquiv,
      List.get_eq_getElem, List.getElem_append_left, List.getElem_append_right]

/-- Appending universally accepting constraints preserves satisfiability. -/
theorem satisfiable_addTrivial_iff (g : Graph C) (eval : C → α → α → Bool)
    (truth : C) (htruth : ∀ a b, eval truth a b = true) (extra : List (ℕ × ℕ)) :
    ((g.addTrivial truth extra).toGraph eval).Satisfiable ↔ (g.toGraph eval).Satisfiable := by
  rw [← ConstraintGraph.satisfiable_comap_iff ((g.addTrivial truth extra).toGraph eval)
    (appendEdgeEquiv g.edges (extra.map fun p => ⟨p.1, p.2, truth⟩)).surjective]
  rw [show ((g.addTrivial truth extra).toGraph eval).comap
      (appendEdgeEquiv g.edges (extra.map fun p => ⟨p.1, p.2, truth⟩)) =
      (g.toGraph eval).union
        ((Graph.mk g.vertices (extra.map fun p => ⟨p.1, p.2, truth⟩)).toGraph eval) from
    toGraph_append g.vertices g.edges _ eval]
  rw [ConstraintGraph.satisfiable_union_iff]
  constructor
  · rintro ⟨σ, hσ, _⟩
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, hσ, fun i => ?_⟩
    simp [ConstraintGraph.Satisfies, toGraph, List.get_eq_getElem, htruth]

/-- Appending universally accepting constraints scales the value by the fraction of original
edges. This also covers empty input and output edge sets. -/
theorem unsatVal_addTrivial (g : Graph C) (eval : C → α → α → Bool)
    (truth : C) (htruth : ∀ a b, eval truth a b = true) (extra : List (ℕ × ℕ)) :
    ((g.addTrivial truth extra).toGraph eval).unsatVal =
      (g.edges.length : ℝ) / (g.edges.length + extra.length) * (g.toGraph eval).unsatVal := by
  change ((Graph.mk g.vertices
    (g.edges ++ extra.map fun p => Edge.mk p.1 p.2 truth)).toGraph eval).unsatVal = _
  rw [← ConstraintGraph.unsatVal_comap_equiv
    ((Graph.mk g.vertices
      (g.edges ++ extra.map fun p => Edge.mk p.1 p.2 truth)).toGraph eval)
    (appendEdgeEquiv g.edges (extra.map fun p => ⟨p.1, p.2, truth⟩)), toGraph_append]
  rw [ConstraintGraph.unsatVal_union_of_forall_rel]
  · simp
  · intro i a b
    simp [toGraph, List.get_eq_getElem, htruth]

/-- Adding universally accepting self-loops preserves satisfiability. -/
theorem satisfiable_addLoops_iff (g : Graph C) (eval : C → α → α → Bool)
    (truth : C) (htruth : ∀ a b, eval truth a b = true) :
    ((g.addLoops truth).toGraph eval).Satisfiable ↔ (g.toGraph eval).Satisfiable :=
  g.satisfiable_addTrivial_iff eval truth htruth _

/-- Adding one universally accepting self-loop per vertex scales the value by the fraction
of original edges. -/
theorem unsatVal_addLoops (g : Graph C) (eval : C → α → α → Bool)
    (truth : C) (htruth : ∀ a b, eval truth a b = true) :
    ((g.addLoops truth).toGraph eval).unsatVal =
      (g.edges.length : ℝ) / (g.edges.length + g.vertices) * (g.toGraph eval).unsatVal := by
  change ((g.addTrivial truth
    ((List.range g.vertices).map fun v => (v, v))).toGraph eval).unsatVal = _
  have h := g.unsatVal_addTrivial eval truth htruth
    ((List.range g.vertices).map fun v => (v, v))
  simpa only [List.length_map, List.length_range] using h

end Cslib.PCP.Encoded.Graph
