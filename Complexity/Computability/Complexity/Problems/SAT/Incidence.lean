/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# The finite incidence graph of a CNF formula

Variables receive consecutive names in first-occurrence order. Clause names follow the variable
names, with one vertex for each clause position, including repeated and empty clauses. Edges
are in literal-occurrence order. Repeated literals therefore give repeated edge records; their
incidences remain distinct when drawing routes or bounding degrees.

The representation is the existing binary-encoded `Cslib.Complexity.Graph`, rather than a new
graph type. Natural source variable labels are compared as binary strings and never determine
the number of vertices.

## Main definitions

* `Cslib.Complexity.SAT.incidenceGraph`: the variable-clause incidence graph.

## Main results

* `Cslib.Complexity.SAT.length_vertices_incidenceGraph`,
  `Cslib.Complexity.SAT.length_edges_incidenceGraph`: exact presentation sizes.
* `Cslib.Complexity.SAT.incidenceGraph_endpoints`: every edge endpoint is declared.
* `Cslib.Complexity.SAT.incidenceGraph_bipartite`: each edge joins a variable to a clause.
* `Cslib.Complexity.SAT.incidenceGraph_loopless`: incidence edges have distinct endpoints.
* `Cslib.Complexity.SAT.computableInPolyTime_incidenceGraph`: constructing the graph is
  polynomial-time under binary encodings.

## References

This finite-list incidence presentation and its native computation proof are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL
open Turing.MultiTapeTM

variable {V : Type} [DecidableEq V]

/-- The finite incidence graph, with one edge record for every literal occurrence. -/
def incidenceGraph (φ : CNF V) : Graph :=
  (List.range (φ.distinctVars.length + φ.length),
    (Cslib.Logic.PL.occurrences φ).map fun o =>
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1))

/-- There is one vertex per distinct variable and per clause position. -/
theorem length_vertices_incidenceGraph (φ : CNF V) :
    (incidenceGraph φ).1.length = φ.numVars + φ.length := by
  simp [incidenceGraph, CNF.length_distinctVars]

/-- Every literal occurrence gives exactly one edge record. -/
theorem length_edges_incidenceGraph (φ : CNF V) :
    (incidenceGraph φ).2.length = φ.vars.length := by
  simp [incidenceGraph, length_occurrences]

/-- The edge records join the variable and clause parts of the declared vertex interval. -/
theorem incidenceGraph_bipartite {φ : CNF V} {e : ℕ × ℕ}
    (he : e ∈ (incidenceGraph φ).2) :
    e.1 < φ.distinctVars.length ∧ φ.distinctVars.length ≤ e.2 ∧
      e.2 < φ.distinctVars.length + φ.length := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
  have hvar : o.2.2.1 ∈ φ.vars := by
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho
  have hindex := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hvar)
  obtain ⟨hclause, _, _⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
  exact ⟨hindex, Nat.le_add_right _ _, Nat.add_lt_add_left hclause _⟩

/-- Every edge endpoint occurs in the list of declared vertices. -/
theorem incidenceGraph_endpoints {φ : CNF V} {e : ℕ × ℕ}
    (he : e ∈ (incidenceGraph φ).2) :
    e.1 ∈ (incidenceGraph φ).1 ∧ e.2 ∈ (incidenceGraph φ).1 := by
  obtain ⟨hu, _, hv⟩ := incidenceGraph_bipartite he
  simp only [incidenceGraph, List.mem_range]
  exact ⟨hu.trans_le (Nat.le_add_right _ _), hv⟩

/-- The variable and clause name intervals are disjoint, so incidence edges are not loops. -/
theorem incidenceGraph_loopless {φ : CNF V} {e : ℕ × ℕ}
    (he : e ∈ (incidenceGraph φ).2) : e.1 ≠ e.2 := by
  obtain ⟨hu, hv, _⟩ := incidenceGraph_bipartite he
  omega

/-- Constructing the incidence graph compares binary encodings rather than expanding source
variable names to unary. -/
@[fun_prop]
theorem computableInPolyTime_incidenceGraph (enc : V ↪ List Bool) :
    ComputableInPolyTime (incidenceGraph (V := V))
      (encList (encList (encPair enc encBool))) encGraph := by
  let unaryGraph := encPair (encList encUnary) (encList (encPair encUnary encUnary))
  have hd := CNF.computableInPolyTime_distinctVars enc
  have ho := Cslib.Logic.PL.computableInPolyTime_occurrences enc
  unfold Cslib.Logic.PL.encOccurrence at ho
  have hu : ComputableInPolyTime (incidenceGraph (V := V))
      (encList (encList (encPair enc encBool))) unaryGraph := by
    unfold incidenceGraph unaryGraph
    fun_prop
  have hc : ComputableInPolyTime (fun g : Graph => g) unaryGraph encGraph := by
    open ComputableInPolyTime in
    have hp := (unary_to_binary.comp (fst encUnary encUnary)).prod
      (unary_to_binary.comp (snd encUnary encUnary))
    open ComputableInPolyTime in
    have h := ((map unary_to_binary).comp
      (fst (encList encUnary) (encList (encPair encUnary encUnary)))).prod
        ((map hp).comp (snd (encList encUnary) (encList (encPair encUnary encUnary))))
    simpa [Function.comp_def, unaryGraph, encGraph] using h
  exact hc.comp hu

end Cslib.Complexity.SAT
