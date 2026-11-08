/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence
public import Complexity.Computability.Complexity.Problems.SAT.Incidence
public import Complexity.Computability.Complexity.Problems.Graph.Ports
public import Complexity.Computability.PolyTime.CSP.Vars
public import Complexity.Computability.PolyTime.CSP.Occurrence
import Complexity.Logics.Propositional.CNF.PolyTime
import Mathlib.Data.List.GetD

/-!
# Native ordered CSP incidence multigraphs

Variables receive dense names in first-occurrence order; constraint-position vertices follow.
There is one listed edge per ordered argument occurrence, including repeated variables and
identical constraints. The existing positive-CNF adapter has exactly these scopes, so both the
construction and its native polynomial-time certificate reuse `SAT.incidenceGraph`.

The incidence model is the bipartite multigraph of Fulla–Živný, *On Planar Valued CSPs*,
arXiv:1602.06323v3, Section 2.1, p. 4 (the paragraph preceding Definition 1). Constraint positions
replace their indexed valued constraints; ordered scopes give their argument incidences. This
module treats arbitrary-domain decision CSPs, retaining nullary constraints and using only
occurring variables. It supplies neither a drawing nor the order-preserving plane representation
of Definition 1. That extra structure is needed for a planar-CSP claim.

The finite-list naming and encoding proofs are original. Binary source labels are never expanded
into a range up to their maximum; generated vertex names are bounded by the input's list sizes.

## Main results

* `Cslib.Complexity.CSP.incidenceGraph_edges`: exact ordered edge list.
* `Cslib.Complexity.CSP.incidenceEdgeIndex`: identifies each occurrence's distinct edge record.
* `Cslib.Complexity.CSP.computableInPolyTime_incidenceGraph`: native binary graph construction.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- The existing listed multigraph, with dense variable and constraint-position vertices. -/
@[expose] def incidenceGraph (F : CSP Rel V) : Graph := SAT.incidenceGraph F.varCNF

/-- The graph declares precisely the variable interval followed by the constraint interval. -/
theorem incidenceGraph_vertices (F : CSP Rel V) :
    (incidenceGraph F).1 = List.range (F.numVars + F.length) := by
  simp [incidenceGraph, SAT.incidenceGraph, CSP.length_distinctVars]

/-- Each occurrence contributes one edge in constraint-then-scope order. Parallel edges remain
separate list entries; the original scope position is recoverable from the occurrence table. -/
theorem incidenceGraph_edges (F : CSP Rel V) :
    (incidenceGraph F).2 = F.occurrences.map
      (fun o => (F.distinctVars.idxOf o.2.2, F.numVars + o.1)) := by
  simp only [incidenceGraph, SAT.incidenceGraph, CSP.occurrences, List.map_map,
    CSP.distinctVars_varCNF, CSP.length_distinctVars, Function.comp_def]

/-- Vertex count includes every constraint position, even identical and nullary constraints. -/
theorem length_vertices_incidenceGraph (F : CSP Rel V) :
    (incidenceGraph F).1.length = F.numVars + F.length := by
  rw [incidenceGraph_vertices, List.length_range]

/-- Edge count includes each argument occurrence, even repeated variables. -/
theorem length_edges_incidenceGraph (F : CSP Rel V) :
    (incidenceGraph F).2.length = (F.map fun c => c.2.length).sum := by
  rw [incidenceGraph_edges, List.length_map, CSP.length_occurrences]

/-- Every listed edge joins the variable part to the constraint-position part. -/
theorem incidenceGraph_bipartite {e : ℕ × ℕ} (he : e ∈ (incidenceGraph F).2) :
    e.1 < F.numVars ∧ F.numVars ≤ e.2 ∧ e.2 < F.numVars + F.length := by
  simpa only [CSP.distinctVars_varCNF, CSP.length_distinctVars, CSP.length_varCNF] using
    SAT.incidenceGraph_bipartite he

/-- Both endpoints of every listed edge are declared vertices. -/
theorem incidenceGraph_endpoints {e : ℕ × ℕ} (he : e ∈ (incidenceGraph F).2) :
    e.1 ∈ (incidenceGraph F).1 ∧ e.2 ∈ (incidenceGraph F).1 :=
  SAT.incidenceGraph_endpoints he

/-- The two vertex intervals are disjoint, so incidence edges are never loops. -/
theorem incidenceGraph_loopless {e : ℕ × ℕ} (he : e ∈ (incidenceGraph F).2) : e.1 ≠ e.2 :=
  SAT.incidenceGraph_loopless he

/-- Edge-list position of an argument occurrence, retaining parallel edge identity. -/
@[expose] def incidenceEdgeIndex (o : F.Occurrence) : ℕ := F.occurrences.idxOf o.record

/-- Every argument occurrence indexes a declared edge record. -/
theorem incidenceEdgeIndex_lt (o : F.Occurrence) :
    incidenceEdgeIndex o < (incidenceGraph F).2.length := by
  rw [incidenceGraph_edges, List.length_map]
  exact List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩)

/-- Different scope or constraint positions give different edge-list positions. -/
theorem incidenceEdgeIndex_injective : Function.Injective (incidenceEdgeIndex (F := F)) := by
  intro o p h
  apply CSP.Occurrence.record_injective
  exact (List.idxOf_inj (CSP.mem_occurrences.mpr ⟨o, rfl⟩)).mp h

/-- Every edge-list position comes from an argument occurrence. -/
theorem exists_incidenceEdgeIndex (i : ℕ) (hi : i < (incidenceGraph F).2.length) :
    ∃ o : F.Occurrence, incidenceEdgeIndex o = i := by
  have hi' : i < F.occurrences.length := by
    simpa only [incidenceGraph_edges, List.length_map] using hi
  obtain ⟨o, ho⟩ := CSP.mem_occurrences.mp (List.getElem_mem hi')
  refine ⟨o, ?_⟩
  simp only [incidenceEdgeIndex, ho]
  exact F.occurrences_nodup.idxOf_getElem i hi'

/-- The occurrence's listed edge connects its dense variable name to its constraint position. -/
theorem getElem_incidenceEdgeIndex (o : F.Occurrence) :
    (incidenceGraph F).2[incidenceEdgeIndex o]'(incidenceEdgeIndex_lt o) =
      (F.distinctVars.idxOf o.var, F.numVars + o.1) := by
  simp only [incidenceGraph_edges, List.getElem_map, incidenceEdgeIndex]
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  rfl

/-- Reuse the general graph endpoint reader: `false` is the variable, `true` the constraint. -/
theorem edgeEndpoint_incidenceEdgeIndex (o : F.Occurrence) (side : Bool) :
    (incidenceGraph F).edgeEndpoint (incidenceEdgeIndex o) side =
      if side then F.numVars + o.1 else F.distinctVars.idxOf o.var := by
  simp only [Graph.edgeEndpoint, List.getD_eq_getElem _ _ (incidenceEdgeIndex_lt o),
    getElem_incidenceEdgeIndex]

/-- Construct the native graph under framed CSP encoding and binary graph labels. Source
variables are compared as encoded strings; there is no iteration to their largest name. -/
@[fun_prop]
theorem computableInPolyTime_incidenceGraph (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (incidenceGraph (Rel := Rel) (V := V))
      (encCSP encRel encV) encGraph :=
  (SAT.computableInPolyTime_incidenceGraph encV).comp
    (computableInPolyTime_varCNF encRel encV)

end Cslib.Complexity.CSP
