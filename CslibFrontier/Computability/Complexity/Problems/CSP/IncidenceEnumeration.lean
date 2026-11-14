/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Incidence
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import Mathlib.Data.List.GetD

/-!
# Exact incidence indices in the original occurrence enumeration

The typed occurrence scan and the native record scan have exactly the same indexed positions.
Looking up an incidence index returns its original record, including repeated names and
duplicate constraints. No rotation or source well-formedness assumption is needed.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Every incidence index lies within the native variable-occurrence word. -/
theorem incidenceEdgeIndex_lt_vars {F : CSP Rel V} (o : F.Occurrence) :
    incidenceEdgeIndex o < F.vars.length := by
  have hl := congrArg List.length (CSP.map_occurrences F)
  simp only [List.length_map] at hl
  rw [← hl]
  simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o

/-- The native variable-occurrence list reads the original variable at the corresponding
incidence edge index. -/
theorem getElem_vars_incidenceEdgeIndex (o : F.Occurrence) :
    F.vars[incidenceEdgeIndex o]'(incidenceEdgeIndex_lt_vars o) =
      o.var := by
  simp only [← CSP.map_occurrences F, List.getElem_map, incidenceEdgeIndex]
  rw [List.getElem_idxOf
    (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  rfl

/-- Every occurring variable has an actual occurrence at its native first-list index.
No enumeration through the numeric variable name is involved. -/
theorem exists_occurrence_at_first_index (v : V) (hv : v ∈ F.vars) :
    ∃ o : F.Occurrence, incidenceEdgeIndex o = F.vars.idxOf v ∧ o.var = v := by
  have hi : F.vars.idxOf v < (incidenceGraph F).edges.length := by
    have hl := congrArg List.length (CSP.map_occurrences F)
    simp only [List.length_map] at hl
    rw [incidenceGraph_edges, List.length_map, hl]
    exact List.idxOf_lt_length_of_mem hv
  obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) (F.vars.idxOf v) hi
  refine ⟨o, ho, ?_⟩
  have h := getElem_vars_incidenceEdgeIndex o
  simpa only [ho, List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)] using h.symm

/-- The original variable-word getter at an actual incidence index returns its own label. -/
theorem getD_vars_incidenceEdgeIndex {F : CSP Rel V} (o : F.Occurrence) (fallback : V) :
    F.vars.getD (incidenceEdgeIndex o) fallback = o.var := by
  rw [List.getD_eq_getElem _ _ (incidenceEdgeIndex_lt_vars o), getElem_vars_incidenceEdgeIndex]

/-- The original raw occurrence getter at an actual incidence index returns its own record. -/
theorem getD_occurrences_incidenceEdgeIndex {F : CSP Rel V} (o : F.Occurrence)
    (fallback : ℕ × ℕ × V) : F.occurrences.getD (incidenceEdgeIndex o) fallback = o.record := by
  rw [List.getD_eq_getElem _ _ (by
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))

/-- The typed scan enumerates actual edge indices in their literal native order. -/
theorem map_incidenceEdgeIndex_incidenceList (F : CSP Rel V) :
    (CSP.incidenceList F).map incidenceEdgeIndex = List.range F.occurrences.length := by
  have hlen : (CSP.incidenceList F).length = F.occurrences.length := by
    rw [CSP.occurrences_eq_map_incidenceList, List.length_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hlen]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hb : i < F.occurrences.length := by simpa only [List.length_range] using hj
    have hr : F.occurrences[i] = (CSP.incidenceList F)[i].record := by
      simp only [CSP.occurrences_eq_map_incidenceList, List.getElem_map]
    unfold incidenceEdgeIndex
    rw [← hr]
    exact F.occurrences_nodup.idxOf_getElem i hb

end Cslib.Complexity.CSP
