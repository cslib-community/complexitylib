/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
import CslibFrontier.Foundations.Data.List.FlatMapPositions

/-!
# Incidence positions from literal constraint prefixes

An occurrence's edge index is the number of preceding argument positions plus its original
scope position. The formula counts records, including duplicates, without inspecting names.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- The original incidence index equals its actual constraint-prefix occurrence count plus
its ordered scope index. No distinctness assumption on variables or constraints is needed. -/
theorem incidenceEdgeIndex_eq_prefix {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (o : F.Occurrence) : incidenceEdgeIndex o = (CSP.vars (F.take o.1.val)).length + o.2.val := by
  let f := fun c : Constraint Rel V × ℕ =>
    c.1.scope.zipIdx.map fun v => (c.2, v.2, v.1)
  have hp (i : ℕ) : ((F.zipIdx.take i).flatMap f).length = (CSP.vars (F.take i)).length := by
    simp only [f, List.length_flatMap, List.length_map, List.length_zipIdx, CSP.vars]
    conv_rhs => rw [← List.zipIdx_map_fst 0 F, List.map_take, List.map_map]
    simp only [← List.map_take, Function.comp_def]
  have hi : o.1.val < F.zipIdx.length := by
    simpa only [List.length_zipIdx] using o.1.isLt
  have hj : o.2.val < (f F.zipIdx[o.1.val]).length := by
    simpa only [f, List.length_map, List.length_zipIdx, List.getElem_zipIdx] using o.2.isLt
  have he := List.getElem_flatMap_prefix_add F.zipIdx f hi hj
  have hb := List.flatMap_prefix_add_lt F.zipIdx f hi hj
  have ht : F.zipIdx.flatMap f = F.occurrences := (CSP.occurrences_eq_flatMap_zipIdx F).symm
  rw [ht, hp] at hb
  have hread : F.occurrences[(CSP.vars (F.take o.1.val)).length + o.2.val]'hb = o.record := by
    simpa only [ht, hp, f, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
      CSP.Occurrence.record, CSP.Occurrence.var] using he
  unfold incidenceEdgeIndex
  rw [← hread]
  exact F.occurrences_nodup.idxOf_getElem _ hb

end Cslib.Complexity.CSP
