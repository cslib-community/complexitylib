/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Incidence
public import Complexity.Logics.Propositional.CNF.Compact.Relabel

/-!
# Compaction preserves the listed CNF incidence graph

## Main results

* `Cslib.Complexity.SAT.incidenceGraph_compact`: the entire listed graph is unchanged,
  including variable indices, clause indices, repeated edge occurrences and their order.

## References

This is an elementary consequence of the existing first-occurrence numbering conventions.
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL

/-- Compaction changes literal labels without changing any vertex or edge of the listed graph. -/
theorem incidenceGraph_compact {V : Type} [DecidableEq V] (φ : CNF V) :
    incidenceGraph φ.compact = incidenceGraph φ := by
  simp only [incidenceGraph, CNF.distinctVars_compact, List.length_map, CNF.length_compact]
  congr 1
  simp only [CNF.compact, occurrences_relabel, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro o ho
  have hv : o.2.2.1 ∈ φ.vars := by
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho
  congr 1
  simpa only [CNF.distinctVars_compact] using CNF.idxOf_distinctVars_compact φ hv

end Cslib.Complexity.SAT
