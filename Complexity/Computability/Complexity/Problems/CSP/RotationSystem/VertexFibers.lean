/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem

/-!
# Endpoint fibers in actual CSP incidence coordinates

Equality of incidence endpoints distinguishes the variable and constraint sides, then compares
original variable labels or actual constraint positions. Repeated variables and constraints
retain separate darts; dense vertex names do not require an injection on source labels.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- Actual endpoint equality is exactly same side and the corresponding original label or
constraint-position equality. This includes parallel occurrences and arbitrary source labels. -/
theorem vertex_incidenceDart_eq_iff {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (o p : F.Occurrence) (side other : Bool) :
    (incidenceDart o side).vertex = (incidenceDart p other).vertex ↔
      side = other ∧ (if side then o.1 = p.1 else o.var = p.var) := by
  have ho := incidenceGraph_bipartite (List.getElem_mem (incidenceEdgeIndex_lt o))
  have hp := incidenceGraph_bipartite (List.getElem_mem (incidenceEdgeIndex_lt p))
  rw [getElem_incidenceEdgeIndex] at ho hp
  rw [vertex_incidenceDart, vertex_incidenceDart]
  cases side <;> cases other
  · simp only [Bool.false_eq_true, ite_false, true_and]
    exact List.idxOf_inj (CSP.mem_distinctVars.mpr o.var_mem)
  · simp only [Bool.false_eq_true, ite_false, ite_true, false_and, iff_false]
    omega
  · simp only [Bool.false_eq_true, ite_false, ite_true, Bool.true_eq_false, false_and, iff_false]
    omega
  · simp only [ite_true, true_and, Fin.ext_iff]
    omega

end Cslib.Complexity.CSP
