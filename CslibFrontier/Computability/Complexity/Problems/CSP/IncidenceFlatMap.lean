/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidencePrefix
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.FlatMap

/-!
# Actual edge offsets in concatenated CSP bodies

The original incidence edge index commutes with literal body concatenation: each local edge
shifts by exactly the preceding bodies' occurrence count. No constraints or names are identified.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- The actual incidence edge of a copied occurrence has precisely the original local edge
index plus the preceding bodies' variable-word length. -/
theorem incidenceEdgeIndex_flatMapOccurrence {α Rel V : Type} [DecidableEq V]
    (l : List α) (f : α → CSP Rel V) (i : Fin l.length)
    (o : (f l[i.val]).Occurrence) :
    incidenceEdgeIndex (CSP.flatMapOccurrence l f i o) =
      (CSP.vars ((l.take i.val).flatMap f)).length + incidenceEdgeIndex o := by
  rw [incidenceEdgeIndex_eq_prefix]
  change (CSP.vars ((l.flatMap f).take (((l.take i.val).flatMap f).length + o.1.val))).length +
    o.2.val = _
  rw [List.take_flatMap_prefix_add l f i.isLt (Nat.le_of_lt o.1.isLt)]
  simp only [CSP.vars, List.flatMap_append, List.length_append]
  rw [incidenceEdgeIndex_eq_prefix]
  exact Nat.add_assoc _ _ _

end Cslib.Complexity.CSP
