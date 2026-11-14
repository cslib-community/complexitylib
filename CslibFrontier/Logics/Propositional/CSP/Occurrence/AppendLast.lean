/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence
import CslibFrontier.Logics.Propositional.CNF.ModelCount

/-!
# Appending an argument to the last indexed constraint

The actual ordered occurrence list gains one final record, retaining every previous
constraint/scope position even with repeated variables or identical constraints. This
original list identity is independent of incidence graphs and relation semantics.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- Appending one argument to the last constraint appends exactly one occurrence record.
Repeated variables and identical constraints remain indexed rather than deduplicated. -/
theorem occurrences_append_last_argument {Rel V : Type} (F : CSP Rel V) (r : Rel)
    (scope : List V) (v : V) :
    (F ++ [Constraint.mk r (scope ++ [v])]).occurrences =
      (F ++ [Constraint.mk r scope]).occurrences ++ [(F.length, scope.length, v)] := by
  simp [CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences,
    List.zipIdx_append, List.zipIdx_map, List.flatMap_append, List.map_flatMap,
    List.map_map, Function.comp_def]

end Cslib.Logic.PL.CSP
