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
# A trailing nullary constraint has no argument occurrences

These structural identities retain all earlier constraint positions and repeated variables.
They make no satisfiability assertion: the interpretation of the nullary relation is separate.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- Appending a nullary scope leaves the variable-occurrence word unchanged. -/
theorem vars_append_nullary {Rel V : Type} (F : CSP Rel V) (r : Rel) :
    (F ++ [Constraint.mk r []]).vars = F.vars := by
  simp [CSP.vars]

/-- A trailing nullary constraint contributes no indexed argument record. -/
theorem occurrences_append_nullary {Rel V : Type} (F : CSP Rel V) (r : Rel) :
    (F ++ [Constraint.mk r []]).occurrences = F.occurrences := by
  simp [CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences,
    List.zipIdx_append, List.flatMap_append]

/-- First-occurrence variable names remain literal when a nullary scope is appended. -/
theorem distinctVars_append_nullary {Rel V : Type} [DecidableEq V] (F : CSP Rel V) (r : Rel) :
    (F ++ [Constraint.mk r []]).distinctVars = F.distinctVars := by
  simp only [CSP.distinctVars, vars_append_nullary]

/-- Nullary constraints do not introduce variable names. -/
theorem numVars_append_nullary {Rel V : Type} [DecidableEq V] (F : CSP Rel V) (r : Rel) :
    (F ++ [Constraint.mk r []]).numVars = F.numVars := by
  simp only [CSP.numVars, vars_append_nullary]

end Cslib.Logic.PL.CSP
