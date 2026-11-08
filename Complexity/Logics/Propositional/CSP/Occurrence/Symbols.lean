/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence

/-!
# Occurrences under relation-symbol maps

Changing constraint symbols while retaining their scopes keeps the exact positive-CNF
adapter and indexed occurrence list. Duplicate constraints remain separate positions.
These original structural identities have no hypothesis about relation semantics.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- Relation-symbol maps retain the literal positive-clause adapter. -/
theorem varCNF_mapRelation {Rel Other V : Type} (F : CSP Rel V) (f : Rel → Other) :
    CSP.varCNF (F.map fun (r, scope) => (f r, scope)) = F.varCNF := by
  simp [CSP.varCNF, List.map_map, Function.comp_def]

/-- Every indexed argument record stays unchanged under a relation-symbol map. -/
theorem occurrences_mapRelation {Rel Other V : Type} (F : CSP Rel V) (f : Rel → Other) :
    CSP.occurrences (F.map fun (r, scope) => (f r, scope)) = F.occurrences := by
  simp only [CSP.occurrences, varCNF_mapRelation]

end Cslib.Logic.PL.CSP
