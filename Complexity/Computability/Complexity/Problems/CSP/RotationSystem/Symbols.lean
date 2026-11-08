/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Complexity.Logics.Propositional.CSP.Occurrence.Symbols

/-!
# Ordered incidence certificates under relation-symbol maps

The incidence graph and exact argument-order checker depend on the positional scopes.
Relation-symbol maps therefore retain the same accepted raw certificate. These structural
facts permit tags for the exterior probe; arity and SAT semantics remain separate properties
of an actual language interpretation.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel Other V : Type} [DecidableEq V]

/-- A symbol map leaves every actual listed vertex and indexed edge unchanged. -/
theorem incidenceGraph_mapRelation (F : CSP Rel V) (f : Rel → Other) :
    incidenceGraph (F.map fun (r, scope) => (f r, scope)) = incidenceGraph F := by
  simp only [incidenceGraph, CSP.varCNF_mapRelation]

omit [DecidableEq V] in
/-- The native position table is unchanged by a relation-symbol map. -/
theorem argumentPositions_mapRelation (F : CSP Rel V) (f : Rel → Other) :
    argumentPositions (F.map fun (r, scope) => (f r, scope)) = argumentPositions F := by
  simp only [argumentPositions, CSP.occurrences_mapRelation]

omit [DecidableEq V] in
/-- Scope widths are retained at every position, including missing and nullary entries. -/
theorem scopeLength_mapRelation (F : CSP Rel V) (f : Rel → Other) (i : ℕ) :
    scopeLength (F.map fun (r, scope) => (f r, scope)) i = scopeLength F i := by
  simp [scopeLength, List.map_map, Function.comp_def]

omit [DecidableEq V] in
/-- The argument-order check retains its literal result on every raw table. -/
theorem verifyArgumentOrder_mapRelation (F : CSP Rel V) (f : Rel → Other)
    (c : Graph.RotationCertificate) :
    verifyArgumentOrder (F.map fun (r, scope) => (f r, scope)) c = verifyArgumentOrder F c := by
  simp only [verifyArgumentOrder, CSP.occurrences_mapRelation, argumentNextIndex,
    argumentPositions_mapRelation, scopeLength_mapRelation]
  rfl

/-- Symbol maps keep the exact acceptance result, without changing any scope or dart. -/
theorem verifyRotationCertificate_mapRelation (F : CSP Rel V) (f : Rel → Other)
    (c : Graph.RotationCertificate) :
    verifyRotationCertificate (F.map fun (r, scope) => (f r, scope)) c =
      verifyRotationCertificate F c := by
  rw [verifyRotationCertificate, verifyRotationCertificate, incidenceGraph_mapRelation,
    verifyArgumentOrder_mapRelation]

end Cslib.Complexity.CSP
