/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Nullary
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.PointDeclarations
import Mathlib.Data.List.GetD

/-!
# Ordered certificates and a trailing isolated constraint center

A trailing nullary constraint adds a declared point and no darts. The actual componentwise
numerical convention accepts that point separately; the supplied table and all original
argument rotations are retained. This is structural and does not erase the nullary relation
from satisfiability semantics.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph Graph.RotationSystem

variable {Rel V : Type} [DecidableEq V]

/-- A trailing nullary adds exactly one isolated constraint declaration. -/
theorem incidenceGraph_append_nullary (F : CSP Rel V) (r : Rel) :
    incidenceGraph (F ++ [Constraint.mk r []]) =
      ⟨(incidenceGraph F).vertices ++ [F.numVars + F.length], (incidenceGraph F).edges⟩ := by
  apply Graph.ext
  · simp only [incidenceGraph_vertices, CSP.numVars_append_nullary, List.length_append,
      List.length_singleton, ← Nat.add_assoc, List.range_succ]
  · simp only [incidenceGraph_edges, CSP.occurrences_append_nullary,
      CSP.distinctVars_append_nullary, CSP.numVars_append_nullary]

omit [DecidableEq V] in
/-- The extra zero-width entry agrees even with the length reader's missing-entry default. -/
theorem scopeLength_append_nullary (F : CSP Rel V) (r : Rel) (i : ℕ) :
    scopeLength (F ++ [Constraint.mk r []]) i = scopeLength F i := by
  unfold scopeLength
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_nil]
  by_cases hi : i < F.length
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
    rw [List.getD_eq_default (F.map fun c => c.scope.length) 0
      (by simpa using Nat.le_of_not_gt hi)]
    cases i - F.length <;> simp

omit [DecidableEq V] in
/-- Every original clockwise argument successor is unchanged on the very same raw table. -/
theorem verifyArgumentOrder_append_nullary (F : CSP Rel V) (r : Rel)
    (c : RotationCertificate) :
    verifyArgumentOrder (F ++ [Constraint.mk r []]) c = verifyArgumentOrder F c := by
  simp only [verifyArgumentOrder, CSP.occurrences_append_nullary, argumentNextIndex,
    argumentPositions, scopeLength_append_nullary]
  rfl

/-- Appending or removing an isolated nullary constraint retains the exact accepted raw
ordered numerical certificate. Its truth value under relation semantics is not asserted. -/
theorem verifyRotationCertificate_append_nullary (F : CSP Rel V) (r : Rel)
    (c : RotationCertificate) :
    verifyRotationCertificate (F ++ [Constraint.mk r []]) c = verifyRotationCertificate F c := by
  have he : (incidenceGraph (F ++ [Constraint.mk r []])).edges = (incidenceGraph F).edges :=
    by simpa only using
      congrArg (fun G : Graph => G.edges) (incidenceGraph_append_nullary F r)
  have hg := RotationCertificate.verifyGenusZero_eq_of_edges_eq he
    (incidenceVertices_declared (F ++ [Constraint.mk r []])) (incidenceVertices_declared F) c
  simp only [verifyRotationCertificate, verifyArgumentOrder_append_nullary, hg]

end Cslib.Complexity.CSP
