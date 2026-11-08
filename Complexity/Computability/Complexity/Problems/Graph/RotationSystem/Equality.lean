/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Transport

/-!
# Rotation transport across equality of listed graphs

The explicit edge/end equivalence `graphEqDartEquiv` changes neither the generated certificate
nor numerical genus. Equality elimination proves these facts without unfolding a concrete
graph-construction program during subsequent transport proofs.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Equality transport retains the exact generated successor list. -/
theorem ofRotation_graphEqDartEquiv {G H : Graph} (r : RotationSystem G) (h : G = H) :
    RotationCertificate.ofRotation (r.transport (graphEqDartEquiv h)
      (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])) =
        RotationCertificate.ofRotation r := by
  cases h
  rfl

/-- Equality transport preserves the actual numerical genus predicate without an
endpoint-declaration premise, because the listed graphs are literally equal. -/
theorem numericalGenusZero_graphEqDartEquiv {G H : Graph} (r : RotationSystem G) (h : G = H) :
    (r.transport (graphEqDartEquiv h)
      (by intro a b; rw [vertex_graphEqDartEquiv, vertex_graphEqDartEquiv])).NumericalGenusZero ↔
        r.NumericalGenusZero := by
  cases h
  rfl

end Cslib.Complexity.Graph.RotationSystem
