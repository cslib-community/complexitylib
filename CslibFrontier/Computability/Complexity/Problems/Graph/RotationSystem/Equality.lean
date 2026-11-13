/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport

/-!
# Rotation transport across equality of listed graphs

The explicit edge/end equivalence `graphEqDartEquiv` changes neither the generated certificate
nor numerical genus. Equality elimination proves these facts without unfolding a concrete
graph-construction program during subsequent transport proofs.
`ext_rotate` identifies two rotations on the same graph from their literal successor permutations.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A rotation system is determined by its literal successor permutation. -/
@[ext] theorem ext_rotate {G : Graph} {r s : RotationSystem G} (h : r.rotate = s.rotate) :
    r = s := by
  cases r
  cases s
  cases h
  rfl

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
