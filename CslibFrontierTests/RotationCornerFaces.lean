/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerGenus

/-! Directed face surgery includes fixed points and joins distinct edge components. -/

namespace CslibFrontierTests.RotationCornerFaces

open Cslib.Complexity Graph.RotationSystem

private abbrev twoEdges : Graph := ([0, 1, 2, 3], [(0, 1), (2, 3)])

private def twoEdgeRotation : Graph.RotationSystem twoEdges where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

example : Graph.RotationCertificate.ofRotation
    (twoEdgeRotation.insertEdge (0, false) (1, false)) =
      ⟨[4, 1, 5, 3, 0, 2]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (cornerGraph (G := twoEdges) (0, false) (1, false))
      ⟨[4, 1, 5, 3, 0, 2]⟩ = true := by decide

example : Nat.card (twoEdgeRotation.insertEdge (0, false) (1, false)).Face + 1 =
    Nat.card twoEdgeRotation.Face :=
  card_faces_insertEdge_different_faces _ _ _ (by decide +kernel)

example : Nat.card (twoEdgeRotation.insertEdge (0, false) (0, false)).Face =
    Nat.card twoEdgeRotation.Face + 1 :=
  card_faces_insertEdge_cofacial _ _ _ Equiv.Perm.SameCycle.rfl

private abbrev mixed : Graph := ([0, 1, 2, 3, 4, 5], [(0, 1), (2, 3), (5, 5)])

private def mixedRotation : Graph.RotationSystem mixed where
  rotate := Equiv.swap (2, false) (2, true)
  sameCycle_iff := by decide +kernel

private theorem mixedGenus : mixedRotation.NumericalGenusZero := by
  have hG : ∀ v ∈ mixed.incidenceVertices, v ∈ mixed.1 := by decide
  have h := (Graph.RotationCertificate.verifyEuler_eq_true_iff
    (Graph.RotationCertificate.verifyRotation_ofRotation mixedRotation hG)).mp (by decide)
  exact Graph.RotationCertificate.decode_ofRotation mixedRotation hG ▸ h

-- Coincident corners in one component preserve the separate edge, closed loop and point.
example : (mixedRotation.insertEdge (0, false) (0, false)).NumericalGenusZero :=
  numericalGenusZero_insertEdge _ (by decide) mixedGenus _ _ Equiv.Perm.SameCycle.rfl

example : (mixedRotation.insertEdge (0, false) (0, true)).NumericalGenusZero :=
  numericalGenusZero_insertEdge _ (by decide) mixedGenus _ _ (by decide +kernel)

end CslibFrontierTests.RotationCornerFaces
