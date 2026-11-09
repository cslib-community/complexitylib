/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerInsertion
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-! Actual indexed graph regressions for oriented corner insertion. -/

namespace CslibFrontierTests.RotationCornerInsertion

open Cslib.Complexity
open Graph.RotationSystem

private abbrev edge : Graph := ([0, 1], [(0, 1)])

private def edgeRotation : Graph.RotationSystem edge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- Coincident corners create a loop with two distinct new ends, in the documented order.
example : (edgeRotation.insertEdge (0, false) (0, false)).rotate
    (oldCornerDart (G := edge) (0, false) (0, false) (0, false)) =
      newCornerDart (G := edge) (0, false) (0, false) true :=
  rotate_insertEdge_at_right _ _ _

example : Graph.RotationCertificate.ofRotation
    (edgeRotation.insertEdge (0, false) (0, false)) = ⟨[3, 1, 0, 2]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (cornerGraph (G := edge) (0, false) (0, false)) ⟨[3, 1, 0, 2]⟩ = true := by decide

-- Distinct endpoint corners append a parallel edge without collapsing occurrences.
example : Graph.RotationCertificate.ofRotation
    (edgeRotation.insertEdge (0, false) (0, true)) = ⟨[2, 3, 0, 1]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (cornerGraph (G := edge) (0, false) (0, true)) ⟨[2, 3, 0, 1]⟩ = true := by decide

private abbrev loop : Graph := ([0], [(0, 0)])

private def loopRotation : Graph.RotationSystem loop where
  rotate := Equiv.swap (0, false) (0, true)
  sameCycle_iff := by decide +kernel

-- Different corners at the same vertex can lie on different faces. This insertion is toroidal;
-- endpoint equality alone must never be accepted as the face-location hypothesis.
example : Graph.RotationCertificate.ofRotation
    (loopRotation.insertEdge (0, false) (0, true)) = ⟨[2, 3, 1, 0]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (cornerGraph (G := loop) (0, false) (0, true)) ⟨[2, 3, 1, 0]⟩ = false := by decide

-- A fixed point survives insertion as an actual two-element cycle.

end CslibFrontierTests.RotationCornerInsertion
