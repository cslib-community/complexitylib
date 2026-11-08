/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Transport

/-! Actual dart reindexing, vertex-name changes and extra declared point components. -/

namespace ComplexityTests.RotationTransport

open Cslib.Complexity Graph.RotationSystem

private abbrev G : Graph := ([0, 1, 2, 3, 4, 5], [(0, 1), (2, 3), (5, 5)])
private abbrev H : Graph :=
  ([100, 200, 300, 400, 500, 600, 999, 999], [(600, 600), (300, 400), (100, 200)])

private def r : Graph.RotationSystem G where
  rotate := Equiv.swap (2, false) (2, true)
  sameCycle_iff := by decide +kernel

private def coordinates : Graph.Dart G ≃ Graph.Dart H :=
  Equiv.prodCongr ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ (Equiv.refl Bool)

private theorem vertexFibers : ∀ a b : Graph.Dart G,
    (coordinates a).vertex = (coordinates b).vertex ↔ a.vertex = b.vertex := by decide +kernel

private theorem reversal : ∀ a : Graph.Dart G,
    coordinates a.reverse = (coordinates a).reverse := by decide +kernel

private theorem genus : r.NumericalGenusZero := by
  have hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1 := by decide
  have h := (Graph.RotationCertificate.verifyEuler_eq_true_iff
    (Graph.RotationCertificate.verifyRotation_ofRotation r hG)).mp (by decide)
  exact Graph.RotationCertificate.decode_ofRotation r hG ▸ h

example : Graph.RotationCertificate.ofRotation (r.transport coordinates vertexFibers) =
    ⟨[1, 0, 2, 3, 4, 5]⟩ := by decide +kernel

example : (r.transport coordinates vertexFibers).NumericalGenusZero :=
  numericalGenusZero_transport r coordinates vertexFibers reversal (by decide) (by decide) genus

example : Graph.RotationCertificate.verifyGenusZero H ⟨[1, 0, 2, 3, 4, 5]⟩ = true := by decide

end ComplexityTests.RotationTransport
