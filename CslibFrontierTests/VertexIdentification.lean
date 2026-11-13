/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMergeGenus

/-! Active transpositions, nonconstant selections and literal vertex-identification tables. -/

namespace CslibFrontierTests.VertexIdentification

open Cslib.Complexity Graph.RotationSystem

private abbrev edge : Graph := ⟨[0, 1, 8], [(0, 1)]⟩

private def edgeRotation : Graph.RotationSystem edge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

example : Graph.RotationCertificate.ofRotation
    (edgeRotation.mergeVertices (0, false) (0, true) (by decide)) = ⟨[1, 0]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (mergeGraph (G := edge) (0, false) (0, true)) ⟨[1, 0]⟩ = true := by decide

example : Nat.card (ComponentFace
      (edgeRotation.mergeVertices (0, false) (0, true) (by decide)) 0) =
    Nat.card (ComponentFace edgeRotation 0) + 1 := by
  have h := card_componentFace_mergeVertices edgeRotation (by decide) (0, false) (0, true)
    (by decide) (by decide +kernel) (0, false)
  rw [vertex_mergeDartEquiv] at h
  have hv : Graph.Dart.vertex (G := edge) (0, false) = 0 := by decide
  have ht : Graph.Dart.vertex (G := edge) (0, true) = 1 := by decide
  have hself : Graph.RotationCertificate.SameComponent edge
      (Graph.Dart.vertex (G := edge) (0, false))
      (Graph.Dart.vertex (G := edge) (0, false)) := .refl (by decide)
  rw [ite_eq_left hself] at h
  simpa only [hv, ht, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1), id_eq] using h

-- The generic genus proof retains the separately declared point at 8.
example : (edgeRotation.mergeVertices (0, false) (0, true) (by decide)).NumericalGenusZero := by
  have hG : ∀ v ∈ edge.incidenceVertices, v ∈ edge.1 := by decide
  have hr : edgeRotation.NumericalGenusZero := by
    have h := (Graph.RotationCertificate.verifyEuler_eq_true_iff
      (Graph.RotationCertificate.verifyRotation_ofRotation edgeRotation hG)).mp (by decide)
    exact Graph.RotationCertificate.decode_ofRotation edgeRotation hG ▸ h
  exact edgeRotation.numericalGenusZero_mergeVertices hG hr (0, false) (0, true)
    (by decide) (by decide +kernel)

private abbrev bigon : Graph := ⟨[0, 1], [(0, 1), (0, 1)]⟩

private def bigonRotation : Graph.RotationSystem bigon where
  rotate := Equiv.swap (0, false) (1, false) * Equiv.swap (0, true) (1, true)
  sameCycle_iff := by decide +kernel

-- These distinct vertices are in the same component but the chosen corners lie on
-- different faces. The computed identification is valid as a rotation and has positive genus.
example : Graph.RotationCertificate.ofRotation
    (bigonRotation.mergeVertices (0, false) (0, true) (by decide)) =
      ⟨[3, 2, 0, 1]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero
    (mergeGraph (G := bigon) (0, false) (0, true)) ⟨[3, 2, 0, 1]⟩ = false := by decide

end CslibFrontierTests.VertexIdentification
