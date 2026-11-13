/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Lifting

/-! The algebraic converse on actual edge and point components, and a torus obstruction. -/

open Cslib.Complexity Graph Graph.RotationSystem

private abbrev edgeAndPoint : Graph := ⟨[0, 1, 8, 8], [(0, 1)]⟩

private def edgeRotation : RotationSystem edgeAndPoint where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- Every edge bit has explicit endpoint spins. This derives numerical genus zero by
-- the new converse, without taking an Euler or genus certificate as a premise.
example : edgeRotation.NumericalGenusZero := by
  apply edgeRotation.numericalGenusZero_of_faceEven_lifts (by decide)
  intro x _
  refine ⟨fun v => if v = 1 then x 0 else false, ?_⟩
  funext i
  have hi : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have h : i.val < 1 := i.isLt
    omega
  subst i
  simp [edgeGradient, Dart.vertex, Graph.edgeEndpoint]

private abbrev points : Graph := ⟨[2 ^ 250, 7, 7], []⟩

private def pointRotation : RotationSystem points where
  rotate := Equiv.refl _
  sameCycle_iff d := d.1.elim0

-- Restriction to incident components is empty. The theorem retains the separate point
-- convention, with no finite universe on the sparse natural-number names.
example : pointRotation.NumericalGenusZero := by
  apply pointRotation.numericalGenusZero_of_faceEven_lifts (by decide)
  intro x _
  exact ⟨fun _ => false, funext fun i => i.elim0⟩

private abbrev torus : Graph := ⟨[0, 9], [(0, 0), (0, 0)]⟩

private def torusRotation : RotationSystem torus where
  rotate := ((Dart.indexEquiv torus).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv torus).symm
  sameCycle_iff := by decide +kernel

-- The converse cannot incorrectly identify the torus as genus zero: its universal
-- lifting premise is false. The unchanged forward implication still accepts gradients.
example : ¬ ∀ x : Fin torus.2.length → Bool, torusRotation.FaceEven x →
    ∃ spin : ℕ → Bool, torus.edgeGradient spin = x := by
  intro h
  have hG : ∀ v ∈ torus.incidenceVertices, v ∈ torus.1 := by decide
  have hg := torusRotation.numericalGenusZero_of_faceEven_lifts hG h
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation torusRotation hG)).mpr
      ((RotationCertificate.decode_ofRotation torusRotation hG).symm ▸ hg)
  exact (by decide : RotationCertificate.verifyEuler torus
    (RotationCertificate.ofRotation torusRotation) ≠ true) he

example (spin : ℕ → Bool) : torusRotation.FaceEven (torus.edgeGradient spin) :=
  torusRotation.faceEven_edgeGradient spin
