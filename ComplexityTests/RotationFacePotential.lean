/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FacePotential
import Complexity.Foundations.GroupTheory.Perm.Fin

/-! Full finite cycles, nonconstant Boolean potentials, and their distinction from vertex spins. -/

open Cslib Cslib.Complexity Graph Graph.RotationSystem

example : (permutationRotation (1 : Equiv.Perm (Fin 3))).NumericalGenusZero :=
  numericalGenusZero_permutationRotation _

example : RotationCertificate.ofRotation (permutationRotation (1 : Equiv.Perm (Fin 3))) =
    ⟨[1, 0, 3, 2, 5, 4]⟩ := by decide +kernel

example : RotationCertificate.verifyGenusZero (permutationGraph (1 : Equiv.Perm (Fin 3)))
    ⟨[1, 0, 3, 2, 5, 4]⟩ = true := by decide +kernel

example : RotationCertificate.verifyGenusZero (permutationGraph (Equiv.swap (0 : Fin 2) 1))
    (RotationCertificate.ofRotation (permutationRotation (Equiv.swap (0 : Fin 2) 1))) = true := by
  decide +kernel

example : (permutationRotation (1 : Equiv.Perm (Fin 0))).NumericalGenusZero :=
  numericalGenusZero_permutationRotation _

-- Two marked positions on a genuine three-cycle have even sum and admit a nonconstant
-- cyclic potential; a marked singleton fixed point does not admit such a potential.
example : ∃ p : Fin 3 → Bool, ∀ i, decide (i.val < 2) = (p i ^^ p (finRotate 3 i)) := by
  apply exists_potential_of_cycleSum_zero
  intro i
  simp only [Equiv.Perm.sameCycle_finRotate, ite_true]
  decide +kernel

example : ¬ ∃ p : Fin 1 → Bool, ∀ i, true = (p i ^^ p ((1 : Equiv.Perm (Fin 1)) i)) := by
  rintro ⟨p, hp⟩
  have h := hp 0
  simp only [Equiv.Perm.one_apply, Bool.xor_self, Bool.true_eq_false] at h

private abbrev torus : Graph := ([0], [(0, 0), (0, 0)])

private def torusRotation : RotationSystem torus where
  rotate := ((Dart.indexEquiv torus).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv torus).symm
  sameCycle_iff := by decide +kernel

private def badLabel (i : Fin 2) : Bool := decide (i = 0)

private theorem torusEven : torusRotation.FaceEven badLabel := by
  apply (torusRotation.faceEven_iff_dart badLabel).mpr
  intro d
  have hc : ∀ d e : Dart torus, torusRotation.faceNext.SameCycle d e := by decide +kernel
  rw [torusRotation.faceParity_mk]
  simp only [hc, Finset.filter_true, parityOn_eq_sum]
  decide +kernel

example : ∃ p : Dart torus → Bool, ∀ d,
    badLabel d.1 = (p d ^^ p (torusRotation.faceNext d)) :=
  torusRotation.exists_facePotential_of_faceEven badLabel torusEven

example : ¬ ∃ spin : ℕ → Bool, torus.edgeGradient spin = badLabel := by
  rintro ⟨spin, he⟩
  have h := congrFun he 0
  simp [edgeGradient, Dart.vertex, Graph.edgeEndpoint, badLabel] at h
