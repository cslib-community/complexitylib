/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus
import CslibFrontier.Foundations.GroupTheory.Perm.RemoveNoneExtension

/-! General deletion on splitting bridges, pendant points, loops and untouched components. -/

namespace CslibFrontierTests.RotationDeletionComponents

open Cslib.Complexity Graph Graph.RotationSystem

private theorem checkedGenus {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (h : RotationCertificate.verifyEuler G (RotationCertificate.ofRotation r) = true) :
    r.NumericalGenusZero := by
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation r hG)).mp h
  exact RotationCertificate.decode_ofRotation r hG ▸ he

private abbrev mixed : Graph := ⟨[0, 1, 2, 3, 4, 99, 99], [(0, 1), (2, 3), (4, 4)]⟩

private def mixedSource : RotationSystem (lastEdgeGraph mixed 1 2) where
  rotate :=
    Equiv.swap ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph mixed 1 2)) (⟨3, by decide⟩, false) *
    Equiv.swap ((⟨1, by decide⟩, false) : Dart (lastEdgeGraph mixed 1 2)) (⟨3, by decide⟩, true) *
    Equiv.swap ((⟨2, by decide⟩, false) : Dart (lastEdgeGraph mixed 1 2)) (⟨2, by decide⟩, true)
  sameCycle_iff := by decide +kernel

-- The connector is an actual bridge joining two nontrivial edge components. The loop
-- component and duplicate-declared isolated point remain untouched.
example : mixedSource.deleteLastEdge.NumericalGenusZero :=
  mixedSource.numericalGenusZero_deleteLastEdge (by decide)
    (checkedGenus mixedSource (by decide) (by decide +kernel))

example : RotationCertificate.ofRotation mixedSource.deleteLastEdge = ⟨[0, 1, 2, 3, 5, 4]⟩ := by
  decide +kernel

example : RotationCertificate.verifyGenusZero mixed
    (RotationCertificate.ofRotation mixedSource.deleteLastEdge) = true := by decide +kernel

example : RotationCertificate.componentBool mixed 0 2 = false ∧
    RotationCertificate.componentBool mixed 0 1 = true ∧
      RotationCertificate.componentBool mixed 2 3 = true := by decide +kernel

private abbrev pendant : Graph := ⟨[0, 1, 2, 8], [(0, 1)]⟩

private def pendantSource : RotationSystem (lastEdgeGraph pendant 1 2) where
  rotate := Equiv.swap ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph pendant 1 2))
    (⟨1, by decide⟩, false)
  sameCycle_iff := by decide +kernel

example : pendantSource.deleteLastEdge.NumericalGenusZero :=
  pendantSource.numericalGenusZero_deleteLastEdge (by decide)
    (checkedGenus pendantSource (by decide) (by decide +kernel))

example : RotationCertificate.ofRotation pendantSource.deleteLastEdge = ⟨[0, 1]⟩ := by
  decide +kernel

example : ¬ ∃ d : Dart pendant, d.vertex = 2 := by decide +kernel

example : RotationCertificate.verifyGenusZero pendant
    (RotationCertificate.ofRotation pendantSource.deleteLastEdge) = true := by decide +kernel

private abbrev loopAndPoint : Graph := ⟨[0, 8], [(0, 0)]⟩

private def sphereLoops : RotationSystem (lastEdgeGraph loopAndPoint 0 0) where
  rotate := ((finCongr (show 4 = 2 * (lastEdgeGraph loopAndPoint 0 0).2.length by decide)).trans
    (Dart.indexEquiv (lastEdgeGraph loopAndPoint 0 0)).symm).permCongr (finRotate 4)
  sameCycle_iff := by decide +kernel

example : sphereLoops.deleteLastEdge.NumericalGenusZero :=
  sphereLoops.numericalGenusZero_deleteLastEdge (by decide)
    (checkedGenus sphereLoops (by decide) (by decide +kernel))

example : RotationCertificate.ofRotation sphereLoops.deleteLastEdge = ⟨[1, 0]⟩ := by decide +kernel

example : RotationCertificate.verifyGenusZero loopAndPoint
    (RotationCertificate.ofRotation sphereLoops.deleteLastEdge) = true := by decide +kernel

private abbrev onlyPoints : Graph := ⟨[0, 8], []⟩

private def soleLoop : RotationSystem (lastEdgeGraph onlyPoints 0 0) where
  rotate := Dart.reversal _
  sameCycle_iff := by decide +kernel

example : soleLoop.deleteLastEdge.NumericalGenusZero :=
  soleLoop.numericalGenusZero_deleteLastEdge (by decide)
    (checkedGenus soleLoop (by decide) (by decide +kernel))

example : RotationCertificate.ofRotation soleLoop.deleteLastEdge = ⟨[]⟩ := by decide +kernel

-- A removed permutation point is assigned its successor's value. This is nonconstant
-- on retained points and uses a genuine three-cycle, not a fixed or identity permutation.
private def threeCycle : Equiv.Perm (Option (Fin 2)) :=
  Equiv.swap (some 0) none * Equiv.swap (some 0) (some 1)

example : Equiv.Perm.extendRemoveNone threeCycle (fun i => decide (i = 0)) false none = true ∧
    Equiv.Perm.extendRemoveNone threeCycle (fun i => decide (i = 0)) false (some 1) = false := by
  decide +kernel

end CslibFrontierTests.RotationDeletionComponents
