/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.EdgeDeletion
import CslibFrontier.Foundations.GroupTheory.Perm.RemoveTwo

/-! Executed boundary restrictions with every removed-point visit pattern and full checkers. -/

namespace CslibFrontierTests.PlanarBoundaryRestriction

open Cslib.Complexity CSP.OrderedBoundary Graph Graph.RotationSystem

private abbrev loop : Graph := ⟨[0, 88, 88], [(0, 0)]⟩

private def firstOrder : RotationSystem (lastEdgeGraph loop 0 0) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph loop 0 0))
      (⟨1, by decide⟩, false) *
    Equiv.swap ((⟨1, by decide⟩, false) : Dart (lastEdgeGraph loop 0 0)) (⟨1, by decide⟩, true) *
    Equiv.swap ((⟨1, by decide⟩, true) : Dart (lastEdgeGraph loop 0 0)) (⟨0, by decide⟩, true)
  sameCycle_iff := by decide +kernel

private def secondOrder : RotationSystem (lastEdgeGraph loop 0 0) where
  rotate := firstOrder.rotate.symm
  sameCycle_iff := by decide +kernel

-- In one orientation the actual scan is 0 -> 2 -> 3 -> 1; in the other orientation
-- it is 1 -> 3 -> 2 -> 0. Both are genuine three-step first returns.
example : RotationCertificate.ofRotation firstOrder = ⟨[2, 0, 3, 1]⟩ ∧
    RotationCertificate.ofRotation secondOrder = ⟨[1, 3, 0, 2]⟩ := by decide +kernel

example : restrictPrefix 2 (RotationCertificate.ofRotation firstOrder) = ⟨[1, 0]⟩ ∧
    restrictPrefix 2 (RotationCertificate.ofRotation secondOrder) = ⟨[1, 0]⟩ := by decide +kernel

example : RotationCertificate.verifyGenusZero loop
    (restrictPrefix 2 (RotationCertificate.ofRotation firstOrder)) = true := by decide +kernel

example : RotationCertificate.verifyGenusZero loop
    (restrictPrefix 2 (RotationCertificate.ofRotation secondOrder)) = true := by decide +kernel

-- The public theorem ties the literal scan to the literal constructed rotation, rather
-- than merely asserting existence of some accepted target table.
example : restrictPrefix 2 (RotationCertificate.ofRotation firstOrder) =
    RotationCertificate.ofRotation firstOrder.deleteLastEdge :=
  restrictPrefix_ofRotation_deleteLastEdge firstOrder

private abbrev edge : Graph := ⟨[0, 1, 99], [(0, 1)]⟩

private def bigon : RotationSystem (lastEdgeGraph edge 0 1) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph edge 0 1))
    (⟨1, by decide⟩, false) * Equiv.swap
      ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph edge 0 1)) (⟨1, by decide⟩, true)
  sameCycle_iff := by decide +kernel

-- Both two-step paths occur, one through each deleted end.
example : RotationCertificate.ofRotation bigon = ⟨[2, 3, 0, 1]⟩ ∧
    restrictPrefix 2 (RotationCertificate.ofRotation bigon) = ⟨[0, 1]⟩ := by decide +kernel

example : RotationCertificate.verifyGenusZero edge
    (restrictPrefix 2 (RotationCertificate.ofRotation bigon)) = true := by decide +kernel

private abbrev points : Graph := ⟨[0, 1, 66, 66], []⟩

private def bridge : RotationSystem (lastEdgeGraph points 0 1) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

example : restrictPrefix 0 (RotationCertificate.ofRotation bridge) = ⟨[]⟩ ∧
    RotationCertificate.verifyGenusZero points
      (restrictPrefix 0 (RotationCertificate.ofRotation bridge)) = true := by decide +kernel

example : restrictPrefix 0 (RotationCertificate.ofRotation bridge) =
    RotationCertificate.ofRotation bridge.deleteLastEdge :=
  restrictPrefix_ofRotation_deleteLastEdge bridge

example : RotationCertificate.verifyGenusZero points
    (restrictPrefix 0 (RotationCertificate.ofRotation bridge)) = true := by
  apply verifyGenusZero_restrictPrefix_deleteLastEdge bridge (by decide)
  have h := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation bridge (by decide))).mp (by decide +kernel)
  exact RotationCertificate.decode_ofRotation bridge (by decide) ▸ h

-- An arbitrary permutation may fix either removed point. The generic result still
-- identifies the first retained successor and does not drop singleton cycles.
example : Equiv.removeNone (Equiv.removeNone
    (1 : Equiv.Perm (Option (Option Unit)))) () = () := by decide +kernel

-- The raw table need not be valid for a short-return equation. A huge binary successor
-- index is followed with fallback lookup; the clock remains the supplied four entries.
example : (restrictPrefix 2 ⟨[2 ^ 250, 1, 0, 0]⟩).successor = [0, 1] := by decide +kernel

-- The actual binary atom/probe table has one marker per free variable. Removing the last
-- marker first retains exactly the same final body table. One variable's return loses a
-- marker, the other's marker is retained in the intermediate prefix, and odd ends return
-- immediately. These are all three branches of the short-return composition proof.
example : restrictPrefix 4 (restrictPrefix 6 ⟨[6, 3, 4, 1, 2, 7, 0, 5]⟩) =
    restrictPrefix 4 ⟨[6, 3, 4, 1, 2, 7, 0, 5]⟩ := by
  apply restrictPrefix_restrictPrefix_of_short_returns _ _ _ (by decide) (by decide)
  intro i hi
  interval_cases i <;> decide +kernel

example : (restrictPrefix 4 (restrictPrefix 6 ⟨[6, 3, 4, 1, 2, 7, 0, 5]⟩)).successor =
    [0, 3, 2, 1] := by decide +kernel

-- The composition identity also has honest fallback behavior on raw malformed tables.
example : restrictPrefix 2 (restrictPrefix 4 ⟨[2 ^ 250, 1, 0, 0]⟩) =
    restrictPrefix 2 ⟨[2 ^ 250, 1, 0, 0]⟩ := by
  apply restrictPrefix_restrictPrefix_of_short_returns _ _ _ (by decide) (by decide)
  intro i hi
  interval_cases i <;> decide +kernel

end CslibFrontierTests.PlanarBoundaryRestriction
