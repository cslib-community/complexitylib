/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus

/-! Actual nonbridge contractions, directed loop blocks, empty blocks and point components. -/

namespace CslibFrontierTests.RotationContraction

open Cslib.Complexity Graph Graph.RotationSystem

private theorem checkedGenus {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (h : RotationCertificate.verifyEuler G (RotationCertificate.ofRotation r) = true) :
    r.NumericalGenusZero := by
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation r hG)).mp h
  exact RotationCertificate.decode_ofRotation r hG ▸ he

private abbrev residual : Graph := ([0, 1, 9, 99, 99], [(0, 0), (1, 1), (0, 1), (9, 9)])

private def nonbridge : RotationSystem (lastEdgeGraph residual 0 1) where
  rotate :=
    Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph residual 0 1))
      (⟨0, by decide⟩, true) *
    Equiv.swap ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph residual 0 1))
      (⟨2, by decide⟩, false) *
    Equiv.swap ((⟨2, by decide⟩, false) : Dart (lastEdgeGraph residual 0 1))
      (⟨4, by decide⟩, false) *
    Equiv.swap ((⟨1, by decide⟩, false) : Dart (lastEdgeGraph residual 0 1))
      (⟨1, by decide⟩, true) *
    Equiv.swap ((⟨1, by decide⟩, true) : Dart (lastEdgeGraph residual 0 1))
      (⟨4, by decide⟩, true) *
    Equiv.swap ((⟨4, by decide⟩, true) : Dart (lastEdgeGraph residual 0 1))
      (⟨2, by decide⟩, true) *
    Equiv.swap ((⟨3, by decide⟩, false) : Dart (lastEdgeGraph residual 0 1))
      (⟨3, by decide⟩, true)
  sameCycle_iff := by decide +kernel

-- The deleted connector has a parallel retained edge, so it is not a bridge. Loops at
-- both endpoints, the untouched loop component, and duplicate isolated names all remain.
example : RotationCertificate.ofRotation (nonbridge.contractLastEdge (by decide)) =
    ⟨[1, 4, 3, 0, 5, 2, 7, 6]⟩ := by decide +kernel

example : contractLastEdgeGraph residual 0 1 =
    ([1, 1, 9, 99, 99], [(1, 1), (1, 1), (1, 1), (9, 9)]) := by decide +kernel

example : (nonbridge.contractLastEdge (by decide)).NumericalGenusZero :=
  nonbridge.numericalGenusZero_contractLastEdge (by decide) (by decide)
    (checkedGenus nonbridge (by decide) (by decide +kernel))

example : RotationCertificate.verifyGenusZero (contractLastEdgeGraph residual 0 1)
    (RotationCertificate.ofRotation (nonbridge.contractLastEdge (by decide))) = true := by
  decide +kernel

-- The exact successor table distinguishes the retained directed word from its reflection.
example : (RotationCertificate.ofRotation (nonbridge.contractLastEdge (by decide))).successor ≠
    [3, 0, 5, 2, 1, 4, 7, 6] := by decide +kernel

private abbrev points : Graph := ([0, 1, 7, 7], [])

private def soleEdge : RotationSystem (lastEdgeGraph points 0 1) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- Both residual blocks are empty. The contracted component becomes a declared point;
-- its conventional face is not a nonexistent dart face.
example : RotationCertificate.ofRotation (soleEdge.contractLastEdge (by decide)) = ⟨[]⟩ := by
  decide +kernel

example : (soleEdge.contractLastEdge (by decide)).NumericalGenusZero :=
  soleEdge.numericalGenusZero_contractLastEdge (by decide) (by decide)
    (checkedGenus soleEdge (by decide) (by decide +kernel))

example : RotationCertificate.verifyGenusZero (contractLastEdgeGraph points 0 1) ⟨[]⟩ = true := by
  decide +kernel

private abbrev oneBlock : Graph := ([0, 1, 12], [(0, 0)])

private def pendant : RotationSystem (lastEdgeGraph oneBlock 0 1) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph oneBlock 0 1))
    (⟨0, by decide⟩, true) * Equiv.swap
      ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph oneBlock 0 1))
      (⟨1, by decide⟩, false)
  sameCycle_iff := by decide +kernel

-- One residual block is empty; the other contains both ends of an actual old loop.
example : RotationCertificate.ofRotation (pendant.contractLastEdge (by decide)) = ⟨[1, 0]⟩ := by
  decide +kernel

example : (pendant.contractLastEdge (by decide)).NumericalGenusZero :=
  pendant.numericalGenusZero_contractLastEdge (by decide) (by decide)
    (checkedGenus pendant (by decide) (by decide +kernel))


end CslibFrontierTests.RotationContraction
