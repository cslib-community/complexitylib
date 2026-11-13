/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.VertexSplitGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
import CslibFrontier.Foundations.GroupTheory.Perm.ListCycles
import CslibFrontier.Foundations.GroupTheory.Perm.ListSplice

/-! Directed successor words and an actual split with an untouched closed component and isolates. -/

namespace CslibFrontierTests.RotationSubstitutionSurgery

open Cslib.Complexity Graph Graph.RotationSystem

example : List.nextInCycles [[], [3], [1, 4, 2], []] 4 = 2 := by decide

example : List.nextInCycles [[], [3], [1, 4, 2], []] 2 = 1 := by decide

example : List.nextInCycles [[], [3], [1, 4, 2], []] 3 = 3 := by decide

example : List.nextInCycles [[], [3], [1, 4, 2], []] 99 = 99 := by decide

-- The retained word-surgery API fixes the actual outgoing-swap orientation.
example : (([0, 1] : List (Fin 4)) ++ [2, 3]).formPerm =
    ([0, 1] : List (Fin 4)).formPerm * ([2, 3] : List (Fin 4)).formPerm *
      Equiv.swap 1 3 :=
  List.formPerm_append_of_last_notMem (α := Fin 4)
    [0, 1] [2, 3] (by decide) (by decide) (by decide)

example : List.ofFn (fun i : Fin 4 => ([0, 1] ++ [2, 3]).formPerm i) =
    [1, 2, 3, 0] := by decide +kernel

example : ((([0] : List (Fin 4)) ++ [1, 2]) ++ [3]).formPerm =
    ([0, 3] : List (Fin 4)).formPerm * Equiv.swap 1 2 * Equiv.swap 0 2 :=
  List.formPerm_split_adjacent_pair (α := Fin 4) [0] [3] 1 2 (by decide) (by decide)

example : (List.cyclePermutation [[], [3], [1, 4, 2], []]).SameCycle 1 2 := by
  exact (List.sameCycle_cyclePermutation_iff_of_mem _ (by decide) [1, 4, 2]
    (by simp) 1 2 (by simp)).mpr (by simp)

private abbrev splitGraph : Graph :=
  ⟨[0, 1, 2, 3, 7, 99, 99], [(0, 2), (1, 3), (7, 7)]⟩

private def splitRotation : RotationSystem splitGraph where
  rotate := Equiv.swap ((⟨2, by decide⟩, false) : Dart splitGraph) (⟨2, by decide⟩, true)
  sameCycle_iff := by decide +kernel

private def h : Dart splitGraph := (⟨0, by decide⟩, false)
private def k : Dart splitGraph := (⟨1, by decide⟩, false)

private theorem splitGenus : splitRotation.NumericalGenusZero := by
  apply splitRotation.numericalGenusZero_of_mergeVertices h k (by decide) (by decide)
  let joined := splitRotation.mergeVertices h k (by decide)
  have hdecl : ∀ v ∈ (mergeGraph h k).incidenceVertices, v ∈ (mergeGraph h k).vertices := by
    decide
  have hc : RotationCertificate.verifyEuler (mergeGraph h k)
      (RotationCertificate.ofRotation joined) = true := by decide +kernel
  have hg := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation joined hdecl)).mp hc
  rwa [RotationCertificate.decode_ofRotation] at hg

-- The full original checker accepts the split rotation supplied by the generic inverse
-- merge theorem, rather than an unproved numerical-genus hypothesis.
example : RotationCertificate.verifyGenusZero splitGraph
    (RotationCertificate.ofRotation splitRotation) = true := by
  apply (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨RotationCertificate.verifyRotation_ofRotation splitRotation (by decide), ?_⟩
  rw [RotationCertificate.decode_ofRotation splitRotation (by decide)]
  exact splitGenus

example : RotationCertificate.ofRotation splitRotation = ⟨[0, 1, 2, 3, 5, 4]⟩ := by
  decide +kernel

-- The additive extensionality API is available through an ordinary import.
example : (splitRotation.insertEdge h k).deleteLastEdge = splitRotation :=
  deleteLastEdge_insertEdge splitRotation h k

end CslibFrontierTests.RotationSubstitutionSurgery
