/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus

/-! Different-component vertex joins retain parallel occurrences, a closed loop and points. -/

namespace CslibFrontierTests.RotationVertexJoin

open Cslib.Complexity Graph.RotationSystem

private abbrev G : Graph :=
  ([0, 1, 2, 3, 4, 5, 6, 6], [(0, 1), (0, 1), (2, 3), (2, 3), (4, 4)])

private abbrev c : Graph.RotationCertificate := ⟨[2, 3, 0, 1, 6, 7, 4, 5, 9, 8]⟩

private noncomputable def r : Graph.RotationSystem G :=
  Graph.RotationCertificate.decode G c (by decide)

private theorem genus : r.NumericalGenusZero :=
  (Graph.RotationCertificate.verifyEuler_eq_true_iff (by decide :
    Graph.RotationCertificate.verifyRotation G c = true)).mp (by decide)

private abbrev h : Graph.Dart G := (0, false)
private abbrev k : Graph.Dart G := (2, false)

-- The source has two genuinely nontrivial, distinct components, plus a loop and two points.
private theorem different : ¬ Graph.RotationCertificate.SameComponent G h.vertex k.vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : (r.mergeVertices h k (by decide)).NumericalGenusZero :=
  numericalGenusZero_mergeVertices_of_not_sameComponent r (by decide) genus h k
    (by decide) different

-- The exact successor list is the source list with precisely the two outgoing entries swapped.
example : Graph.RotationCertificate.ofRotation (r.mergeVertices h k (by decide)) =
    ⟨[6, 3, 0, 1, 2, 7, 4, 5, 9, 8]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero (mergeGraph h k)
    ⟨[6, 3, 0, 1, 2, 7, 4, 5, 9, 8]⟩ = true := by decide

example : (mergeGraph h k).2 = [(0, 1), (0, 1), (0, 3), (0, 3), (4, 4)] := rfl

example : (mergeGraph h k).1 = [0, 1, 0, 3, 4, 5, 6, 6] := rfl

-- Both parallel-edge components are joined, while the loop remains separate.
example : Graph.RotationCertificate.SameComponent (mergeGraph h k)
    (mergeDartEquiv h k (1, true)).vertex (mergeDartEquiv h k (3, true)).vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : ¬ Graph.RotationCertificate.SameComponent (mergeGraph h k)
    (mergeDartEquiv h k h).vertex (mergeDartEquiv h k (4, false)).vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : 5 ∉ (mergeGraph h k).incidenceVertices := by decide

-- Different components are essential: opposite corners of this planar dipole share no face.
private abbrev dipole : Graph := ([0, 1], [(0, 1), (0, 1), (0, 1)])
private abbrev dipoleTable : Graph.RotationCertificate := ⟨[2, 5, 4, 1, 0, 3]⟩
private noncomputable def dipoleRotation : Graph.RotationSystem dipole :=
  Graph.RotationCertificate.decode dipole dipoleTable (by decide)

example : Graph.RotationCertificate.verifyGenusZero dipole dipoleTable = true := by decide

example : Graph.RotationCertificate.verifyGenusZero
    (mergeGraph (G := dipole) (0, false) (0, true))
    (Graph.RotationCertificate.ofRotation
      (dipoleRotation.mergeVertices (0, false) (0, true) (by decide))) = false := by
  decide +kernel

end CslibFrontierTests.RotationVertexJoin
