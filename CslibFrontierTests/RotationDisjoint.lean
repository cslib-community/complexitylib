/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus

/-! Exact disjoint blocks include sparse names, loops, repeated declarations and empty blocks. -/

namespace CslibFrontierTests.RotationDisjoint

open Cslib.Complexity Graph.RotationSystem

private abbrev G : Graph := ([1000, 100000, 7, 9, 9], [(1000, 100000), (7, 7)])
private abbrev c : Graph.RotationCertificate := ⟨[0, 1, 3, 2]⟩
private noncomputable def r : Graph.RotationSystem G :=
  Graph.RotationCertificate.decode G c (by decide)

private theorem genus : r.NumericalGenusZero :=
  (Graph.RotationCertificate.verifyEuler_eq_true_iff (by decide :
    Graph.RotationCertificate.verifyRotation G c = true)).mp (by decide)

-- Two copies with equal old names occupy disjoint parity-tagged blocks, without deduplication.
example : (G.disjointUnion G).1 =
    [2000, 200000, 14, 18, 18, 2001, 200001, 15, 19, 19] := rfl

example : (G.disjointUnion G).2 =
    [(2000, 200000), (14, 14), (2001, 200001), (15, 15)] := rfl

example : Graph.RotationCertificate.ofRotation (r.disjointUnion r) =
    ⟨[0, 1, 3, 2, 4, 5, 7, 6]⟩ := by decide +kernel

example : (r.disjointUnion r).NumericalGenusZero :=
  numericalGenusZero_disjointUnion r r (by decide) (by decide) genus genus

example : Graph.RotationCertificate.verifyGenusZero (G.disjointUnion G)
    ⟨[0, 1, 3, 2, 4, 5, 7, 6]⟩ = true := by decide

private abbrev h : Graph.Dart (G.disjointUnion G) :=
  Graph.disjointDartEquiv G G (Sum.inl (0, false))
private abbrev k : Graph.Dart (G.disjointUnion G) :=
  Graph.disjointDartEquiv G G (Sum.inr (0, false))

private theorem different : ¬ Graph.RotationCertificate.SameComponent
    (G.disjointUnion G) h.vertex k.vertex := by
  rw [sameComponent_disjointUnion_iff (by decide) (by decide)]
  exact not_false

-- The join's different-component premise is derived from the actual disjoint coordinates.
example : ((r.disjointUnion r).mergeVertices h k (by decide)).NumericalGenusZero :=
  numericalGenusZero_mergeVertices_of_not_sameComponent _
    (Graph.endpoints_declared_disjointUnion G G (by decide) (by decide))
    (numericalGenusZero_disjointUnion r r (by decide) (by decide) genus genus)
    h k (by decide) different

example : Graph.RotationCertificate.ofRotation
    ((r.disjointUnion r).mergeVertices h k (by decide)) =
      ⟨[4, 1, 3, 2, 0, 5, 7, 6]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero (mergeGraph h k)
    ⟨[4, 1, 3, 2, 0, 5, 7, 6]⟩ = true := by decide

private def emptyRotation : Graph.RotationSystem (([99, 99], []) : Graph) where
  rotate := Equiv.refl _
  sameCycle_iff d := Fin.elim0 d.1

private theorem emptyGenus : emptyRotation.NumericalGenusZero := by
  apply (emptyRotation.numericalGenusZero_iff_component_cards (by decide)).mpr
  intro d
  exact Fin.elim0 d.1

example : (emptyRotation.disjointUnion r).NumericalGenusZero :=
  numericalGenusZero_disjointUnion _ _ (by decide) (by decide) emptyGenus genus

example : Graph.RotationCertificate.ofRotation (emptyRotation.disjointUnion r) =
    ⟨[0, 1, 3, 2]⟩ := by decide +kernel

example : (r.disjointUnion emptyRotation).NumericalGenusZero :=
  numericalGenusZero_disjointUnion _ _ (by decide) (by decide) genus emptyGenus

end CslibFrontierTests.RotationDisjoint
