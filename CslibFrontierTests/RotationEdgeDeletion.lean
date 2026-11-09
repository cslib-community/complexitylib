/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletionGenus
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import Mathlib.Tactic.FinCases

/-! Literal deletion, the matrix Euler bound, and separate point conventions. -/

namespace CslibFrontierTests.RotationEdgeDeletion

open Cslib.Complexity Graph Graph.RotationSystem

private abbrev bridge : Graph := ([0, 1], [(0, 1)])
private abbrev points : Graph := ([0, 1, 8, 8], [])

private def bridgeRotation : RotationSystem bridge where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- This is the actual matrix consequence on a planar edge component, with equality.
example : (bridge.componentVertexSet 0).card + (bridgeRotation.componentFaceIndices 0).card ≤
    (bridge.componentEdgeSet 0).card + 2 :=
  bridgeRotation.component_euler_le (by decide) (0, false)

private theorem bridgeGenus : bridgeRotation.NumericalGenusZero := by
  have hG : ∀ v ∈ bridge.incidenceVertices, v ∈ bridge.1 := by decide
  have h := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation bridgeRotation hG)).mp (by decide)
  exact RotationCertificate.decode_ofRotation bridgeRotation hG ▸ h

example : (bridge.componentVertexSet 0).card + (bridgeRotation.componentFaceIndices 0).card =
    (bridge.componentEdgeSet 0).card + 2 :=
  (bridgeRotation.numericalGenusZero_iff_component_cards (by decide)).mp bridgeGenus (0, false)

private abbrev torus : Graph := ([0, 9], [(0, 0), (0, 0)])

private def torusRotation : RotationSystem torus where
  rotate := ((Dart.indexEquiv torus).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv torus).symm
  sameCycle_iff := by decide +kernel

-- The universal bound is strict on this torus component. Point 9 contributes no dart.
example : (torus.componentVertexSet 0).card + (torusRotation.componentFaceIndices 0).card ≤
    (torus.componentEdgeSet 0).card + 2 :=
  torusRotation.component_euler_le (by decide) (0, false)

example : (torus.componentVertexSet 0).card + (torusRotation.componentFaceIndices 0).card <
    (torus.componentEdgeSet 0).card + 2 := by
  classical
  have hv : torus.componentVertexSet 0 = {0} := by
    ext v
    simp only [Graph.componentVertexSet, Finset.mem_filter, List.mem_toFinset,
      List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · rfl
      · have hbool :=
          (RotationCertificate.componentBool_eq_true_iff (by decide : 0 ∈ torus.1)).mpr h
        exact False.elim ((by decide : RotationCertificate.componentBool torus 0 9 ≠ true) hbool)
    · rintro rfl
      exact ⟨Or.inl rfl, .refl (by decide)⟩
  have hd (d : Dart torus) : d.vertex = 0 := by
    rcases d with ⟨i, b⟩
    fin_cases i <;> cases b <;> rfl
  have he : torus.componentEdgeSet 0 = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    rw [hd]
    exact .refl (by decide)
  have eqv : ComponentFace torusRotation 0 ≃ torusRotation.Face :=
    { toFun := Subtype.val
      invFun := fun f => ⟨f, Quotient.inductionOn f (fun d =>
        ⟨d, by rw [hd]; exact .refl (by decide), rfl⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf : Nat.card torusRotation.Face = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      intro a b
      refine Quotient.inductionOn₂ a b fun d e => Quotient.sound ?_
      exact (by decide +kernel : ∀ d e : Dart torus, torusRotation.faceNext.SameCycle d e) d e
    · exact ⟨Quotient.mk _ (0, false)⟩
  rw [hv, he, card_componentFaceIndices,
    torusRotation.count_faceRepresentatives_eq_card_componentFace (by decide),
    Nat.card_congr eqv, hf]
  decide

private def pointRotation : RotationSystem points where
  rotate := Equiv.refl _
  sameCycle_iff d := d.1.elim0

-- No application of the matrix theorem invents a point dart. The existing convention
-- handles all declared points, including duplicate declarations.
example : ¬ Nonempty (Dart points) := by rintro ⟨d⟩; exact d.1.elim0

example : pointRotation.NumericalGenusZero := by
  intro root _
  have hn : ¬ ∃ d : Dart points, d.vertex = root := by rintro ⟨d, -⟩; exact d.1.elim0
  simp only [hn, ite_false]

private def pointsWithBridge : RotationSystem (lastEdgeGraph points 0 1) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

example : RotationCertificate.ofRotation pointsWithBridge.deleteLastEdge = ⟨[]⟩ := by
  decide +kernel

example : RotationCertificate.verifyGenusZero points
    (RotationCertificate.ofRotation pointsWithBridge.deleteLastEdge) = true := by decide +kernel

example : pointsWithBridge.deleteLastEdge.NumericalGenusZero :=
  pointsWithBridge.numericalGenusZero_deleteLastEdge_of_no_edges rfl

private abbrev oneLoop : Graph := ([0], [(0, 0)])

private def sphereBigon : RotationSystem (lastEdgeGraph bridge 0 1) where
  rotate := (Equiv.prodCongr
    (finCongr (show 2 = (lastEdgeGraph bridge 0 1).2.length by decide)) (Equiv.refl Bool)).permCongr
      (Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool))
  sameCycle_iff := by decide +kernel

private theorem bigonGenus : sphereBigon.NumericalGenusZero := by
  have hG : ∀ v ∈ (lastEdgeGraph bridge 0 1).incidenceVertices,
      v ∈ (lastEdgeGraph bridge 0 1).1 := by decide
  have h := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation sphereBigon hG)).mp (by decide)
  exact RotationCertificate.decode_ofRotation sphereBigon hG ▸ h

-- Actual deletion consumes the universal bound to prove genus zero; its target certificate
-- and forward successor table are checked independently as well.
example : sphereBigon.deleteLastEdge.NumericalGenusZero :=
  sphereBigon.numericalGenusZero_deleteLastEdge (by decide) bigonGenus

example : RotationCertificate.ofRotation sphereBigon.deleteLastEdge = ⟨[0, 1]⟩ := by
  decide +kernel

example : RotationCertificate.verifyGenusZero bridge
    (RotationCertificate.ofRotation sphereBigon.deleteLastEdge) = true := by decide +kernel

-- Deleting one loop of a positive-genus bouquet still gives the literal sphere-loop
-- rotation. The genus-zero deletion theorem is not invoked with a false source premise.
private def torusNoPoint : RotationSystem (lastEdgeGraph oneLoop 0 0) where
  rotate := ((Dart.indexEquiv (lastEdgeGraph oneLoop 0 0)).trans
    (Equiv.swap (1 : Fin 4) 2 * finRotate 4 * Equiv.swap (1 : Fin 4) 2)).trans
      (Dart.indexEquiv (lastEdgeGraph oneLoop 0 0)).symm
  sameCycle_iff := by decide +kernel

example : RotationCertificate.ofRotation torusNoPoint.deleteLastEdge = ⟨[1, 0]⟩ := by
  decide +kernel

end CslibFrontierTests.RotationEdgeDeletion
