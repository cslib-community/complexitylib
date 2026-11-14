/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star

/-!
Ordinary-import clients APPLY the complete general forward theorem with no supplied drawing
or local split. Families cover arbitrary degree, empty graphs, points and bridges. Concrete
certificates cover one empty contraction block, nonbridge parallel edges, loops at both
endpoints, untouched loop components, sparse duplicate declarations and isolates. A realized
clockwise triple also excludes its reflected cyclic order.
-/

namespace CslibFrontierTests.PolygonalForward

open Cslib Cslib.Polygonal Cslib.Complexity Cslib.Complexity.Graph
open RotationSystem

-- This applies general forward directly to a nonloop graph of every degree, including >4.
example (n : ℕ) : ∃ D : PolygonalDrawing (starGraph n),
    D.IsEmbedding ∧ D.Realizes (starRotation n) :=
  (starRotation n).exists_polygonalDrawing (starGraph_endpoints_declared n)
    (numericalGenusZero_starRotation n)

example : ∃ D : PolygonalDrawing (starGraph 13),
    D.IsEmbedding ∧ D.Realizes (starRotation 13) :=
  (starRotation 13).exists_polygonalDrawing (starGraph_endpoints_declared 13)
    (numericalGenusZero_starRotation 13)

private theorem checkedGenus {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (h : RotationCertificate.verifyEuler G (RotationCertificate.ofRotation r) = true) :
    r.NumericalGenusZero := by
  have he := (RotationCertificate.verifyEuler_eq_true_iff
    (RotationCertificate.verifyRotation_ofRotation r hG)).mp h
  exact RotationCertificate.decode_ofRotation r hG ▸ he

private abbrev points : Graph := ⟨[7, 11, 1000000, 7, 1000000], []⟩

private def soleEdge : RotationSystem (lastEdgeGraph points 7 11) where
  rotate := Equiv.refl _
  sameCycle_iff := by decide +kernel

-- Both retained blocks are empty. Isolated declarations include sparse duplicates.
example : ∃ D : PolygonalDrawing (lastEdgeGraph points 7 11),
    D.IsEmbedding ∧ D.Realizes soleEdge :=
  soleEdge.exists_polygonalDrawing (by decide +kernel)
    (checkedGenus soleEdge (by decide +kernel) (by decide +kernel))

private abbrev oneBlock : Graph := ⟨[0, 1, 12, 12], [(0, 0)]⟩

private def pendant : RotationSystem (lastEdgeGraph oneBlock 0 1) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph oneBlock 0 1))
    (⟨0, by decide⟩, true) * Equiv.swap
      ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph oneBlock 0 1)) (⟨1, by decide⟩, false)
  sameCycle_iff := by decide +kernel

-- One source cycle has an empty tail; its precise connector insertion is reconstructed.
example : ∃ D : PolygonalDrawing (lastEdgeGraph oneBlock 0 1),
    D.IsEmbedding ∧ D.Realizes pendant :=
  pendant.exists_polygonalDrawing (by decide +kernel)
    (checkedGenus pendant (by decide +kernel) (by decide +kernel))

private abbrev otherBlock : Graph := ⟨[0, 1, 12, 12], [(1, 1)]⟩

private def pendantOther : RotationSystem (lastEdgeGraph otherBlock 0 1) where
  rotate := Equiv.swap ((⟨0, by decide⟩, false) : Dart (lastEdgeGraph otherBlock 0 1))
    (⟨0, by decide⟩, true) * Equiv.swap
      ((⟨0, by decide⟩, true) : Dart (lastEdgeGraph otherBlock 0 1)) (⟨1, by decide⟩, true)
  sameCycle_iff := by decide +kernel

-- The opposite empty-tail orientation is also reconstructed without a supplied gap.
example : ∃ D : PolygonalDrawing (lastEdgeGraph otherBlock 0 1),
    D.IsEmbedding ∧ D.Realizes pendantOther :=
  pendantOther.exists_polygonalDrawing (by decide +kernel)
    (checkedGenus pendantOther (by decide +kernel) (by decide +kernel))

private abbrev residual : Graph :=
  ⟨[7, 11, 50, 1000000, 7, 1000000], [(7, 7), (11, 11), (7, 11), (50, 50)]⟩

private def certificate : RotationCertificate := ⟨[1, 4, 3, 9, 8, 2, 7, 6, 0, 5]⟩

private noncomputable def nonbridge : RotationSystem (lastEdgeGraph residual 7 11) :=
  RotationCertificate.decode _ certificate (by decide +kernel)

private theorem nonbridgeGenus : nonbridge.NumericalGenusZero :=
  (RotationCertificate.verifyEuler_eq_true_iff
    (G := lastEdgeGraph residual 7 11) (c := certificate) (by decide +kernel)).mp
      (by decide +kernel)

-- The selected nonbridge has a parallel occurrence that becomes a target loop and
-- must reopen at two separate cut ends. The third loop component and isolates stay intact.
example : ∃ D : PolygonalDrawing (lastEdgeGraph residual 7 11),
    D.IsEmbedding ∧ D.Realizes nonbridge :=
  nonbridge.exists_polygonalDrawing (by decide +kernel) nonbridgeGenus

-- General forward also covers empty listed graphs and repeated isolated declarations.
private def emptyRotation : RotationSystem points where
  rotate := Equiv.refl _
  sameCycle_iff := by decide

example : ∃ D : PolygonalDrawing points, D.IsEmbedding ∧ D.Realizes emptyRotation :=
  emptyRotation.exists_polygonalDrawing (by decide)
    (checkedGenus emptyRotation (by decide) (by decide +kernel))

example (r : RotationSystem ⟨[], []⟩) :
    ∃ D : PolygonalDrawing ⟨[], []⟩, D.IsEmbedding ∧ D.Realizes r := by
  apply r.exists_polygonalDrawing
  · simp [Graph.incidenceVertices]
  · intro root hroot
    simp at hroot

private theorem starInterval : starDartEquiv 5 (1, true) ∈ (starRotation 5).rotationInterval
    (starDartEquiv 5 (0, true)) (starDartEquiv 5 (2, true)) := by
  have hdist₁ : (starRotation 5).rotationDistance (starDartEquiv 5 (0, true))
      (starDartEquiv 5 (1, true)) = 1 := by
    apply (starRotation 5).rotationDistance_eq _ _ (by decide +kernel) 1 (by decide +kernel)
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    decide +kernel
  have hdist₂ : (starRotation 5).rotationDistance (starDartEquiv 5 (0, true))
      (starDartEquiv 5 (2, true)) = 2 := by
    apply (starRotation 5).rotationDistance_eq _ _ (by decide +kernel) 2 (by decide +kernel)
    intro k hk
    interval_cases k <;> decide +kernel
  have hmem : starDartEquiv 5 (1, true) ∈ (starRotation 5).rotationInterval
      (starDartEquiv 5 (0, true)) (starDartEquiv 5 (2, true)) := by
    apply ((starRotation 5).mem_rotationInterval_iff_lt_distance _ _ _ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr
    omega
  exact hmem

-- The actual produced drawing pins the clockwise sign, independent of coordinates.
example : ∃ D : PolygonalDrawing (starGraph 5), D.IsEmbedding ∧ D.Realizes (starRotation 5) ∧
    sbtw (D.direction (starDartEquiv 5 (2, true)))
      (D.direction (starDartEquiv 5 (1, true))) (D.direction (starDartEquiv 5 (0, true))) ∧
    ¬sbtw (D.direction (starDartEquiv 5 (0, true)))
      (D.direction (starDartEquiv 5 (1, true))) (D.direction (starDartEquiv 5 (2, true))) := by
  obtain ⟨D, hD, hR⟩ := (starRotation 5).exists_polygonalDrawing
    (starGraph_endpoints_declared 5) (numericalGenusZero_starRotation 5)
  have hclock := (hR.clockwise (starDartEquiv 5 (0, true)) (starDartEquiv 5 (1, true))
    (starDartEquiv 5 (2, true)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr starInterval
  exact ⟨D, hD, hR, hclock, hclock.not_sbtw⟩

-- This is the literal reflection of the explicit star across the real axis.
private def reflectedStar : PolygonalDrawing (starGraph 5) where
  vertex := fun w => if w = 5 then 0 else ⟨(w : ℝ) + 1, -1⟩
  route := fun e => Route.line ⟨(e.val : ℝ) + 1, -1⟩ 0
  endpoint_eq := by
    intro e side
    let i : Fin 5 := ⟨e.val, by simpa [starGraph] using e.isLt⟩
    have he : (e, side) = starDartEquiv 5 (i, side) := rfl
    rw [he, vertex_starDartEquiv]
    cases side
    · have hi : i.val ≠ 5 := Nat.ne_of_lt i.isLt
      simp [Route.endpoint, hi, i]
    · simp [Route.endpoint]

example (w : ℕ) : reflectedStar.vertex w =
    (starRingEnd ℂ) ((PolygonalDrawing.star 5).vertex w) := by
  by_cases hw : w = 5
  · simp [reflectedStar, PolygonalDrawing.star, PolygonalDrawing.starPoint, hw]
  · simp only [reflectedStar, PolygonalDrawing.star, PolygonalDrawing.starPoint, ite_eq_right hw]
    rfl

-- Reflection keeps an actual drawing but reverses the required clockwise order.
example : ¬reflectedStar.Realizes (starRotation 5) := by
  have hdir (i : Fin 5) : reflectedStar.direction (starDartEquiv 5 (i, true)) =
      -((⟨(i.val : ℝ) + 1, 1⟩ : ℂ).arg : Real.Angle) := by
    change (((Route.line ⟨(i.val : ℝ) + 1, -1⟩ 0).germ true).arg : Real.Angle) = _
    rw [Route.germ_line]
    simp only [↓reduceIte, sub_zero]
    exact Complex.arg_conj_coe_angle ⟨(i.val : ℝ) + 1, 1⟩
  have h01 := arg_port_strictAnti (a := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  have h12 := arg_port_strictAnti (a := 2) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have h1 := arg_port_mem (x := 1) (by norm_num)
  have h3 := arg_port_mem (x := 3) (by norm_num)
  have href : sbtw (reflectedStar.direction (starDartEquiv 5 (0, true)))
      (reflectedStar.direction (starDartEquiv 5 (1, true)))
      (reflectedStar.direction (starDartEquiv 5 (2, true))) := by
    rw [hdir, hdir, hdir]
    norm_num
    rw [← Real.Angle.coe_neg, ← Real.Angle.coe_neg, ← Real.Angle.coe_neg]
    exact sbtw_angle_of_lt_of_span_lt (by linarith) (by linarith)
      (by linarith [h1.2, h3.1, Real.pi_pos])
  intro hR
  exact hR.not_counterclockwise (starDartEquiv 5 (0, true)) (starDartEquiv 5 (1, true))
    (starDartEquiv 5 (2, true)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) starInterval href

end CslibFrontierTests.PolygonalForward
