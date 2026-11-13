/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star
import Mathlib.Tactic.IntervalCases

/-!
Ordinary-import regression clients for the complete loop-only forward realization. The
unbounded-degree family uses the existing numerical duality and ordered stars; no genus-zero
assumption is supplied by the test caller. Concrete successor tables also exercise nested and
disjoint loops, repeated edge pairs, disconnected components, sparse duplicated declarations,
isolates, and the empty graph. The wrong cyclic order and interlacing obstruction are negative
checks. No full-graph or geometric-converse equivalence is claimed.
-/

namespace CslibFrontierTests.PolygonalBouquet

open Cslib Cslib.Complexity Cslib.Complexity.Graph
open Polygonal RotationSystem

private theorem star_dual_loops (n : ℕ) (e : Fin (starRotation n).dualGraph.2.length) :
    (Dart.vertex (G := (starRotation n).dualGraph) (e, false)) = Dart.vertex (e, true) := by
  let i : Fin (starGraph n).2.length := ⟨e.val, by simpa using e.isLt⟩
  have he (b : Bool) : (e, b) = (starRotation n).dualDartEquiv (i, b) := rfl
  rw [he false, he true, vertex_dualDartEquiv, vertex_dualDartEquiv, faceId_eq_iff]
  exact sameFace_starRotation _ _

-- This produces an embedded bouquet of n indexed loops, for every n, with no degree bound.
example (n : ℕ) : ∃ D : PolygonalDrawing (starRotation n).dualGraph,
    D.IsEmbedding ∧ D.Realizes (starRotation n).dualRotation :=
  (starRotation n).dualRotation.exists_polygonalDrawing_of_loops
    (starRotation n).dualGraph_endpoints_declared
    (((starRotation n).numericalGenusZero_dual_iff (starGraph_endpoints_declared n)).mpr
      (numericalGenusZero_starRotation n)) (star_dual_loops n)

-- All 2*n darts of this family lie at one vertex whenever a dart exists.
example (n : ℕ) : Fintype.card (Dart (starRotation n).dualGraph) = 2 * n := by
  rw [Dart.card, dualGraph_length]
  simp [starGraph]

example (n : ℕ) (a b : Dart (starRotation n).dualGraph) : a.vertex = b.vertex := by
  obtain ⟨a, rfl⟩ := (starRotation n).dualDartEquiv.surjective a
  obtain ⟨b, rfl⟩ := (starRotation n).dualDartEquiv.surjective b
  rw [vertex_dualDartEquiv, vertex_dualDartEquiv, faceId_eq_iff]
  exact sameFace_starRotation _ _

-- Three repeated loops at 100: cyclic word 0-,1-,1+,0+,2-,2+.
-- Two repeated loops at 7 are disjoint; 42 and 1000000 are disconnected isolates.
private abbrev listed : Graph :=
  ⟨[100, 7, 100, 42, 1000000, 7], [(100, 100), (100, 100), (100, 100), (7, 7), (7, 7)]⟩

private def certificate : RotationCertificate := ⟨[2, 4, 3, 1, 5, 0, 7, 8, 9, 6]⟩

private noncomputable def rotation : RotationSystem listed :=
  RotationCertificate.decode listed certificate (by decide)

private theorem genus : rotation.NumericalGenusZero :=
  (RotationCertificate.verifyEuler_eq_true_iff (G := listed) (c := certificate)
    (by decide)).mp (by decide)

example : ∃ D : PolygonalDrawing listed, D.IsEmbedding ∧ D.Realizes rotation :=
  rotation.exists_polygonalDrawing_of_loops (by decide) genus (by decide)

example : (PolygonalDrawing.bouquet rotation (by decide)).IsEmbedding :=
  PolygonalDrawing.bouquet_isEmbedding rotation (by decide) genus (by decide)

example : (PolygonalDrawing.bouquet rotation (by decide)).vertex 42 ≠
    (PolygonalDrawing.bouquet rotation (by decide)).vertex 1000000 :=
  (PolygonalDrawing.bouquet_isEmbedding rotation (by decide) genus (by decide)).vertex_ne
    (by decide) (by decide) (by decide)

-- Actual nested and disjoint five-segment contacts, at arbitrary real parameters.
example (i j : Fin 5) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (h : (portLoop 1 6).eval i s = (portLoop 2 3).eval j t) :
    (portLoop 1 6).eval i s = 0 :=
  portLoop_contact_eq_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) i j hs ht h

example (i j : Fin 5) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (h : (portLoop 4 1).eval i s = (portLoop 8 5).eval j t) :
    (portLoop 4 1).eval i s = 0 :=
  portLoop_contact_eq_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) i j hs ht h

example : (portLoop 1 200).IsSimple := isSimple_portLoop (by norm_num)

-- Interlacing port intervals really do cross, here along overlapping upper segments.
example : (portLoop 1 3).eval (2 : Fin 5) (3 / 4) =
    (portLoop 2 4).eval (2 : Fin 5) (1 / 4) := by
  rw [eval_portLoop 1 3 2 (3 / 4), eval_portLoop 2 4 2 (1 / 4)]
  apply Complex.ext <;> norm_num

example : (portLoop 1 3).eval (2 : Fin 5) (3 / 4) ≠ 0 := by
  intro h
  rw [eval_portLoop 1 3 2 (3 / 4)] at h
  have := congrArg Complex.im h
  norm_num at this

-- Positive ports pin the fixed clockwise orientation; reversing it fails.
example : sbtw ((⟨3, 1⟩ : ℂ).arg : Real.Angle) ((⟨2, 1⟩ : ℂ).arg : Real.Angle)
    ((⟨1, 1⟩ : ℂ).arg : Real.Angle) := clockwise_ports (by norm_num) (by norm_num) (by norm_num)

example : ¬sbtw ((⟨1, 1⟩ : ℂ).arg : Real.Angle) ((⟨2, 1⟩ : ℂ).arg : Real.Angle)
    ((⟨3, 1⟩ : ℂ).arg : Real.Angle) :=
  (clockwise_ports (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num) (by norm_num)).not_sbtw

private def wrongCertificate : RotationCertificate := ⟨[5, 3, 0, 2, 1, 4, 9, 6, 7, 8]⟩

private noncomputable def wrongRotation : RotationSystem listed :=
  RotationCertificate.decode listed wrongCertificate (by decide)

-- The exact drawing of the given rotation cannot also realize its reversed order.
example : ¬(PolygonalDrawing.bouquet rotation (by decide)).Realizes wrongRotation := by
  have hdist : rotation.rotationDistance (0, false) (1, true) = 2 := by
    apply rotation.rotationDistance_eq _ _ (by decide) 2 (by decide)
    intro k hk
    interval_cases k <;> decide
  have hmem : (1, false) ∈ rotation.rotationInterval (0, false) (1, true) := by
    unfold RotationSystem.rotationInterval
    rw [hdist]
    decide
  have hwrong : wrongRotation.rotationDistance (0, false) (1, true) = 4 := by
    apply wrongRotation.rotationDistance_eq _ _ (by decide) 4 (by decide)
    intro k hk
    interval_cases k <;> decide
  have hnot : (1, false) ∉ wrongRotation.rotationInterval (0, false) (1, true) := by
    unfold RotationSystem.rotationInterval
    rw [hwrong]
    decide
  intro h
  have hclock := (PolygonalDrawing.bouquet_realizes rotation (by decide)).clockwise
    (0, false) (1, false) (1, true) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact hnot ((h.clockwise _ _ _ (by decide) (by decide)
    (by decide) (by decide) (by decide)).mp (hclock.mpr hmem))

-- Three indexed loops in the cyclic word 0-,1-,0+,1+,2-,2+ contain a torus obstruction.
-- This differs from the existing private two-loop regression model.
private abbrev interlaced : Graph := ⟨[11, 11, 90], [(11, 11), (11, 11), (11, 11)]⟩

private def interlacedCertificate : RotationCertificate := ⟨[2, 3, 1, 4, 5, 0]⟩

private noncomputable def interlacedRotation : RotationSystem interlaced :=
  RotationCertificate.decode interlaced interlacedCertificate (by decide)

example : ¬interlacedRotation.NumericalGenusZero := by
  have hdist : interlacedRotation.rotationDistance (1, false) (1, true) = 2 := by
    apply interlacedRotation.rotationDistance_eq _ _ (by decide) 2 (by decide)
    intro k hk
    interval_cases k <;> decide
  have hcross : interlacedRotation.Alternates (0, false) (0, true) (1, false) (1, true) := by
    unfold RotationSystem.Alternates RotationSystem.rotationInterval
    rw [hdist]
    decide
  intro hr
  exact interlacedRotation.not_alternates_loops (by decide) hr 0 1 (by decide)
    (by decide) (by decide) hcross

-- No edges, repeated sparse isolates, and no declared vertices at all.
example (vs : List ℕ) (r : RotationSystem ⟨vs, []⟩) :
    ∃ D : PolygonalDrawing ⟨vs, []⟩, D.IsEmbedding ∧ D.Realizes r := by
  apply r.exists_polygonalDrawing_of_loops
  · simp [Graph.incidenceVertices]
  · intro root _
    simp [Dart]
  · intro e
    exact Fin.elim0 e

example (r : RotationSystem ⟨[], []⟩) :
    ∃ D : PolygonalDrawing ⟨[], []⟩, D.IsEmbedding ∧ D.Realizes r := by
  apply r.exists_polygonalDrawing_of_loops
  · simp [Graph.incidenceVertices]
  · intro root hroot
    simp at hroot
  · intro e
    exact Fin.elim0 e

end CslibFrontierTests.PolygonalBouquet
