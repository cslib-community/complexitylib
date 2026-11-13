/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Restoration
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Bouquet
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus

/-!
Automatic split layout on the actual contraction of a nonbridge parallel edge, with
loops at both original endpoints, duplicate declarations and an untouched isolate.
The remaining parallel edge becomes a loop and its two cut ends are assigned to opposite
new centers. No separator, center or connector-order premise is supplied.
The restoration client constructs and checks the actual source embedding without a supplied split.
The restored realization keeps the original clockwise convention.
-/

namespace CslibFrontierTests.PolygonalContractionSplit

open Cslib Cslib.Polygonal Cslib.Complexity Cslib.Complexity.Graph
open RotationSystem

private abbrev retained : Graph := ⟨[7, 11, 7, 100, 100], [(7, 7), (11, 11), (7, 11)]⟩

private abbrev source : Graph := lastEdgeGraph retained 7 11

private def certificate : Graph.RotationCertificate := ⟨[1, 4, 3, 7, 6, 2, 0, 5]⟩

private noncomputable def rotation : RotationSystem source :=
  Graph.RotationCertificate.decode source certificate (by decide +kernel)

private theorem genus : rotation.NumericalGenusZero :=
  (Graph.RotationCertificate.verifyEuler_eq_true_iff (G := source) (c := certificate)
    (by decide +kernel)).mp (by decide +kernel)

private abbrev target : Graph := contractLastEdgeGraph retained 7 11

private abbrev parallel : Fin target.2.length := ⟨2, by decide +kernel⟩

private noncomputable def targetRotation : RotationSystem target :=
  rotation.contractLastEdge (by decide)

private theorem target_genus : targetRotation.NumericalGenusZero :=
  rotation.numericalGenusZero_contractLastEdge (by decide) (by decide +kernel) genus

private noncomputable def drawing : PolygonalDrawing target :=
  PolygonalDrawing.bouquet targetRotation (by decide +kernel)

private theorem embedded : drawing.IsEmbedding :=
  PolygonalDrawing.bouquet_isEmbedding targetRotation (by decide +kernel) target_genus
    (by decide +kernel)

private theorem realized : drawing.Realizes targetRotation :=
  PolygonalDrawing.bouquet_realizes targetRotation (by decide +kernel)

-- Both source endpoint loops survive; the remaining parallel edge is reopened from
-- two distinct actual cut ends, with separated continuous spokes at the new centers.
example : ∃ ρ > 0, ∃ a ∈ Metric.ball (drawing.vertex 11) ρ,
    ∃ b ∈ Metric.ball (drawing.vertex 11) ρ,
      (drawing.outsideRoute 11 ρ parallel).IsSimple ∧
      (∀ (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        AffineMap.lineMap a (drawing.cutPort ρ (parallel, false)) s ≠
          AffineMap.lineMap b (drawing.cutPort ρ (parallel, true)) t) := by
  obtain ⟨ρ, hρ, _, hsimple, _⟩ := embedded.exists_restriction 11 (by decide +kernel)
  obtain ⟨a, ha, b, hb, f, hsep, hpa, hpb, _, _⟩ :=
    realized.exists_contraction_split rotation (by decide) embedded hρ
  refine ⟨ρ, hρ, a, ha, b, hb, hsimple parallel, fun s t hs ht => ?_⟩
  exact split_spokes_ne f hsep
    (hpa ⟨(parallel, false), by decide +kernel⟩ (by decide +kernel))
    (hpb ⟨(parallel, true), by decide +kernel⟩ (by decide +kernel)) hs ht

-- Apply the actual restoration constructor: all four source routes, including the
-- selected parallel connector and both endpoint loops, have full continuous simplicity.
example : ∃ D : PolygonalDrawing source,
    (∀ e, (D.route e).IsSimple) ∧ D.vertex 7 ≠ D.vertex 11 := by
  obtain ⟨ρ, hρ, _, hsimple, _, hcut⟩ := embedded.exists_restriction 11 (by decide +kernel)
  obtain ⟨a, ha, b, hb, f, hsep, hpa, hpb, _, _⟩ :=
    realized.exists_contraction_split rotation (by decide) embedded hρ
  let D := drawing.restoration (by decide : 7 ≠ 11) ρ a b
  have hab : a ≠ b := fun heq => (ne_of_lt hsep) (congrArg f heq.symm)
  refine ⟨D, ?_, ?_⟩
  · intro e
    change (if h : e.val < retained.2.length then
      drawing.restoredRoute ρ a b ⟨e.val, h⟩ else Route.line a b).IsSimple
    split_ifs with he
    · exact embedded.restoredRoute_simple (by decide) hρ hsimple hcut ha hb f hsep hpa hpb _
    · exact Route.isSimple_line hab
  · change drawing.restoredVertex a b 7 ≠ drawing.restoredVertex a b 11
    simpa [PolygonalDrawing.restoredVertex] using hab

-- Apply automatic restoration with no cut radius, separator, center, fan or embedding
-- of the source graph supplied by the client. Every real contact condition is included.
example : ∃ D : PolygonalDrawing source, D.IsEmbedding ∧ D.Realizes rotation := by
  obtain ⟨ρ, _, a, b, hD, hR⟩ := realized.exists_restoration rotation (by decide)
    (by decide +kernel) embedded
  exact ⟨drawing.restoration (by decide) ρ a b, hD, hR⟩

end CslibFrontierTests.PolygonalContractionSplit
