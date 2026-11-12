/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Restoration
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.EdgeTransport
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Bouquet
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus

/-!
# Polygonal realization of arbitrary numerical genus-zero rotations

Induction on the actual listed edge count contracts any nonloop occurrence after an
indexed permutation. Automatic geometric restoration reopens every retained edge end
independently and inserts the selected connector in its literal clockwise slot. Transport
back recovers the exact original edge order and declarations. The loop-only base includes
empty graphs, isolated declared names, loops, parallel occurrences and disconnected graphs.

This is a forward existence theorem for actual finite polygonal embeddings over the real
plane. It asserts neither a coordinate-bit bound nor a planarity recognition algorithm.
## Main results

* `Cslib.Complexity.Graph.RotationSystem.exists_polygonalDrawing`:
  every declared numerical genus-zero rotation has an actual clockwise polygonal embedding.

-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Every supplied componentwise numerical genus-zero rotation on an arbitrary actual
listed finite graph has a genuine polygonal embedding realizing its exact clockwise order.
No geometric patch, separator, drawing or order provider is an additional premise. -/
theorem exists_polygonalDrawing {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero) :
    ∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r := by
  classical
  have forward : ∀ n, ∀ G : Graph, G.2.length = n → ∀ r : RotationSystem G,
      (∀ v ∈ G.incidenceVertices, v ∈ G.1) → r.NumericalGenusZero →
        ∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro G hlen r hG hr
      by_cases hloop : ∀ e : Fin G.2.length,
          Dart.vertex (G := G) (e, false) = Dart.vertex (e, true)
      · exact r.exists_polygonalDrawing_of_loops hG hr hloop
      · push Not at hloop
        obtain ⟨i, hnonloop⟩ := hloop
        obtain ⟨H, u, v, e, hdecl, hlenH, hcoord, _, hu, hv⟩ := G.exists_lastEdge_reindex i
        have huv : u ≠ v := by rw [hu, hv]; exact hnonloop
        have hm : ∀ w, w ∈ G.1 ↔ w ∈ (lastEdgeGraph H u v).1 := by
          intro w
          simp only [lastEdgeGraph, hdecl]
        have hH := endpoints_declared_edge_reindex e hcoord hm hG
        let E : Dart G ≃ Dart (lastEdgeGraph H u v) := e.prodCongr (Equiv.refl Bool)
        have hvE : ∀ a b, (E a).vertex = (E b).vertex ↔ a.vertex = b.vertex := by
          intro a b
          change Dart.vertex (e a.1, a.2) = Dart.vertex (e b.1, b.2) ↔ _
          rw [hcoord, hcoord]
        let s := r.transport E hvE
        have hs : s.NumericalGenusZero :=
          r.numericalGenusZero_transport E hvE (fun _ => rfl) hG hH hr
        have hsmall : (contractLastEdgeGraph H u v).2.length < n := by
          simp only [contractLastEdgeGraph, Graph.relabel, List.length_map]
          omega
        obtain ⟨D, hD, hR⟩ := ih _ hsmall (contractLastEdgeGraph H u v) rfl
          (s.contractLastEdge huv) (endpoints_declared_contractLastEdge hH)
          (s.numericalGenusZero_contractLastEdge huv hH hs)
        obtain ⟨ρ, _, a, b, hnew, hnewR⟩ := hR.exists_restoration s huv hH hD
        have hback : ∀ i side, Dart.vertex (G := G) (e.symm i, side) =
            Dart.vertex (G := lastEdgeGraph H u v) (i, side) := by
          intro i side
          simpa only [e.apply_symm_apply] using (hcoord (e.symm i) side).symm
        let Q := D.restoration huv ρ a b
        refine ⟨Q.edgeTransport e.symm hback,
          hnew.edgeTransport e.symm hback (fun w => (hm w).symm), ?_⟩
        have hreal := hnewR.edgeTransport e.symm hback
        have hvBack : ∀ a b, (E.symm a).vertex = (E.symm b).vertex ↔ a.vertex = b.vertex := by
          intro a b
          change Dart.vertex (e.symm a.1, a.2) = Dart.vertex (e.symm b.1, b.2) ↔ _
          rw [hback, hback]
        have hrot := r.transport_symm E hvE hvBack
        exact hrot ▸ hreal
  exact forward G.2.length G rfl r hG hr

end Cslib.Complexity.Graph.RotationSystem
