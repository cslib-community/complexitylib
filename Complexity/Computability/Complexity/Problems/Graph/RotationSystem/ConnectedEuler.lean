/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.FaceCounts

/-!
# Euler counts for a connected indexed rotation

For a graph with an actual dart and a single declared-vertex component, the existing
componentwise numerical predicate reduces to one equation using the full face quotient.
Singleton face orbits are included. The dart hypothesis explicitly excludes point components;
their conventional face is already handled by `NumericalGenusZero` itself.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Graph.RotationCertificate

/-- Connectedness identifies every component face with a face of the whole rotation. -/
noncomputable def connectedFaceEquiv {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hc : ∀ u ∈ G.1, ∀ v ∈ G.1, SameComponent G u v) (d : Dart G) :
    ComponentFace r d.vertex ≃ r.Face where
  toFun := Subtype.val
  invFun f := ⟨f, Quotient.inductionOn f (fun a =>
    ⟨a, hc _ (vertex_mem hG d) _ (vertex_mem hG a), rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- On a connected graph with an actual edge, numerical genus zero is precisely Euler's
single equation. No geometric meaning or recognition algorithm is asserted. -/
theorem numericalGenusZero_iff_connected_euler {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hc : ∀ u ∈ G.1, ∀ v ∈ G.1, SameComponent G u v) (d : Dart G) :
    r.NumericalGenusZero ↔ G.1.toFinset.card + Nat.card r.Face = G.2.length + 2 := by
  classical
  have hv (a : Dart G) : G.componentVertexSet a.vertex = G.1.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact hc _ (vertex_mem hG a) _ (List.mem_toFinset.mp hv)
  have he (a : Dart G) : G.componentEdgeSet a.vertex = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact hc _ (vertex_mem hG a) _ (vertex_mem hG (i, false))
  have hf (a : Dart G) : (r.componentFaceIndices a.vertex).card = Nat.card r.Face := by
    rw [card_componentFaceIndices,
      r.count_faceRepresentatives_eq_card_componentFace hG]
    exact Nat.card_congr (r.connectedFaceEquiv hG hc a)
  rw [r.numericalGenusZero_iff_component_cards hG]
  simp only [hv, he, hf, Finset.card_univ, Fintype.card_fin]
  exact ⟨fun h => h d, fun h _ => h⟩

end Cslib.Complexity.Graph.RotationSystem
