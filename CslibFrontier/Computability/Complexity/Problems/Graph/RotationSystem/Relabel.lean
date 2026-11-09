/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem
import Mathlib.Data.List.GetD

/-!
# Vertex-name maps on actual listed graph darts

All declared names and edge endpoints are mapped pointwise. Edge positions and end tags
remain unchanged, even for a noninjective map. This supplies endpoint equations for vertex
identification and nonloop contraction; arbitrary renaming alone does not supply a rotation
or preserve numerical genus. Isolated declarations remain in the mapped vertex list.
-/

public section

namespace Cslib.Complexity.Graph

/-- Map the actual declared names and both endpoints of every listed edge occurrence. -/
@[expose] def relabel (G : Graph) (f : ℕ → ℕ) : Graph :=
  (G.1.map f, G.2.map (Prod.map f f))

/-- Mapping all declared names and edge endpoints retains endpoint declaration, without
an injectivity assumption on the map. -/
theorem endpoints_declared_relabel (G : Graph) (f : ℕ → ℕ)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    ∀ v ∈ (G.relabel f).incidenceVertices, v ∈ (G.relabel f).1 := by
  intro v hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.map_fst, Prod.map_snd] at hv
  rcases hv with rfl | rfl
  · exact List.mem_map_of_mem (hG old.1 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩))
  · exact List.mem_map_of_mem (hG old.2 (List.mem_flatMap.mpr ⟨old, ho, by simp⟩))

namespace Dart

/-- A vertex-name map retains every original indexed edge end. No injection is required. -/
@[expose] def relabelEquiv (G : Graph) (f : ℕ → ℕ) : Dart G ≃ Dart (G.relabel f) :=
  (finCongr (show G.2.length = (G.relabel f).2.length by simp [Graph.relabel])).prodCongr
    (Equiv.refl Bool)

/-- The actual endpoint is mapped by the supplied name function. -/
theorem vertex_relabelEquiv (G : Graph) (f : ℕ → ℕ) (d : Dart G) :
    (relabelEquiv G f d).vertex = f d.vertex := by
  rcases d with ⟨i, b⟩
  change (if b then ((G.2.map (Prod.map f f)).getD i.val (0, 0)).2
    else ((G.2.map (Prod.map f f)).getD i.val (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt),
    List.getElem_map]
  change _ = f (if b then (G.2.getD i.val (0, 0)).2 else (G.2.getD i.val (0, 0)).1)
  rw [List.getD_eq_getElem _ _ i.isLt]
  cases b <;> rfl

/-- Mapping vertex names commutes with edge reversal. -/
theorem reverse_relabelEquiv (G : Graph) (f : ℕ → ℕ) (d : Dart G) :
    relabelEquiv G f d.reverse = (relabelEquiv G f d).reverse := rfl

end Dart
end Cslib.Complexity.Graph
