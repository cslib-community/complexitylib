/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Incidence parity from exact dart words

A duplicate-free word listing precisely one vertex's indexed darts computes its existing
incidence parity. Repeated edge records and the two ends of a loop remain separate darts.
-/

public section

namespace Cslib.Complexity.Graph

/-- Incidence parity needs to be checked only at actual indexed dart endpoints. Every
other name, including isolated or undeclared names, has an empty incidence sum. -/
theorem vertexEven_iff_dart {G : Graph} (x : Fin G.edges.length → Bool) :
    G.VertexEven x ↔ ∀ d : Dart G, G.vertexParity x d.vertex = false := by
  classical
  constructor
  · exact fun h d => h d.vertex
  · intro h v
    by_cases hv : ∃ d : Dart G, d.vertex = v
    · obtain ⟨d, rfl⟩ := hv
      exact h d
    · unfold vertexParity
      apply Finset.sum_eq_zero
      intro d _
      exact ite_eq_right (fun hd => hv ⟨d, hd⟩)

/-- Compute actual incidence parity from any exact duplicate-free vertex word. Empty
words compute zero, including undeclared or isolated names. -/
theorem vertexParity_eq_sum_word {G : Graph} (x : Fin G.edges.length → Bool)
    (v : ℕ) (word : List (Dart G)) (hn : word.Nodup)
    (hw : ∀ d, d ∈ word ↔ d.vertex = v) :
    G.vertexParity x v = (word.map fun d => x d.1).sum := by
  classical
  rw [vertexParity, ← List.sum_toFinset _ hn]
  have hset : word.toFinset = Finset.univ.filter (fun d : Dart G => d.vertex = v) := by
    ext d
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and, hw]
  rw [hset, Finset.sum_filter]

end Cslib.Complexity.Graph
