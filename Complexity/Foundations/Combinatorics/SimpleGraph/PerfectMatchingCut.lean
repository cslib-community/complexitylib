/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, perfect matching cuts)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Perfect matching cuts with labeled sides

The entire crossing-edge subgraph must be a perfect matching, and both sides must be nonempty.
This is the convention in [ChenJiangZhu2027], Proposition D.2 (PDF p. 34). Boolean side labels
represent an ordered bipartition: swapping labels counts separately.

## Main definitions

* `SimpleGraph.crossingSubgraph`: every original edge between opposite sides, on all vertices.
* `SimpleGraph.IsPerfectMatchingCut`: nonempty sides with a perfect crossing matching.

## Main results

* `SimpleGraph.isPerfectMatchingCut_iff`: on a nonempty vertex type, exactly one opposite-side
  neighbor at every vertex is precisely a perfect matching cut.
-/

public section

namespace SimpleGraph

/-- The spanning subgraph containing all crossing edges of the Boolean-labeled cut. -/
@[expose] def crossingSubgraph {V : Type*} (G : SimpleGraph V) (side : V → Bool) : G.Subgraph where
  verts := Set.univ
  Adj u v := G.Adj u v ∧ side u ≠ side v
  adj_sub := And.left
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩

/-- A labeled partition into two nonempty sides whose crossing graph is a perfect matching. -/
@[expose] def IsPerfectMatchingCut {V : Type*} (G : SimpleGraph V) (side : V → Bool) : Prop :=
  (∃ u, side u = false) ∧ (∃ u, side u = true) ∧ (G.crossingSubgraph side).IsPerfectMatching

/-- Nonempty graphs need no additional side witnesses: one opposite neighbor forces both sides. -/
theorem isPerfectMatchingCut_iff {V : Type*} [Nonempty V] (G : SimpleGraph V) (side : V → Bool) :
    G.IsPerfectMatchingCut side ↔ ∀ u, ∃! v, G.Adj u v ∧ side u ≠ side v := by
  constructor
  · rintro ⟨_, _, h⟩
    exact Subgraph.isPerfectMatching_iff.mp h
  · intro h
    have hm : (G.crossingSubgraph side).IsPerfectMatching := Subgraph.isPerfectMatching_iff.mpr h
    obtain ⟨u⟩ := ‹Nonempty V›
    obtain ⟨v, hv, _⟩ := h u
    refine ⟨?_, ?_, hm⟩
    · cases hu : side u with
      | false => exact ⟨u, hu⟩
      | true =>
        refine ⟨v, ?_⟩
        cases hv' : side v <;> simp_all
    · cases hu : side u with
      | true => exact ⟨u, hu⟩
      | false =>
        refine ⟨v, ?_⟩
        cases hv' : side v <;> simp_all

end SimpleGraph
