/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/DominatingSet.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Dominating sets

A set `S` of vertices of a simple graph is *dominating* when every vertex lies in `S` or is
adjacent to a vertex of `S`. Deciding whether a graph has a dominating set of at most `k`
vertices is the NP-complete dominating set problem, the source problem of the hardness of
approximating metric k-center ([WilliamsonShmoys2011], Section 2.2;
`Cslib.Algorithms.Lean.KCenter.isDominatingSet_of_radius_le_mul`). Mathlib has no notion of
domination for simple graphs.

## Main definitions

* `SimpleGraph.IsDominatingSet`: `S` dominates `G`.

## Main results

* `SimpleGraph.isDominatingSet_iff`: the defining property.
* `SimpleGraph.isDominatingSet_univ`, `SimpleGraph.IsDominatingSet.mono`: the vertex set is
  dominating, and supersets of dominating sets are dominating.
* `SimpleGraph.IsDominatingSet.nonempty`: a dominating set of a nonempty graph is nonempty.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.2.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}

variable (G) in
/-- A set `S` of vertices **dominates** `G` when every vertex lies in `S` or is adjacent to a
vertex of `S`. -/
def IsDominatingSet (S : Set V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj v s

theorem isDominatingSet_iff : G.IsDominatingSet S ↔ ∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj v s :=
  Iff.rfl

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (S : Finset V) :
    Decidable (G.IsDominatingSet (S : Set V)) :=
  decidable_of_iff (∀ v, v ∈ S ∨ ∃ s ∈ S, G.Adj v s) (by simp only [isDominatingSet_iff,
    Finset.mem_coe])

variable (G) in
/-- The set of all vertices dominates every graph. -/
theorem isDominatingSet_univ : G.IsDominatingSet Set.univ :=
  fun v => Or.inl (Set.mem_univ v)

/-- A superset of a dominating set is dominating. -/
theorem IsDominatingSet.mono (h : G.IsDominatingSet S) (hST : S ⊆ T) : G.IsDominatingSet T :=
  fun v => (h v).imp (fun hv => hST hv) fun ⟨s, hs, hvs⟩ => ⟨s, hST hs, hvs⟩

/-- A dominating set of a graph with a vertex is nonempty. -/
theorem IsDominatingSet.nonempty [Nonempty V] (h : G.IsDominatingSet S) : S.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  rcases h v with hv | ⟨s, hs, -⟩
  · exact ⟨v, hv⟩
  · exact ⟨s, hs⟩

end SimpleGraph
