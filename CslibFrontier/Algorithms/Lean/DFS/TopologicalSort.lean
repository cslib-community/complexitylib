/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.Basic
public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Topological sort

Topological sort of a directed graph given by adjacency lists: the vertices in reverse order of
finishing time under the depth-first search of `CslibFrontier.Algorithms.Lean.DFS.Basic`, following
[Cormen et al., Section 22.4][CLRS2009].

## Main definitions

* `Cslib.Algorithms.Lean.DFS.IsTopologicalOrder`: a list of all the vertices, without repetition,
  in which the source of every edge comes before its target.
* `Cslib.Algorithms.Lean.DFS.topologicalSort`, `Cslib.Algorithms.Lean.DFS.topologicalSortM`:
  topological sort, and topological sort in `TimeM`.

## Main results

* `Cslib.Algorithms.Lean.DFS.IsTopologicalOrder.acyclic`: a graph with a topological order is
  acyclic.
* `Cslib.Algorithms.Lean.DFS.isTopologicalOrder_topologicalSort_iff`: from a list of all the
  vertices, topological sort returns a topological order exactly when the graph is acyclic
  [Cormen et al., Theorem 22.12][CLRS2009]. In particular a graph is acyclic if and only if it has
  a topological order (`Cslib.Algorithms.Lean.DFS.acyclic_iff_exists_isTopologicalOrder`).
* `Cslib.Algorithms.Lean.DFS.time_topologicalSortM`: topological sort costs exactly
  `|vs| + ∑ v, |adj v|`, linear in the size of the graph.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.DFS

open scoped List

variable {V : Type*} {adj : V → List V}

/-- A topological order of the graph: a list of distinct vertices containing every vertex, in
which the source of each edge comes before its target. -/
structure IsTopologicalOrder (adj : V → List V) (l : List V) : Prop where
  /-- No vertex is repeated. -/
  nodup : l.Nodup
  /-- Every vertex occurs. -/
  mem : ∀ v, v ∈ l
  /-- The source of every edge comes before its target. -/
  sublist : ∀ u v, Edge adj u v → [u, v] <+ l

private theorem idxOf_lt_of_sublist [DecidableEq V] :
    ∀ {l : List V} {a b : V}, l.Nodup → [a, b] <+ l → l.idxOf a < l.idxOf b
  | [], _, _, _, h => by simp at h
  | x :: l, a, b, hl, h => by
    rw [List.nodup_cons] at hl
    rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, hrl⟩
    · have ha : x ≠ a := fun hxa => hl.1 (hxa ▸ h.subset List.mem_cons_self)
      have hb : x ≠ b := fun hxb => hl.1 (hxb ▸ h.subset (by simp))
      rw [List.idxOf_cons_ne _ ha, List.idxOf_cons_ne _ hb]
      exact Nat.succ_lt_succ (idxOf_lt_of_sublist hl.2 h)
    · obtain ⟨hxa, rfl⟩ : x = a ∧ r = [b] := by simpa using hr.symm
      subst hxa
      have hb : x ≠ b := fun hxb => hl.1 (hxb ▸ List.singleton_sublist.1 hrl)
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ hb]
      exact Nat.succ_pos _

/-- **A graph with a topological order is acyclic**: positions in the order strictly increase
along every edge. -/
theorem IsTopologicalOrder.acyclic {l : List V} (hl : IsTopologicalOrder adj l) :
    Relation.Acyclic (Edge adj) := by
  classical
  have key : ∀ a b, Relation.TransGen (Edge adj) a b → l.idxOf a < l.idxOf b := by
    intro a b hab
    induction hab with
    | single hab => exact idxOf_lt_of_sublist hl.nodup (hl.sublist _ _ hab)
    | tail _ hbc ih => exact ih.trans (idxOf_lt_of_sublist hl.nodup (hl.sublist _ _ hbc))
  exact ⟨fun v hv => lt_irrefl _ (key v v hv)⟩

/-- **Topological sort**: the vertices in reverse order of finishing time under depth-first search
from the vertices `vs` in turn. -/
def topologicalSort [DecidableEq V] (adj : V → List V) (vs : List V) : List V :=
  (dfs adj vs.length vs).finished

theorem card_le_length [Fintype V] {vs : List V} (hvs : ∀ v, v ∈ vs) :
    Fintype.card V ≤ vs.length := by
  classical
  calc Fintype.card V = (Finset.univ : Finset V).card := rfl
    _ ≤ vs.toFinset.card := Finset.card_le_card fun v _ => List.mem_toFinset.2 (hvs v)
    _ ≤ vs.length := List.toFinset_card_le vs

section TopologicalSort

variable [DecidableEq V] {vs : List V}

/-- From a list of all the vertices, topological sort lists each vertex at most once. -/
theorem nodup_topologicalSort (hvs : ∀ v, v ∈ vs) : (topologicalSort adj vs).Nodup :=
  letI : Fintype V := Fintype.ofList vs hvs
  nodup_dfs_finished (card_le_length hvs) vs

/-- From a list of all the vertices, topological sort lists every vertex. -/
theorem mem_topologicalSort (hvs : ∀ v, v ∈ vs) (v : V) : v ∈ topologicalSort adj vs :=
  letI : Fintype V := Fintype.ofList vs hvs
  (mem_dfs_finished_iff (card_le_length hvs) vs v).2 ⟨v, hvs v, .refl⟩

/-- **Topological sort is correct exactly on acyclic graphs** [Cormen et al., Theorem
22.12][CLRS2009]: from a list `vs` of all the vertices, `topologicalSort adj vs` is a topological
order if and only if the graph is acyclic. -/
theorem isTopologicalOrder_topologicalSort_iff (hvs : ∀ v, v ∈ vs) :
    IsTopologicalOrder adj (topologicalSort adj vs) ↔ Relation.Acyclic (Edge adj) := by
  refine ⟨fun h => h.acyclic, fun hacyc => ⟨nodup_topologicalSort hvs,
    mem_topologicalSort hvs, fun u v huv => ?_⟩⟩
  let : Fintype V := Fintype.ofList vs hvs
  rcases dfs_finished_order (card_le_length hvs) vs (mem_topologicalSort hvs u) huv with h | h
  · exact h
  · exact absurd (Relation.TransGen.head' huv h) (hacyc.irrefl u)

omit [DecidableEq V] in
/-- A finite graph is acyclic if and only if it has a topological order. -/
theorem acyclic_iff_exists_isTopologicalOrder [Finite V] :
    Relation.Acyclic (Edge adj) ↔ ∃ l, IsTopologicalOrder adj l := by
  classical
  have : Fintype V := Fintype.ofFinite V
  refine ⟨fun h => ⟨topologicalSort adj Finset.univ.toList, ?_⟩, fun ⟨_, hl⟩ => hl.acyclic⟩
  exact (isTopologicalOrder_topologicalSort_iff fun v =>
    Finset.mem_toList.2 (Finset.mem_univ v)).2 h

end TopologicalSort

/-! ### Cost -/

open TimeM

/-- Topological sort in `TimeM`. -/
def topologicalSortM [DecidableEq V] (adj : V → List V) (vs : List V) : TimeM ℕ (List V) :=
  State.finished <$> dfsM adj vs.length vs

section Cost

variable [DecidableEq V] [Fintype V] {vs : List V}

omit [Fintype V] in
theorem ret_topologicalSortM (adj : V → List V) (vs : List V) :
    (topologicalSortM adj vs).ret = topologicalSort adj vs := by
  simp [topologicalSortM, ret_dfsM, topologicalSort]

/-- **Topological sort in linear time**: from a list `vs` of the vertices, topological sort costs
exactly `|vs| + ∑ v, |adj v|`, the number of vertices listed plus the number of edges. -/
theorem time_topologicalSortM (hvs : ∀ v, v ∈ vs) :
    (topologicalSortM adj vs).time = vs.length + ∑ v, (adj v).length := by
  rw [topologicalSortM, TimeM.time_map, time_dfsM]
  congr 1
  have hn : (dfs adj vs.length vs).finished.Nodup := nodup_topologicalSort hvs
  rw [outDegreeSum, ← List.sum_toFinset _ hn]
  congr 1
  ext v
  have hv : v ∈ (dfs adj vs.length vs).finished := mem_topologicalSort hvs v
  simpa using hv

end Cost

end Cslib.Algorithms.Lean.DFS
