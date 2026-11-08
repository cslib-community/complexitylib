/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.SimpleGraph.TutteBerge
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Berge's lemma and the Tutte–Berge formula: checked instances

* The path `0 - 1 - 2 - 3` with the matching `{12}`: the path itself is an explicit augmenting
  path, so `{12}` is not maximum; the perfect matching `{01, 23}` is maximum.
* The `5`-cycle with the matching `{01, 23}`: `U = ∅` certifies that it is maximum, because the
  cycle has an odd number of vertices and hence an odd component. The cycle is not bipartite.
* The star `K_{1,3}` with centre `0` and the matching `{01}`: `U = {0}` certifies that it is
  maximum, because deleting the centre leaves three isolated vertices.
-/

namespace ComplexityTests.GeneralMatching

open SimpleGraph SimpleGraph.Subgraph

/-- In a graph with no edges every vertex is its own component, so a finite such graph has at
least as many odd components as vertices. -/
theorem card_le_ncard_oddComponents_of_forall_not_adj {W : Type*} [Finite W] {H : SimpleGraph W}
    (h : ∀ x y, ¬H.Adj x y) : Nat.card W ≤ H.oddComponents.ncard := by
  have hreach : ∀ x y, H.Reachable x y → x = y := fun x y ⟨p⟩ => by
    cases p with
    | nil => rfl
    | cons ha _ => exact absurd ha (h _ _)
  have hsupp : ∀ x, (H.connectedComponentMk x).supp = {x} := fun x => Set.ext fun y => by
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Set.mem_singleton_iff]
    exact ⟨hreach y x, fun h => h ▸ Reachable.refl _⟩
  have hinj : Function.Injective fun x : W =>
      (⟨H.connectedComponentMk x, by
        change Odd _
        rw [hsupp, Set.ncard_singleton]
        exact odd_one⟩ : H.oddComponents) := fun x y hxy =>
    hreach x y (ConnectedComponent.eq.mp (congrArg Subtype.val hxy))
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_coe_set_eq] at hle

/-! ### The path `0 - 1 - 2 - 3` -/

theorem path_adj (u v : Fin 4) (h : u.val + 1 = v.val) : (pathGraph 4).Adj u v :=
  pathGraph_adj.mpr (Or.inl h)

/-- The matching `{12}` of the path `0 - 1 - 2 - 3`. -/
def pathMatching : (pathGraph 4).Subgraph := (pathGraph 4).subgraphOfAdj (path_adj 1 2 rfl)

/-- The path `0 - 1 - 2 - 3` as a walk. -/
def pathWalk : (pathGraph 4).Walk 0 3 :=
  .cons (path_adj 0 1 rfl) (.cons (path_adj 1 2 rfl) (.cons (path_adj 2 3 rfl) .nil))

/-- The path `0 - 1 - 2 - 3` is `{12}`-augmenting. -/
theorem pathWalk_isAugmentingPath : pathMatching.IsAugmentingPath pathWalk where
  isPath := by rw [Walk.isPath_def]; decide
  ne := by decide
  start_notMem := by simp [pathMatching]
  end_notMem := by simp [pathMatching]
  isAlternating := by
    intro v w w' hww' hvw hvw'
    simp only [spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges, pathMatching,
      subgraphOfAdj_adj] at hvw hvw' ⊢
    revert v w w'
    decide

/-- By Berge's lemma, `{12}` is not a maximum matching of the path. -/
example : ¬pathMatching.IsMaximumMatching := fun h =>
  ((IsMatching.subgraphOfAdj _).isMaximumMatching_iff_forall_not_isAugmentingPath.mp h)
    0 3 pathWalk pathWalk_isAugmentingPath

/-- The perfect matching `{01, 23}` of the path. -/
def pathPerfect : (pathGraph 4).Subgraph where
  verts := Set.univ
  Adj x y := x.val / 2 = y.val / 2 ∧ x ≠ y
  adj_sub {x y} h := pathGraph_adj.mpr (by
    have := x.isLt
    have := y.isLt
    have := Fin.val_ne_of_ne h.2
    omega)
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩

theorem pathPerfect_isPerfectMatching : pathPerfect.IsPerfectMatching := by
  rw [isPerfectMatching_iff]
  unfold ExistsUnique pathPerfect
  decide

/-- `{01, 23}` is a maximum matching of the path: the notion is not vacuous. -/
example : pathPerfect.IsMaximumMatching := pathPerfect_isPerfectMatching.isMaximumMatching

/-! ### The `5`-cycle -/

/-- The matching `{01, 23}` of the `5`-cycle. -/
def cycleMatching : (cycleGraph 5).Subgraph where
  verts := ↑({0, 1, 2, 3} : Finset (Fin 5))
  Adj x y := x.val / 2 = y.val / 2 ∧ x ≠ y ∧ x.val < 4 ∧ y.val < 4
  adj_sub {x y} h := by
    revert x y
    decide
  edge_vert {x y} h := by
    rw [Finset.mem_coe]
    revert x y
    decide
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.2, h.2.2.1⟩⟩

theorem cycleMatching_isMatching : cycleMatching.IsMatching := by
  intro v hv
  rw [cycleMatching, Finset.mem_coe] at hv
  revert v
  unfold ExistsUnique cycleMatching
  decide

/-- `U = ∅` certifies that `{01, 23}` is a maximum matching of the `5`-cycle: the cycle has an odd
component, so `|V(M)| + o(C₅) = 4 + 1 = 5 + |∅|`. -/
example : cycleMatching.IsMaximumMatching := by
  refine (IsMatching.isMaximumMatching_iff_exists_ncard_verts_add_ncard_oddComponents_eq
    cycleMatching_isMatching).mpr ⟨∅, ?_⟩
  have hverts : cycleMatching.verts.ncard = 4 := by
    rw [cycleMatching, Set.ncard_coe_finset]
    rfl
  have hle := cycleMatching_isMatching.ncard_verts_add_ncard_oddComponents_le ∅
  have hodd := (odd_ncard_oddComponents ((⊤ : (cycleGraph 5).Subgraph).deleteVerts ∅).coe).mpr
    (by rw [card_verts_deleteVerts_top, Set.ncard_empty, Nat.card_eq_fintype_card,
      Fintype.card_fin]; decide)
  rw [hverts, Nat.card_eq_fintype_card, Fintype.card_fin, Set.ncard_empty] at hle ⊢
  obtain ⟨k, hk⟩ := hodd
  omega

/-! ### The star `K_{1,3}` -/

/-- The matching `{01}` of the star with centre `0` and leaves `1`, `2`, `3`. -/
def starMatching : (starGraph (0 : Fin 4)).Subgraph :=
  (starGraph (0 : Fin 4)).subgraphOfAdj (starGraph_center_adj (by decide : (0 : Fin 4) ≠ 1))

/-- `U = {0}` certifies that `{01}` is a maximum matching of the star: deleting the centre leaves
three isolated vertices, so `|V(M)| + o(G - U) = 2 + 3 = 4 + |U|`. -/
example : starMatching.IsMaximumMatching := by
  have hM : starMatching.IsMatching := IsMatching.subgraphOfAdj _
  refine hM.isMaximumMatching_iff_exists_ncard_verts_add_ncard_oddComponents_eq.mpr ⟨{0}, ?_⟩
  have hverts : starMatching.verts.ncard = 2 := by
    rw [starMatching, subgraphOfAdj_verts, Set.ncard_pair (by decide)]
  have hle := hM.ncard_verts_add_ncard_oddComponents_le {0}
  have hge := card_le_ncard_oddComponents_of_forall_not_adj
    (H := ((⊤ : (starGraph (0 : Fin 4)).Subgraph).deleteVerts {0}).coe) fun x y hxy => by
      rw [Subgraph.coe_adj, deleteVerts_adj, Subgraph.top_adj, starGraph_adj] at hxy
      obtain ⟨-, hx, -, hy, -, hxy | hxy⟩ := hxy
      · exact hx hxy
      · exact hy hxy
  rw [card_verts_deleteVerts_top, Set.ncard_singleton, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hge
  rw [hverts, Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at hle ⊢
  omega

end ComplexityTests.GeneralMatching
