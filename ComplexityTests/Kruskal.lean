/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Kruskal.SimpleGraph

/-!
# Worked Kruskal Minimum Spanning Forest and Tree Examples

These kernel-checked examples (using no `native_decide`) exercise:

1. Empty-vertex (`n = 0`), singleton (`n = 1`), and negative-weight self-loop boundary cases.
2. A 6-vertex disconnected multigraph with negative `ℤ` weights, parallel edges, a negative-weight
   self-loop `(2, 2, -10)` (rejected despite having minimum weight), and duplicate weights — showing
   both `IsMinSpanningForest` and a concrete non-uniqueness witness (`¬F₁.Perm F₂`) when edge
   weights are not pairwise distinct, plus negative witnesses (`¬IsAcyclic`, `¬IsSpanningForest`,
   `¬IsMinSpanningForest`).
3. Distinct-weight uniqueness (`perm_kruskalEdges_of_isMinSpanningTree_of_nodup_weights`) and exact
   `TimeM Cost` (`comparisons` and `ufSteps`) accounting on a connected 4-vertex graph.
4. End-to-end `SimpleGraph` bridge (`graphEdges`, `kruskalGraph`, `kruskalGraph_isTree`,
   `sum_edgeFinset_kruskalGraph_le_of_isTree`, `eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn`,
   and `kruskalGraphM`) on `K₄` with distinct undirected edge weights.
-/

public section

namespace ComplexityTests.Kruskal

open Cslib.Algorithms.Lean.Kruskal
open Cslib.Algorithms.Lean.DisjointSet

/-! ### 1. Boundary cases (`n = 0`, `n = 1`, self-loops) -/

example :
    kruskalEdges ([] : List (WeightedEdge 0 ℕ)) = [] ∧
      (kruskalM ([] : List (WeightedEdge 0 ℕ))).time = ⟨0, 0⟩ ∧
      kruskalEdges ([⟨0, 0, (-10 : ℤ)⟩] : List (WeightedEdge 1 ℤ)) = [] ∧
      (kruskalM ([⟨0, 0, (-10 : ℤ)⟩] : List (WeightedEdge 1 ℤ))).ret.ufState.numComp = 1 ∧
      ¬IsAcyclic ([⟨0, 0, (-10 : ℤ)⟩] : List (WeightedEdge 1 ℤ)) := by
  refine ⟨by simp [kruskalEdges], by (ext <;> simp [kruskalM, kruskalScanM]); rfl,
    by simp [kruskalEdges], ?_, by decide⟩
  rw [kruskalM_ret, sortEdges_singleton]
  rfl

/-! ### 2. Disconnected multigraph with negative & duplicate `ℤ` weights (`Fin 6`) -/

/-- Six-vertex multigraph with components `{0, 1, 2}`, `{3, 4}`, and `{5}`:
- negative-weight self-loop `(2, 2, -10)` (must be rejected despite smallest weight),
- negative bridge `(1, 2, -4)`,
- tied cycle edges `(0, 1, 2)` and `(0, 2, 2)`,
- parallel heavier edge `(0, 1, 7)`,
- component `{3, 4}` with parallel edges `(3, 4, -1)` and `(4, 3, 5)`. -/
def disconnectedMulti : List (WeightedEdge 6 ℤ) :=
  [ ⟨0, 1, 7⟩
  , ⟨2, 2, -10⟩
  , ⟨0, 2, 2⟩
  , ⟨3, 4, -1⟩
  , ⟨1, 2, -4⟩
  , ⟨4, 3, 5⟩
  , ⟨0, 1, 2⟩ ]

theorem sortEdges_disconnectedMulti :
    sortEdges disconnectedMulti =
      [ ⟨2, 2, -10⟩
      , ⟨1, 2, -4⟩
      , ⟨3, 4, -1⟩
      , ⟨0, 2, 2⟩
      , ⟨0, 1, 2⟩
      , ⟨4, 3, 5⟩
      , ⟨0, 1, 7⟩ ] := by
  simp [disconnectedMulti, sortEdges_cons_cons]

theorem kruskalEdges_disconnectedMulti :
    kruskalEdges disconnectedMulti = [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 2, 2⟩] := by
  rw [kruskalEdges, sortEdges_disconnectedMulti]
  rfl

-- Kruskal rejects `(2, 2, -10)`, `(0, 1, 2)` (closing triangle `{0, 1, 2}` after `(1, 2, -4)` and
-- `(0, 2, 2)`), `(4, 3, 5)`, and `(0, 1, 7)`, achieving minimum total weight `-4 + -1 + 2 = -3`
-- across `3` connected components.
example :
    kruskalEdges disconnectedMulti = [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 2, 2⟩] ∧
      totalWeight (kruskalEdges disconnectedMulti) = -3 ∧
      (kruskalM disconnectedMulti).ret.forest = [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 2, 2⟩] ∧
      (kruskalM disconnectedMulti).ret.ufState.numComp = 3 ∧
      IsMinSpanningForest disconnectedMulti (kruskalEdges disconnectedMulti) := by
  refine ⟨kruskalEdges_disconnectedMulti, ?_, ?_, ?_,
    kruskalEdges_isMinSpanningForest disconnectedMulti⟩
  · rw [kruskalEdges_disconnectedMulti]
    simp
  · rw [kruskalM_forest]
    exact kruskalEdges_disconnectedMulti
  · rw [kruskalM_ret, sortEdges_disconnectedMulti]
    rfl

/-- Alternate minimum spanning forest choosing `(0, 1, 2)` instead of the tied edge `(0, 2, 2)`. -/
def altMinForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 1, 2⟩]

/-- Suboptimal spanning forest choosing `(0, 1, 7)` (total weight `2 > -3`). -/
def suboptimalForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 1, 7⟩]

/-- Non-spanning acyclic subset omitting `(3, 4, -1)` (`4` components instead of `3`). -/
def nonSpanningForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨0, 2, 2⟩]

-- Both `kruskalEdges disconnectedMulti` and `altMinForest` are `IsMinSpanningForest`, yet they are
-- not permutations (`¬altMinForest.Perm (kruskalEdges disconnectedMulti)`), showing necessity of
-- the distinct-weights hypothesis in `perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights`.
example :
    IsMinSpanningForest disconnectedMulti altMinForest ∧
      ¬altMinForest.Perm (kruskalEdges disconnectedMulti) ∧
      IsSpanningForest disconnectedMulti suboptimalForest ∧
      ¬IsMinSpanningForest disconnectedMulti suboptimalForest ∧
      IsAcyclic nonSpanningForest ∧
      ¬IsSpanningForest disconnectedMulti nonSpanningForest := by
  have hk_eq := kruskalEdges_disconnectedMulti
  have halt_sf : IsSpanningForest disconnectedMulti altMinForest := by
    refine ⟨?_, by decide, by decide⟩
    exact ⟨[⟨3, 4, -1⟩, ⟨1, 2, -4⟩, ⟨0, 1, 2⟩], by decide, by decide⟩
  have hsub_sf : IsSpanningForest disconnectedMulti suboptimalForest := by
    refine ⟨?_, by decide, by decide⟩
    exact ⟨[⟨0, 1, 7⟩, ⟨3, 4, -1⟩, ⟨1, 2, -4⟩], by decide, by decide⟩
  refine ⟨⟨halt_sf, ?_⟩, ?_, hsub_sf, ?_, by decide, ?_⟩
  · intro F' hF'
    have hmin := (kruskalEdges_isMinSpanningForest disconnectedMulti).2 F' hF'
    have heq : totalWeight altMinForest = totalWeight (kruskalEdges disconnectedMulti) := by
      rw [hk_eq]
      simp [altMinForest]
    exact heq.trans_le hmin
  · rw [hk_eq]
    decide
  · intro hmin
    have hle := hmin.2 (kruskalEdges disconnectedMulti)
      (kruskalEdges_isSpanningForest disconnectedMulti)
    rw [hk_eq] at hle
    simp [suboptimalForest] at hle
  · intro hsf
    have hcomp := congrArg Partition.numComponents hsf.2.2
    revert hcomp
    decide

/-! ### 3. Connected graph with distinct weights & `TimeM Cost` bounds (`Fin 4`) -/

def diamondEdges : List (WeightedEdge 4 ℕ) :=
  [ ⟨0, 3, 9⟩
  , ⟨0, 1, 1⟩
  , ⟨1, 2, 4⟩
  , ⟨0, 2, 3⟩
  , ⟨2, 3, 2⟩ ]

example :
    kruskalEdges diamondEdges = [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] ∧
      totalWeight (kruskalEdges diamondEdges) = 6 ∧
      IsMinSpanningTree diamondEdges (kruskalEdges diamondEdges) ∧
      (∀ T, IsMinSpanningTree diamondEdges T → T.Perm [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩]) ∧
      (kruskalScanM (UnionFind.init 4) (sortEdges diamondEdges)).time.ufSteps = 21 ∧
      (kruskalM diamondEdges).time.comparisons ≤
        diamondEdges.length * Nat.clog 2 diamondEdges.length ∧
      (kruskalM diamondEdges).time.ufSteps ≤
        diamondEdges.length * (2 * Nat.log 2 4 + 3) := by
  have hconn : (edgePartition diamondEdges).numComponents = 1 := by decide
  have hnodup : (diamondEdges.map WeightedEdge.weight).Nodup := by decide
  have hsort : sortEdges diamondEdges =
      [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩, ⟨1, 2, 4⟩, ⟨0, 3, 9⟩] := by
    simp [diamondEdges, sortEdges_cons_cons]
  have hk : kruskalEdges diamondEdges = [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] := by
    rw [kruskalEdges, hsort]
    rfl
  refine ⟨hk, ?_, kruskalEdges_isMinSpanningTree hconn, ?_, ?_,
    kruskalM_comparisons_le diamondEdges, kruskalM_ufSteps_le diamondEdges⟩
  · rw [hk]
    simp
  · intro T hT
    rw [← hk]
    exact perm_kruskalEdges_of_isMinSpanningTree_of_nodup_weights hconn hnodup hT
  · rw [hsort]
    rfl

/-! ### 4. Weighted `SimpleGraph (Fin 4)` bridge on `K₄` -/

/-- Complete graph `K₄` with kernel-reducible `DecidableRel` adjacency. -/
@[expose] def k4Graph : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel k4Graph.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

theorem k4Graph_eq_top : k4Graph = ⊤ := by
  ext u v
  simp [k4Graph]

/-- Injective symmetric edge weight on `Sym2 (Fin 4)` via kernel-reducible `Quot.lift`:
`2 ^ u + 2 ^ v` gives distinct values for all unordered pairs `{u, v}` with `u ≠ v`
(`{0,1} ↦ 3`, `{0,2} ↦ 5`, `{1,2} ↦ 6`, `{0,3} ↦ 9`, `{1,3} ↦ 10`, `{2,3} ↦ 12`). -/
@[expose] def k4Weight : Sym2 (Fin 4) → ℕ :=
  Quot.lift (fun p : Fin 4 × Fin 4 => 2 ^ p.1.1 + 2 ^ p.2.1) fun a b h => by
    cases h
    · rfl
    · exact Nat.add_comm _ _

theorem k4Weight_injOn : Set.InjOn k4Weight k4Graph.edgeSet := by
  intro z₁ hz₁ z₂ hz₂ hw
  revert z₁ z₂
  decide

-- On `K₄`, Kruskal selects the star `{0, 1}` (weight 3), `{0, 2}` (weight 5), `{0, 3}` (weight 9)
-- of total weight `17` (avoiding `{1, 2}` of weight 6 because `1` and `2` are already connected
-- through `0`), and `toSimpleGraph (kruskalGraph k4Graph k4Weight)` is the unique minimum spanning
-- tree of `K₄`!
example :
    (graphEdges k4Graph k4Weight).length = 6 ∧
      kruskalGraph k4Graph k4Weight =
        [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩] ∧
      (toSimpleGraph (kruskalGraph k4Graph k4Weight)).IsTree ∧
      (∑ z ∈ (toSimpleGraph (kruskalGraph k4Graph k4Weight)).edgeFinset,
          k4Weight z) = 17 ∧
      (∀ (T : SimpleGraph (Fin 4)) [Fintype T.edgeSet],
        T.IsTree →
        17 ≤ ∑ z ∈ T.edgeFinset, k4Weight z) ∧
      (∀ (T : SimpleGraph (Fin 4)) [Fintype T.edgeSet],
        T.IsTree →
        (∑ z ∈ T.edgeFinset, k4Weight z) ≤ 17 →
        T = toSimpleGraph (kruskalGraph k4Graph k4Weight)) ∧
      (kruskalGraphM k4Graph k4Weight).time.comparisons ≤ 6 * Nat.clog 2 6 ∧
      (kruskalGraphM k4Graph k4Weight).time.ufSteps ≤ 6 * (2 * Nat.log 2 4 + 3) := by
  have hconn : k4Graph.Connected := by
    rw [k4Graph_eq_top]
    exact SimpleGraph.connected_top
  have hge : graphEdges k4Graph k4Weight =
      [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩, ⟨1, 2, 6⟩, ⟨1, 3, 10⟩, ⟨2, 3, 12⟩] := rfl
  have hsort : sortEdges (graphEdges k4Graph k4Weight) =
      [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨1, 2, 6⟩, ⟨0, 3, 9⟩, ⟨1, 3, 10⟩, ⟨2, 3, 12⟩] := by
    rw [hge]
    simp [sortEdges_cons_cons]
  have hk : kruskalGraph k4Graph k4Weight = [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩] := by
    rw [kruskalGraph, kruskalEdges, hsort]
    rfl
  have hsum :
      (∑ z ∈ (toSimpleGraph (kruskalGraph k4Graph k4Weight)).edgeFinset,
        k4Weight z) = 17 := by
    rw [sum_edgeFinset_toSimpleGraph_kruskalGraph, hk]
    rfl
  refine ⟨rfl, hk, (kruskalGraph_isTree hconn k4Weight).1, hsum, ?_, ?_, ?_, ?_⟩
  · intro T _ hT
    have hle : T ≤ k4Graph := by rw [k4Graph_eq_top]; exact le_top
    rw [← hsum]
    exact sum_edgeFinset_kruskalGraph_le_of_isTree hconn k4Weight T hle hT
  · intro T _ hT hopt
    have hle : T ≤ k4Graph := by rw [k4Graph_eq_top]; exact le_top
    rw [← hsum] at hopt
    exact eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn hconn k4Weight k4Weight_injOn hle hT hopt
  · have hc := kruskalGraphM_comparisons_le k4Graph k4Weight
    have hcard : k4Graph.edgeFinset.card = 6 := by
      rw [← length_graphEdges k4Graph k4Weight]
      rfl
    rwa [hcard] at hc
  · have hu := kruskalGraphM_ufSteps_le k4Graph k4Weight
    have hcard : k4Graph.edgeFinset.card = 6 := by
      rw [← length_graphEdges k4Graph k4Weight]
      rfl
    rwa [hcard] at hu

end ComplexityTests.Kruskal
