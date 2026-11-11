/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.GomoryHu.Construction

/-!
# Tests for Gusfield's Gomory–Hu tree algorithm

Exercise `Cslib.Algorithms.Lean.GomoryHu.gomoryHuM` (Gusfield's algorithm with one Edmonds–Karp
computation per non-root vertex) on the weighted graph on `Fin 4` with edges `01:4`, `12:2`,
`23:3`, `02:1`, `13:1` (the graph of `CslibFrontierTests.GomoryHu`):

* rooted at `0`, the algorithm returns parent array `[0, 0, 1, 2]` (the path `0 - 1 - 2 - 3`),
  and edge weights `[0, 5, 4, 4]`, matching `minCutBetween W u (p u)` at every vertex;
* rooted at `3`, it returns `[1, 2, 3, 3]` with weights `[5, 4, 4, 0]`. This run takes the swap
  branch of Gusfield's step: when `s = 1` is processed, it takes the place of its parent `0` and
  inherits `0`'s recorded weight `4` while `0` receives `5`;
* the charged running time, and its instances of the sparse and dense bounds;
* non-minimum cut and inconsistent value oracles refuting the conclusions of
  `isGomoryHuTree_gusfieldParent` and `gusfieldWithWeights_weight_eq`;
* edge cases: one vertex, and an edgeless graph with empty adjacency lists.
-/

namespace CslibFrontierTests.GomoryHuConstruction

open Cslib.WeightedCut Cslib.Algorithms.Lean Cslib.Algorithms.Lean.MaxFlow
  Cslib.Algorithms.Lean.GomoryHu
open SimpleGraph (parentGraph parentGraph_adj edgeSide edgeSide_eq_of_forall_adj)

/-- The weighted graph on `Fin 4` with edges `01:4`, `12:2`, `23:3`, `02:1`, `13:1`. -/
private def W : Fin 4 → Fin 4 → ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => 4 | 1, 0 => 4
  | 1, 2 => 2 | 2, 1 => 2
  | 2, 3 => 3 | 3, 2 => 3
  | 0, 2 => 1 | 2, 0 => 1
  | 1, 3 => 1 | 3, 1 => 1
  | _, _ => 0

private theorem hW : IsMultigraph W := by
  unfold IsMultigraph
  decide

/-- Sparse adjacency lists of `W`. -/
private def adjW : Fin 4 → List (Fin 4)
  | ⟨0, _⟩ => [1, 2]
  | ⟨1, _⟩ => [0, 2, 3]
  | ⟨2, _⟩ => [0, 1, 3]
  | ⟨3, _⟩ => [1, 2]

private theorem hadjW : ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ adjW u := by decide

/-- Adjacency lists missing the edge `23` do not cover `W`. -/
example : ¬ ∀ u v, u ≠ v → 0 < W u v + W v u → v ∈ (fun _ => [] : Fin 4 → List (Fin 4)) u := by
  decide

/-! ### The tree and edge weights computed from the root `0` -/

private theorem gomoryHuM_zero_parent : (gomoryHuM W adjW 0).ret.parent = #v[0, 0, 1, 2] := by
  decide

private theorem gomoryHuM_zero_weight : (gomoryHuM W adjW 0).ret.weight = #v[0, 5, 4, 4] := by
  decide

/-- The Edmonds–Karp minimum cuts and maximum flow values used by the run rooted at `0`. -/
example : ekCut W adjW 1 0 = {1, 2, 3} := by decide
example : ekCut W adjW 2 1 = {2, 3} := by decide
example : ekCut W adjW 3 2 = {3} := by decide
example : ekValue W adjW 1 0 = 5 := by decide
example : ekValue W adjW 2 1 = 4 := by decide
example : ekValue W adjW 3 2 = 4 := by decide

/-- The output tree is the path `0 - 1 - 2 - 3`. -/
private theorem parentGraph_gomoryHuM_zero :
    parentGraph (vget (gomoryHuM W adjW 0).ret.parent) = SimpleGraph.pathGraph 4 := by
  ext x y
  rw [parentGraph_adj, SimpleGraph.pathGraph_adj, gomoryHuM_zero_parent]
  revert x y
  decide

/-- The output is also a parent array rooted at `0` in the sense of `SimpleGraph.parentTree`. -/
example : SimpleGraph.parentTree (vget (gomoryHuM W adjW 0).ret.parent) =
    SimpleGraph.pathGraph 4 := by
  rw [SimpleGraph.parentTree_eq_parentGraph (by rw [gomoryHuM_zero_parent]; decide),
    parentGraph_gomoryHuM_zero]

/-- Correctness of the tree and edge weights, instantiated at root `0`. -/
example : IsGomoryHuTree (cutWeight W) (parentGraph (vget (gomoryHuM W adjW 0).ret.parent)) :=
  isGomoryHuTree_gomoryHuM hW hadjW 0

example (u : Fin 4) :
    vget (gomoryHuM W adjW 0).ret.weight u =
      minCutBetween W u (vget (gomoryHuM W adjW 0).ret.parent u) :=
  vget_gomoryHuM_weight_eq_minCutBetween hW hadjW 0 u

example : minCutBetween W 1 0 = 5 ∧ minCutBetween W 2 1 = 4 ∧ minCutBetween W 3 2 = 4 := by
  have h1 := vget_gomoryHuM_weight_eq_minCutBetween hW hadjW 0 1
  have h2 := vget_gomoryHuM_weight_eq_minCutBetween hW hadjW 0 2
  have h3 := vget_gomoryHuM_weight_eq_minCutBetween hW hadjW 0 3
  rw [gomoryHuM_zero_weight, gomoryHuM_zero_parent] at h1 h2 h3
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- Hence the path `0 - 1 - 2 - 3` is a Gomory–Hu tree of `W`. -/
example : IsGomoryHuTree (cutWeight W) (SimpleGraph.pathGraph 4) :=
  parentGraph_gomoryHuM_zero ▸ isGomoryHuTree_gomoryHuM hW hadjW 0

/-! ### The tree and edge weights computed from the root `3` (swap branch) -/

/-- The Edmonds–Karp minimum cuts and maximum flow values used by the run rooted at `3`. -/
example : ekCut W adjW 0 3 = {0, 1} := by decide
example : ekCut W adjW 1 0 = {1, 2, 3} := by decide
example : ekCut W adjW 2 3 = {0, 1, 2} := by decide
example : ekValue W adjW 0 3 = 4 := by decide
example : ekValue W adjW 1 0 = 5 := by decide
example : ekValue W adjW 2 3 = 4 := by decide

/-- The run rooted at `3`, vertex by vertex. Processing `s = 0` (parent `3`, cut `{0, 1}`, flow `4`)
re-hangs `1` below `0` and sets `fl[0] = 4`. Processing `s = 1` (parent `t = 0`, cut `{1, 2, 3}`,
flow `5`) takes the swap branch, since the cut contains the parent `3` of `t`: `1` takes the place
of `0` and inherits `fl[0] = 4`, while `0` is hung below `1` with `fl[0] = 5`. Processing `s = 2`
(parent `3`, cut `{0, 1, 2}`, flow `4`) re-hangs `1` below `2` and sets `fl[2] = 4`. -/
example : (gomoryHuLoopM W adjW 3 [0] (Vector.replicate 4 3) (Vector.replicate 4 0)).ret =
    { parent := #v[3, 0, 3, 3], weight := #v[4, 0, 0, 0] } := by decide
example : (gomoryHuLoopM W adjW 3 [0, 1] (Vector.replicate 4 3) (Vector.replicate 4 0)).ret =
    { parent := #v[1, 3, 3, 3], weight := #v[5, 4, 0, 0] } := by decide
example : (gomoryHuM W adjW 3).ret =
    { parent := #v[1, 2, 3, 3], weight := #v[5, 4, 4, 0] } := by decide

/-- The root `3` gives the same path `0 - 1 - 2 - 3` and matching edge weights `5, 4, 4`. -/
example : parentGraph (vget (gomoryHuM W adjW 3).ret.parent) = SimpleGraph.pathGraph 4 := by
  ext x y
  rw [parentGraph_adj, SimpleGraph.pathGraph_adj,
    show (gomoryHuM W adjW 3).ret.parent = #v[1, 2, 3, 3] by decide]
  revert x y
  decide

example (u : Fin 4) :
    vget (gomoryHuM W adjW 3).ret.weight u =
      minCutBetween W u (vget (gomoryHuM W adjW 3).ret.parent u) :=
  vget_gomoryHuM_weight_eq_minCutBetween hW hadjW 3 u

/-! ### Running time -/

/-- The charged running time of the run rooted at `0`. -/
example : (gomoryHuM W adjW 0).time = 313 := by decide

/-- The general bound: `adjSteps adjW = 10`, so the bound is
`3 * 4 + 3 * ((10 * 2 + 2) * (10 + 5 * 4) + 4 + 3) = 2013`. -/
example : (gomoryHuM W adjW 0).time ≤ 2013 := by
  have h := gomoryHuM_time_le hadjW 0
  rwa [show adjSteps adjW = 10 by decide] at h

/-- The dense bound on `Fin 4`. -/
example : (gomoryHuM W (defaultAdj 4) 0).time ≤ 3705 :=
  gomoryHuM_time_le_dense 0

/-! ### Non-minimum cut and inconsistent value oracles -/

/-- The oracle returning the singleton `{s}`, a cut that is not minimal in general. -/
private def singletonCut (s _ : Fin 4) : Finset (Fin 4) := {s}

/-- With the singleton oracle, the abstract algorithm keeps the star centred at `0`. -/
private theorem gusfieldParent_singletonCut :
    gusfieldParent singletonCut 0 [1, 2, 3] = fun _ => 0 := by decide

/-- The star centred at `0` is not a Gomory–Hu tree of `W`: the side `{1}` of its edge `10` weighs
`7`, but `{1, 2, 3}` separates `1` from `0` with weight `5`. So `isGomoryHuTree_gusfieldParent`
needs its minimum cut hypothesis. -/
example :
    ¬ IsGomoryHuTree (cutWeight W) (parentGraph (gusfieldParent singletonCut 0 [1, 2, 3])) := by
  rw [gusfieldParent_singletonCut]
  intro hT
  have hadj : (parentGraph fun _ : Fin 4 => (0 : Fin 4)).Adj 1 0 := by
    rw [parentGraph_adj]
    decide
  have hside : edgeSide (parentGraph fun _ : Fin 4 => (0 : Fin 4)) 1 0 = {1} := by
    refine edgeSide_eq_of_forall_adj hT.isTree hadj (by decide) (by decide) ?_
    intro x y hxy
    rw [parentGraph_adj] at hxy
    revert x y
    decide
  have h := hT.isMinCutBetween_edgeSide hadj
  rw [hside] at h
  revert h
  unfold IsMinCutBetween
  decide

/-- Using a wrong value oracle (`99` on every query) produces wrong edge weights even with an
exact minimum-cut oracle: `gusfieldWithWeights_weight_eq` needs `val s t = f (C s t)`. -/
example :
    let res := gusfieldWithWeights (ekCut W adjW) (fun _ _ => 99) 0 0 [1, 2, 3]
    res.2 1 ≠ cutWeight W (edgeSide (parentGraph res.1) 1 (res.1 1)) := by
  dsimp only
  have hw1 : (gusfieldWithWeights (ekCut W adjW) (fun _ _ => 99) 0 0 [1, 2, 3]).2 1 = 99 := by
    decide
  have hp1 : (gusfieldWithWeights (ekCut W adjW) (fun _ _ => 99) 0 0 [1, 2, 3]).1 1 = 0 := by
    decide
  have hgraph :
      parentGraph (gusfieldWithWeights (ekCut W adjW) (fun _ _ => 99) 0 0 [1, 2, 3]).1 =
        SimpleGraph.pathGraph 4 := by
    ext x y
    rw [parentGraph_adj, SimpleGraph.pathGraph_adj]
    revert x y
    decide
  have htree : IsGomoryHuTree (cutWeight W) (SimpleGraph.pathGraph 4) :=
    parentGraph_gomoryHuM_zero ▸ isGomoryHuTree_gomoryHuM hW hadjW 0
  have hadj : (SimpleGraph.pathGraph 4).Adj 1 0 := by decide
  have hside : edgeSide (SimpleGraph.pathGraph 4) 1 0 = {1, 2, 3} := by
    refine edgeSide_eq_of_forall_adj htree.isTree hadj (by decide) (by decide) ?_
    intro x y hxy
    rw [SimpleGraph.pathGraph_adj] at hxy
    revert x y
    decide
  rw [hw1, hgraph, hp1, hside]
  decide

/-! ### Edge cases -/

/-- One vertex: parent array `[0]` and weight array `[0]`, in `3` charged steps. -/
example : (gomoryHuM (fun _ _ => 0) (defaultAdj 1) 0).ret =
    { parent := #v[0], weight := #v[0] } := by decide
example : (gomoryHuM (fun _ _ => 0) (defaultAdj 1) 0).time = 3 := by decide

/-- An edgeless graph with empty adjacency lists: the star centred at the root is a Gomory–Hu
tree, every cut and recorded edge weight having weight `0`. -/
example : (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret =
    { parent := #v[0, 0, 0], weight := #v[0, 0, 0] } := by decide

example : IsGomoryHuTree (cutWeight fun _ _ : Fin 3 => 0)
    (parentGraph (vget (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret.parent)) :=
  isGomoryHuTree_gomoryHuM ⟨fun _ _ => rfl, fun _ => rfl⟩ (fun _ _ _ h => absurd h (by decide)) 0

example (u : Fin 3) :
    vget (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret.weight u =
      minCutBetween (fun _ _ : Fin 3 => 0) u
        (vget (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret.parent u) :=
  vget_gomoryHuM_weight_eq_minCutBetween ⟨fun _ _ => rfl, fun _ => rfl⟩
    (fun _ _ _ h => absurd h (by decide)) 0 u

end CslibFrontierTests.GomoryHuConstruction
