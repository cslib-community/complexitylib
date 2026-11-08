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

* rooted at `0`, the algorithm returns the parent array `[0, 0, 1, 2]`, the path `0 - 1 - 2 - 3`,
  which is therefore a Gomory–Hu tree of the graph;
* rooted at `3`, it returns `[1, 2, 3, 3]`, the same path. This run takes the swap branch of
  Gusfield's step: when `s = 1` is processed, it takes the place of its parent `0`;
* the charged running time, and its instance of the general bound;
* a cut oracle that does not return minimum cuts makes the abstract algorithm
  `gusfieldParent` output a star that is not a Gomory–Hu tree;
* edge cases: one vertex, and an edgeless graph with empty adjacency lists.
-/

namespace ComplexityTests.GomoryHuConstruction

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

/-! ### The tree computed from the root `0` -/

private theorem gomoryHuM_zero_ret : (gomoryHuM W adjW 0).ret = #v[0, 0, 1, 2] := by decide

/-- The Edmonds–Karp minimum cuts used by the run rooted at `0`. -/
example : ekCut W adjW 1 0 = {1, 2, 3} := by decide
example : ekCut W adjW 2 1 = {2, 3} := by decide
example : ekCut W adjW 3 2 = {3} := by decide

/-- The output tree is the path `0 - 1 - 2 - 3`. -/
private theorem parentGraph_gomoryHuM_zero :
    parentGraph (vget (gomoryHuM W adjW 0).ret) = SimpleGraph.pathGraph 4 := by
  ext x y
  rw [parentGraph_adj, SimpleGraph.pathGraph_adj, gomoryHuM_zero_ret]
  revert x y
  decide

/-- The output is also a parent array rooted at `0` in the sense of `SimpleGraph.parentTree`. -/
example : SimpleGraph.parentTree (vget (gomoryHuM W adjW 0).ret) = SimpleGraph.pathGraph 4 := by
  rw [SimpleGraph.parentTree_eq_parentGraph (by rw [gomoryHuM_zero_ret]; decide),
    parentGraph_gomoryHuM_zero]

/-- Correctness of the algorithm, instantiated. -/
example : IsGomoryHuTree (cutWeight W) (parentGraph (vget (gomoryHuM W adjW 0).ret)) :=
  isGomoryHuTree_gomoryHuM hW hadjW 0

/-- Hence the path `0 - 1 - 2 - 3` is a Gomory–Hu tree of `W`. -/
example : IsGomoryHuTree (cutWeight W) (SimpleGraph.pathGraph 4) :=
  parentGraph_gomoryHuM_zero ▸ isGomoryHuTree_gomoryHuM hW hadjW 0

/-! ### The tree computed from the root `3` (swap branch) -/

/-- The Edmonds–Karp minimum cuts used by the run rooted at `3`. -/
example : ekCut W adjW 0 3 = {0, 1} := by decide
example : ekCut W adjW 1 0 = {1, 2, 3} := by decide
example : ekCut W adjW 2 3 = {0, 1, 2} := by decide

/-- The run rooted at `3`, vertex by vertex. Processing `s = 0` (parent `3`, cut `{0, 1}`) re-hangs
`1` below `0`. Processing `s = 1` (parent `t = 0`, cut `{1, 2, 3}`) takes the swap branch, since
the cut contains the parent `3` of `t`: `1` takes the place of `0`, and `0` is hung below `1`.
Processing `s = 2` (parent `3`, cut `{0, 1, 2}`) re-hangs `1` below `2`. -/
example : (gomoryHuLoopM W adjW 3 [0] (Vector.replicate 4 3)).ret = #v[3, 0, 3, 3] := by decide
example : (gomoryHuLoopM W adjW 3 [0, 1] (Vector.replicate 4 3)).ret = #v[1, 3, 3, 3] := by decide
example : (gomoryHuM W adjW 3).ret = #v[1, 2, 3, 3] := by decide

/-- The root `3` gives the same path `0 - 1 - 2 - 3`. -/
example : parentGraph (vget (gomoryHuM W adjW 3).ret) = SimpleGraph.pathGraph 4 := by
  ext x y
  rw [parentGraph_adj, SimpleGraph.pathGraph_adj,
    show (gomoryHuM W adjW 3).ret = #v[1, 2, 3, 3] by decide]
  revert x y
  decide

/-! ### Running time -/

/-- The charged running time of the run rooted at `0`. -/
example : (gomoryHuM W adjW 0).time = 306 := by decide

/-- The general bound: `adjSteps adjW = 10`, so the bound is
`2 * 4 + 3 * ((10 * 2 + 2) * (10 + 5 * 4) + 4 + 2) = 2006`. -/
example : (gomoryHuM W adjW 0).time ≤ 2006 := by
  have h := gomoryHuM_time_le hadjW 0
  rwa [show adjSteps adjW = 10 by decide] at h

/-- The dense bound on `Fin 4`. -/
example : (gomoryHuM W (defaultAdj 4) 0).time ≤ 3698 :=
  gomoryHuM_time_le_dense 0

/-! ### Non-minimum cut oracles -/

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

/-! ### Edge cases -/

/-- One vertex: the parent array `[0]`, in `2` charged steps and no maximum flow computation. -/
example : (gomoryHuM (fun _ _ => 0) (defaultAdj 1) 0).ret = #v[0] := by decide
example : (gomoryHuM (fun _ _ => 0) (defaultAdj 1) 0).time = 2 := by decide

/-- An edgeless graph with empty adjacency lists: the star centred at the root is a Gomory–Hu
tree, every cut having weight `0`. -/
example : (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret = #v[0, 0, 0] := by decide

example : IsGomoryHuTree (cutWeight fun _ _ : Fin 3 => 0)
    (parentGraph (vget (gomoryHuM (fun _ _ => 0) (fun _ => []) (0 : Fin 3)).ret)) :=
  isGomoryHuTree_gomoryHuM ⟨fun _ _ => rfl, fun _ => rfl⟩ (fun _ _ _ h => absurd h (by decide)) 0

end ComplexityTests.GomoryHuConstruction
