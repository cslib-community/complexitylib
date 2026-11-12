/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.Menger
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Menger's Theorem Tests

Kernel-checked instances (no `native_decide`) exercising the moved `Digraph` / `SimpleGraph`
notions and all Menger theorem forms in `CslibFrontier.Algorithms.Lean.MaxFlow.Menger`:

1. **3-cube, antipodal vertices `0` and `7`:** two-terminal edge and vertex connectivity (`3`),
   matching-separator test pinning `m = 3`, the `IsVertexSeparator` ↔ `IsSeparator` bridge, and
   `A`–`B` set Menger with `A = {0, 1, 2}`, `B = {5, 6, 7}` (`m = 3`).
2. **A 4-vertex digraph:** two-terminal arc and vertex connectivity (`2`), plus overlapping
   set-to-set `A`–`B` Menger (`A = {0, 1}`, `B = {1, 3}`, `m = 2`).
3. **Global `k`-connectivity edge cases:** `K₃` (`2`-vertex-connected via explicit adjacent-vertex
   injective path families), `K₂` (`1`-vertex-connected but not `2`-vertex-connected), `K₁`
   (`0`-vertex-connected but not `1`-vertex-connected), and `cube` (`3`-edge- and
   `3`-vertex-connected).
4. **Integral-capacity path packing:** a 3-vertex network of capacity `3` with a matching cut.
5. **Directed multidigraph arc-disjoint Menger:** a 3-vertex, 5-arc multidigraph with parallel arcs
   achieving max `3` arc-disjoint dipaths and matching `outArcs` cut.
-/

public section

namespace CslibFrontierTests.Menger

open Cslib.Algorithms.Lean.MaxFlow SimpleGraph

/-! ### 1. The 3-cube -/

/-- The 3-cube on `Fin 8`: `i ~ j` iff `i` and `j` differ in exactly one bit. -/
def cube : SimpleGraph (Fin 8) where
  Adj i j := i.val ^^^ j.val = 1 ∨ i.val ^^^ j.val = 2 ∨ i.val ^^^ j.val = 4
  symm := ⟨fun _ _ h => by rwa [Nat.xor_comm]⟩
  loopless := ⟨fun i h => by simp at h⟩

instance : DecidableRel cube.Adj := fun i j =>
  inferInstanceAs (Decidable (i.val ^^^ j.val = 1 ∨ i.val ^^^ j.val = 2 ∨ i.val ^^^ j.val = 4))

/-- Three internally disjoint `0`–`7` paths in the cube. -/
def cubeW : Fin 3 → cube.Walk 0 7
  | 0 => .cons (v := 1) (by decide) (.cons (v := 3) (by decide) (.cons (by decide) .nil))
  | 1 => .cons (v := 2) (by decide) (.cons (v := 6) (by decide) (.cons (by decide) .nil))
  | 2 => .cons (v := 4) (by decide) (.cons (v := 5) (by decide) (.cons (by decide) .nil))

example : (cubeW 0).support = [0, 1, 3, 7] := by decide

theorem cubeW_isPath : ∀ i, (cubeW i).IsPath := fun i =>
  Walk.IsPath.mk' (by revert i; decide)

theorem cubeW_internallyDisjoint : SimpleGraph.InternallyDisjoint cubeW := by
  intro i j
  revert i j
  decide

theorem cubeW_edgeDisjoint :
    Pairwise fun i j => ∀ e ∈ (cubeW i).edges, e ∉ (cubeW j).edges := by
  intro i j
  revert i j
  decide

example : cube.IsEdgeReachable 3 0 7 :=
  (isEdgeReachable_iff_exists_edgeDisjoint cube 0 7 3).mpr
    ⟨cubeW, cubeW_isPath, cubeW_edgeDisjoint⟩

theorem cube_not_reachable : ¬ (cube.deleteEdges ↑({s(0, 1), s(0, 2), s(0, 4)} :
    Finset (Sym2 (Fin 8)))).Reachable 0 7 :=
  not_reachable_deleteEdges_of_forall_adj (S := ↑({0} : Finset (Fin 8))) (by simp) (by simp)
    (by decide)

example : ¬ cube.IsEdgeReachable 4 0 7 := by
  intro h
  apply cube_not_reachable
  apply h
  rw [Set.encard_coe_eq_coe_finsetCard]
  decide

theorem cube_sep : cube.IsVertexSeparator 0 7 {1, 2, 4} :=
  isVertexSeparator_of_forall_adj (S := {0}) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The bridge between `IsVertexSeparator` and `SimpleGraph.IsSeparator`. -/
example : cube.IsSeparator {0} {7} ↑({1, 2, 4} : Finset (Fin 8)) :=
  (isVertexSeparator_iff_isSeparator.mp cube_sep).2.2

/-- Every `0`–`7` separator of the cube has at least three vertices (Menger, from `cubeW`). -/
example : ∀ T : Finset (Fin 8), cube.IsVertexSeparator 0 7 T → 3 ≤ T.card :=
  (exists_internallyDisjoint_iff_forall_isVertexSeparator cube 0 7 3).mp
    ⟨cubeW, cubeW_isPath, cubeW_internallyDisjoint⟩

example : ¬ ∃ W : Fin 4 → cube.Walk 0 7, (∀ i, (W i).IsPath) ∧
    SimpleGraph.InternallyDisjoint W := by
  rw [exists_internallyDisjoint_iff_forall_isVertexSeparator]
  intro h
  have := h _ cube_sep
  simp at this

/-- The matching-cut form of Menger, used as stated: it yields internally disjoint `0`–`7` paths
and a separator of the same size `m`, and weak duality against `cubeW` and `cube_sep` pins
`m = 3`. -/
example : ∃ (m : ℕ) (W : Fin m → cube.Walk 0 7), m = 3 ∧ (∀ i, (W i).IsPath) ∧
    SimpleGraph.InternallyDisjoint W ∧
    ∃ T : Finset (Fin 8), cube.IsVertexSeparator 0 7 T ∧ T.card = m := by
  obtain ⟨m, W, hW, hdisj, T, hT, hTm⟩ :=
    exists_internallyDisjoint_eq_isVertexSeparator cube (u := 0) (v := 7) (by decide) (by decide)
  refine ⟨m, W, ?_, hW, hdisj, T, hT, hTm⟩
  have h1 := card_le_card_of_internallyDisjoint_of_isVertexSeparator hdisj cube_sep
  have h2 := card_le_card_of_internallyDisjoint_of_isVertexSeparator cubeW_internallyDisjoint hT
  have h3 : ({1, 2, 4} : Finset (Fin 8)).card = 3 := by decide
  omega

/-- Endpoints of three vertex-disjoint `{0, 1, 2}`–`{5, 6, 7}` walks in the cube. -/
def cubeABStarts : Fin 3 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2

def cubeABEnds : Fin 3 → Fin 8
  | 0 => 5
  | 1 => 7
  | 2 => 6

def cubeABW : ∀ i : Fin 3, cube.Walk (cubeABStarts i) (cubeABEnds i)
  | 0 => .cons (v := 4) (by decide) (.cons (by decide) .nil)
  | 1 => .cons (v := 3) (by decide) (.cons (by decide) .nil)
  | 2 => .cons (by decide) .nil

theorem cubeABW_isPath : ∀ i, (cubeABW i).IsPath := fun i =>
  Walk.IsPath.mk' (by revert i; decide)

theorem cubeABW_disjoint :
    Pairwise fun i j => (cubeABW i).support.Disjoint (cubeABW j).support := by
  intro i j hij x h1 h2
  revert i j hij x h1 h2
  decide

theorem cubeAB_sep :
    cube.IsSeparator ↑({0, 1, 2} : Finset (Fin 8)) ↑({5, 6, 7} : Finset (Fin 8))
      ↑({0, 1, 2} : Finset (Fin 8)) :=
  isSeparator_of_subset_left Set.Subset.rfl

/-- Undirected `A`–`B` Menger as stated: pins `m = 3` for `A = {0, 1, 2}`, `B = {5, 6, 7}`. -/
example : ∃ (m : ℕ) (a b : Fin m → Fin 8) (W : ∀ i, cube.Walk (a i) (b i)),
    m = 3 ∧ (∀ i, a i ∈ ({0, 1, 2} : Finset (Fin 8))) ∧
      (∀ i, b i ∈ ({5, 6, 7} : Finset (Fin 8))) ∧ (∀ i, (W i).IsPath) ∧
      (Pairwise fun i j => (W i).support.Disjoint (W j).support) ∧
      ∃ Y : Finset (Fin 8), cube.IsSeparator ↑({0, 1, 2} : Finset (Fin 8))
        ↑({5, 6, 7} : Finset (Fin 8)) ↑Y ∧ Y.card = m := by
  obtain ⟨m, a, b, W, ha, hb, hW, hdisj, Y, hY, hYm⟩ := exists_disjoint_walk_eq_isSeparator cube
    ↑({0, 1, 2} : Finset (Fin 8)) ↑({5, 6, 7} : Finset (Fin 8))
  refine ⟨m, a, b, W, ?_, ha, hb, hW, hdisj, Y, hY, hYm⟩
  have h1 := card_le_card_of_disjoint_of_isSeparator ha hb W hdisj cubeAB_sep
  have h2 := card_le_card_of_disjoint_of_isSeparator (fun i => by revert i; decide)
    (fun i => by revert i; decide) cubeABW cubeABW_disjoint hY
  have h3 : ({0, 1, 2} : Finset (Fin 8)).card = 3 := by decide
  omega

/-! ### 2. A small digraph -/

/-- A small digraph: arcs `0 → 1`, `0 → 2`, `1 → 2`, `1 → 3`, `2 → 3`. -/
def dg : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4))

instance : DecidableRel dg.Adj := fun i j =>
  inferInstanceAs (Decidable ((i, j) ∈ ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)] :
    List (Fin 4 × Fin 4))))

/-- Two arc-disjoint, internally disjoint `0`–`3` paths in `dg`. -/
def dgP : Fin 2 → List (Fin 4)
  | 0 => [0, 1, 3]
  | 1 => [0, 2, 3]

theorem dgP_isDipath : ∀ i, dg.IsDipath 0 3 (dgP i) := by decide

theorem dgP_arcDisjoint : Digraph.ArcDisjoint dgP := by
  intro i j
  revert i j
  decide

theorem dgP_internallyDisjoint : Digraph.InternallyDisjoint 0 3 dgP := by
  intro i j
  revert i j
  decide

example : (dg.outArcs {0}).card = 2 := by decide

/-- Every `0`–`3` arc cut of `dg` has at least two arcs (Menger, from `dgP`). -/
example : ∀ C : Finset (Fin 4 × Fin 4), dg.IsArcCut 0 3 C → 2 ≤ C.card :=
  (exists_arcDisjoint_iff_forall_isArcCut dg 0 3 2).mp ⟨dgP, dgP_isDipath, dgP_arcDisjoint⟩

example : ¬ ∃ P : Fin 3 → List (Fin 4),
    (∀ i, dg.IsDipath 0 3 (P i)) ∧ Digraph.ArcDisjoint P := by
  rw [exists_arcDisjoint_iff_forall_isArcCut]
  intro h
  have := h _ (dg.isArcCut_outArcs (S := {0}) (by decide) (by decide))
  revert this
  decide

example : ¬ ∃ P : Fin 3 → List (Fin 4), (∀ i, dg.IsDipath 0 3 (P i)) ∧
    Digraph.InternallyDisjoint 0 3 P := by
  rw [exists_internallyDisjoint_iff_forall_isVertexCut]
  intro h
  have := h {1, 2} (Digraph.isVertexCut_of_forall_adj (S := {0}) (by decide) (by decide)
    (by decide) (by decide) (by decide))
  simp at this

/-- Directed `A`–`B` Menger with overlap `1 ∈ A ∩ B` (`A = {0, 1}`, `B = {1, 3}`): two paths `[1]`
and `[0, 2, 3]`, separated by `{1, 2}` (or `{0, 1}`), refuting three vertex-disjoint paths. -/
def dgABP : Fin 2 → List (Fin 4)
  | 0 => [1]
  | 1 => [0, 2, 3]

example : ∀ Y : Finset (Fin 4),
    dg.IsSeparator ↑({0, 1} : Finset (Fin 4)) ↑({1, 3} : Finset (Fin 4)) ↑Y → 2 ≤ Y.card :=
  (exists_vertexDisjoint_iff_forall_isSeparator dg
    ↑({0, 1} : Finset (Fin 4)) ↑({1, 3} : Finset (Fin 4)) 2).mp
    ⟨dgABP, fun i => by revert i; decide,
      fun i j hij x h1 h2 => by revert i j hij x h1 h2; decide⟩

example : ¬ ∃ P : Fin 3 → List (Fin 4),
    (∀ i, ∃ a ∈ (↑({0, 1} : Finset (Fin 4)) : Set (Fin 4)),
      ∃ b ∈ (↑({1, 3} : Finset (Fin 4)) : Set (Fin 4)), dg.IsDipath a b (P i)) ∧
    Pairwise fun i j => (P i).Disjoint (P j) := by
  rw [exists_vertexDisjoint_iff_forall_isSeparator]
  intro h
  have hsep : dg.IsSeparator ↑({0, 1} : Finset (Fin 4)) ↑({1, 3} : Finset (Fin 4))
      ↑({0, 1} : Finset (Fin 4)) :=
    Digraph.isSeparator_of_subset_left Set.Subset.rfl
  have := h {0, 1} hsep
  revert this
  decide

/-! ### 3. Global `k`-connectivity edge cases -/

/-- `K₃` is `2`-vertex-connected (via adjacent-vertex injective paths) and not `3`-connected. -/
def k3Paths {u v : Fin 3} (huv : u ≠ v) : Fin 2 → (⊤ : SimpleGraph (Fin 3)).Walk u v
  | 0 => .cons huv .nil
  | 1 =>
    let w : Fin 3 := ⟨3 - u.1 - v.1, by omega⟩
    have huw : u ≠ w := by refine Fin.ne_of_val_ne ?_; revert u v huv; decide
    have hwv : w ≠ v := by refine Fin.ne_of_val_ne ?_; revert u v huv; decide
    .cons (v := w) huw (.cons hwv .nil)

theorem k3_isVertexConnected : (⊤ : SimpleGraph (Fin 3)).IsVertexConnected 2 := by
  rw [isVertexConnected_iff_of_nontrivial]
  intro u v huv
  refine ⟨k3Paths huv, ?_, fun i => Walk.IsPath.mk' ?_, fun i j hij x hxi hxj => ?_⟩
  · intro i j hij
    revert u v huv i j hij
    decide
  · revert u v huv i
    decide
  · revert u v huv i j hij x hxi hxj
    decide

example : ¬ (⊤ : SimpleGraph (Fin 3)).IsVertexConnected 3 := by
  intro h
  have := h.card_gt
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  exact absurd this (by decide)

/-- `K₂` is `1`-vertex-connected, NOT `2`-vertex-connected, and NOT `2`-edge-connected. -/
example : (⊤ : SimpleGraph (Fin 2)).IsVertexConnected 1 := by
  rw [isVertexConnected_one]
  exact ⟨inferInstance, SimpleGraph.connected_top⟩

example : ¬ (⊤ : SimpleGraph (Fin 2)).IsVertexConnected 2 := by
  intro h
  have := h.card_gt
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  exact absurd this (by decide)

example : ¬ ∃ W : Fin 2 → (⊤ : SimpleGraph (Fin 2)).Walk 0 1,
    Function.Injective W ∧ (∀ i, (W i).IsPath) ∧ SimpleGraph.InternallyDisjoint W := by
  intro h
  have hconn : (⊤ : SimpleGraph (Fin 2)).IsVertexConnected 2 :=
    (isVertexConnected_iff_of_nontrivial (⊤ : SimpleGraph (Fin 2)) 2).mpr fun u v huv => by
      rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;>
          rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
      · exact absurd rfl huv
      · exact h
      · obtain ⟨W, hinj, hW, hdisj⟩ := h
        exact ⟨fun i => (W i).reverse, fun i j heq => hinj (Walk.reverse_injective heq),
          fun i => (hW i).reverse, fun i j hij x hxi hxj => by
            rw [Walk.support_reverse, List.mem_reverse] at hxi hxj
            exact (hdisj hij x hxi hxj).symm⟩
      · exact absurd rfl huv
  have := hconn.card_gt
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  exact absurd this (by decide)

example : ¬ (⊤ : SimpleGraph (Fin 2)).IsEdgeConnected 2 := by
  intro h
  have h1 := (h 0 1) (s := {s(0, 1)}) (by simp)
  obtain ⟨w⟩ := h1
  cases w
  · rename_i v h' _
    rw [deleteEdges_adj, top_adj, Set.mem_singleton_iff] at h'
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact absurd rfl h'.1
    · exact h'.2 rfl

/-- `K₁` is `0`-vertex-connected, but NOT `1`-vertex-connected. -/
example : (⊤ : SimpleGraph (Fin 1)).IsVertexConnected 0 :=
  isVertexConnected_zero.mpr inferInstance

example : ¬ (⊤ : SimpleGraph (Fin 1)).IsVertexConnected 1 := by
  rw [isVertexConnected_one]
  intro ⟨h, _⟩
  exact not_nontrivial (Fin 1) h

/-- Three explicit internally disjoint (and edge-disjoint) `u`–`v` paths for any `u ≠ v : Fin 8`
in the 3-cube, handling `1`-, `2`-, and `3`-bit differences uniformly. -/
private def bitList (u v : Fin 8) : List ℕ :=
  ([1, 2, 4] : List ℕ).filter fun b => decide (u.val &&& b ≠ v.val &&& b)

private def cubePathFromBits (u : Fin 8) : List ℕ → List (Fin 8)
  | [] => [u]
  | b :: bs =>
    let nxt : Fin 8 := if h : u.val ^^^ b < 8 then ⟨u.val ^^^ b, h⟩ else u
    u :: cubePathFromBits nxt bs

private def cubeBranch (u v : Fin 8) (i : Fin 3) : List (Fin 8) :=
  let diff := bitList u v
  let same := ([1, 2, 4] : List ℕ).filter fun b => decide (u.val &&& b = v.val &&& b)
  match diff, same with
  | [a], [b, c] =>
    match i with
    | 0 => cubePathFromBits u [a]
    | 1 => cubePathFromBits u [b, a, b]
    | 2 => cubePathFromBits u [c, a, c]
  | [a, b], [c] =>
    match i with
    | 0 => cubePathFromBits u [a, b]
    | 1 => cubePathFromBits u [b, a]
    | 2 => cubePathFromBits u [c, a, b, c]
  | [a, b, c], [] =>
    match i with
    | 0 => cubePathFromBits u [a, b, c]
    | 1 => cubePathFromBits u [b, c, a]
    | 2 => cubePathFromBits u [c, a, b]
  | _, _ => []

private theorem cubeBranch_spec (u v : Fin 8) (huv : u ≠ v) (i : Fin 3) :
    (cubeBranch u v i).Nodup ∧ (cubeBranch u v i).head? = some u ∧
      (cubeBranch u v i).getLast? = some v ∧ (cubeBranch u v i).IsChain cube.Adj := by
  revert u v huv i
  decide

private theorem cubeBranch_internallyDisjoint (u v : Fin 8) (huv : u ≠ v) :
    ∀ i j : Fin 3, i ≠ j → ∀ x ∈ cubeBranch u v i, ∀ _ : x ∈ cubeBranch u v j,
      x = u ∨ x = v := by
  revert u v huv
  decide

private theorem cubeBranch_inj (u v : Fin 8) (huv : u ≠ v) :
    ∀ i j : Fin 3, cubeBranch u v i = cubeBranch u v j → i = j := by
  revert u v huv
  decide

private noncomputable def cubePaths {u v : Fin 8} (huv : u ≠ v) (i : Fin 3) : cube.Walk u v :=
  let h := cubeBranch_spec u v huv i
  have hne : cubeBranch u v i ≠ [] := fun he => by
    have := h.2.1; rw [he] at this; simp at this
  have hhd : (cubeBranch u v i).head hne = u := by
    have := h.2.1; rwa [List.head?_eq_some_head hne, Option.some.injEq] at this
  have hlt : (cubeBranch u v i).getLast hne = v := by
    have := h.2.2.1; rwa [List.getLast?_eq_some_getLast hne, Option.some.injEq] at this
  (Walk.ofSupport (cubeBranch u v i) hne h.2.2.2).copy hhd hlt

/-- The 3-cube is `3`-vertex-connected (and NOT `4`-vertex-connected). -/
theorem cube_isVertexConnected : cube.IsVertexConnected 3 := by
  rw [isVertexConnected_iff_of_nontrivial]
  intro u v huv
  refine ⟨cubePaths huv, fun i j hij => ?_, fun i => ?_, fun i j hij x hxi hxj => ?_⟩
  · have hsup := congrArg Walk.support hij
    simp only [cubePaths, Walk.support_copy, Walk.support_ofSupport] at hsup
    exact cubeBranch_inj u v huv i j hsup
  · simp only [cubePaths, Walk.isPath_copy]
    exact Walk.IsPath.mk' (by rw [Walk.support_ofSupport]; exact (cubeBranch_spec u v huv i).1)
  · simp only [cubePaths, Walk.support_copy, Walk.support_ofSupport] at hxi hxj
    exact cubeBranch_internallyDisjoint u v huv i j hij x hxi hxj

example : ¬ cube.IsVertexConnected 4 := by
  rw [isVertexConnected_iff_forall_isVertexSeparator]
  rintro ⟨-, hsep⟩
  have h := hsep (by decide : (0 : Fin 8) ≠ 7) {1, 2, 4} cube_sep
  revert h
  decide

/-- The `Finset`-of-paths global Menger characterization applied to `cube`. -/
example : ∀ ⦃u v : Fin 8⦄, u ≠ v → ∃ P : Finset (cube.Walk u v), P.card = 3 ∧
    (∀ w ∈ P, w.IsPath) ∧ (P : Set (cube.Walk u v)).Pairwise
      (fun w₁ w₂ => ∀ x ∈ w₁.support, x ∈ w₂.support → x = u ∨ x = v) :=
  ((isVertexConnected_iff_forall_exists_finset cube 3).mp cube_isVertexConnected).2

/-- The 3-cube is `3`-edge-connected, derived from `cube_isVertexConnected` via
Proposition 1.4.2. -/
theorem cube_isEdgeConnected : cube.IsEdgeConnected 3 :=
  isEdgeConnected_of_isVertexConnected cube_isVertexConnected

/-! ### 4. Integral-capacity path packing -/

/-- A 3-vertex network with capacities `0 → 1 (2)`, `1 → 2 (3)`, `0 → 2 (1)`: max `3` paths. -/
def capNet : Network (Fin 3) where
  cap
    | 0, 1 => 2
    | 1, 2 => 3
    | 0, 2 => 1
    | _, _ => 0
  s := 0
  t := 2

def capP : Fin 3 → List (Fin 3)
  | 0 => [0, 1, 2]
  | 1 => [0, 1, 2]
  | 2 => [0, 2]

example : ∀ S : Finset (Fin 3), capNet.IsCut S → 3 ≤ capNet.cutCapacity S :=
  (exists_arcCap_iff_forall_isCut capNet 3).mp ⟨capP, by decide, by decide⟩

example : capNet.cutCapacity {0} = 3 := by decide

/-! ### 5. Directed multidigraph arc-disjoint Menger (with parallel arcs) -/

section Multidigraph

open Cslib

/-- Source map for a 3-vertex, 5-arc multidigraph with two parallel `0 → 1` arcs (`0`, `1`),
two parallel `1 → 2` arcs (`2`, `3`), and one `0 → 2` arc (`4`). -/
def mdSrc : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 0

def mdTgt : Fin 5 → Fin 3
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2

def mdQ : Fin 3 → List (Fin 5)
  | 0 => [0, 2]
  | 1 => [1, 3]
  | 2 => [4]

theorem mdQ_isDipath : ∀ i, Multidigraph.IsDipath mdSrc mdTgt 0 2 (mdQ i) := by decide

theorem mdQ_disjoint : Pairwise fun i j => (mdQ i).Disjoint (mdQ j) := by
  intro i j hij x h1 h2
  revert i j hij x h1 h2
  decide

example : ∀ C : Finset (Fin 5), Multidigraph.IsArcCut mdSrc mdTgt 0 2 C → 3 ≤ C.card :=
  (exists_multidigraph_arcDisjoint_iff_forall_isArcCut mdSrc mdTgt 0 2 3).mp
    ⟨mdQ, mdQ_isDipath, mdQ_disjoint⟩

example : ¬ ∃ Q : Fin 4 → List (Fin 5),
    (∀ i, Multidigraph.IsDipath mdSrc mdTgt 0 2 (Q i)) ∧
    Pairwise fun i j => (Q i).Disjoint (Q j) := by
  rw [exists_multidigraph_arcDisjoint_iff_forall_isArcCut]
  intro h
  have := h _ (Multidigraph.isArcCut_outArcs mdSrc mdTgt (S := {0}) (by decide) (by decide))
  revert this
  decide

example : ∃ S : Finset (Fin 3), (0 : Fin 3) ∈ S ∧ (2 : Fin 3) ∉ S ∧
    (Multidigraph.outArcs mdSrc mdTgt S).card = 3 ∧
    ∃ Q : Fin 3 → List (Fin 5),
      (∀ i, Multidigraph.IsDipath mdSrc mdTgt 0 2 (Q i)) ∧
      Pairwise fun i j => (Q i).Disjoint (Q j) := by
  obtain ⟨S, hs, ht, Q, hQ, hdisj⟩ :=
    exists_multidigraph_arcDisjoint_eq_outArcs mdSrc mdTgt (s := (0 : Fin 3)) (t := 2) (by decide)
  have hle₁ : (Multidigraph.outArcs mdSrc mdTgt S).card ≤
      (Multidigraph.outArcs mdSrc mdTgt {0}).card :=
    Multidigraph.card_le_card_of_disjoint_of_isArcCut mdSrc mdTgt hQ hdisj
      (Multidigraph.isArcCut_outArcs mdSrc mdTgt (by decide) (by decide))
  have hcard0 : (Multidigraph.outArcs mdSrc mdTgt {0}).card = 3 := by decide
  have hle₂ : 3 ≤ (Multidigraph.outArcs mdSrc mdTgt S).card :=
    Multidigraph.card_le_card_of_disjoint_of_isArcCut mdSrc mdTgt mdQ_isDipath mdQ_disjoint
      (Multidigraph.isArcCut_outArcs mdSrc mdTgt hs ht)
  have hcard : (Multidigraph.outArcs mdSrc mdTgt S).card = 3 := by omega
  refine ⟨S, hs, ht, hcard, fun i => Q (Fin.cast hcard.symm i), fun i => hQ _,
    fun i j hij => hdisj (fun heq => hij (Fin.cast_injective _ heq))⟩

end Multidigraph

end CslibFrontierTests.Menger
