/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.Menger

/-!
# Menger's Theorem Tests

Kernel-checked instances (no `native_decide`) of the four forms of Menger's theorem in
`CslibFrontier.Algorithms.Lean.MaxFlow.Menger`:

1. **3-cube, antipodal vertices `0` and `7`:** three explicit internally disjoint (hence
   edge-disjoint) paths give `IsEdgeReachable 3`; the three edges at `0` disconnect `0` from `7`,
   refuting `IsEdgeReachable 4`; the neighbourhood `{1, 2, 4}` is a separator, refuting four
   internally disjoint paths.
2. **A 4-vertex digraph:** two arc-disjoint and internally disjoint `0`-`3` paths, the cut
   `outArcs dg {0}` of size `2`, and the vertex cut `{1, 2}` refute three paths in either form.
-/

public section

namespace ComplexityTests.Menger

open Cslib.Algorithms.Lean.MaxFlow SimpleGraph

/-! ### 1. The 3-cube -/

/-- The 3-cube on `Fin 8`: `i ~ j` iff `i` and `j` differ in exactly one bit. -/
def cube : SimpleGraph (Fin 8) where
  Adj i j := i.val ^^^ j.val = 1 ∨ i.val ^^^ j.val = 2 ∨ i.val ^^^ j.val = 4
  symm := ⟨fun i j h => by rwa [Nat.xor_comm]⟩
  loopless := ⟨fun i h => by simp at h⟩

instance : DecidableRel cube.Adj := fun i j =>
  inferInstanceAs (Decidable (i.val ^^^ j.val = 1 ∨ i.val ^^^ j.val = 2 ∨ i.val ^^^ j.val = 4))

/-- Three internally disjoint `0`-`7` paths in the cube. -/
def cubeW : Fin 3 → cube.Walk 0 7
  | 0 => .cons (v := 1) (by decide) (.cons (v := 3) (by decide) (.cons (by decide) .nil))
  | 1 => .cons (v := 2) (by decide) (.cons (v := 6) (by decide) (.cons (by decide) .nil))
  | 2 => .cons (v := 4) (by decide) (.cons (v := 5) (by decide) (.cons (by decide) .nil))

example : (cubeW 0).support = [0, 1, 3, 7] := by decide

theorem cubeW_isPath : ∀ i, (cubeW i).IsPath := fun i =>
  Walk.IsPath.mk' (by revert i; decide)

theorem cubeW_internallyDisjoint : InternallyDisjoint 0 7 fun i => (cubeW i).support := by
  intro i j
  revert i j
  decide

theorem cubeW_edgeDisjoint : Pairwise fun i j => ∀ e ∈ (cubeW i).edges, e ∉ (cubeW j).edges := by
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

theorem cube_sep : IsVertexSeparator cube 0 7 {1, 2, 4} :=
  isVertexSeparator_of_forall_adj (S := {0}) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- Every `0`-`7` separator of the cube has at least three vertices (Menger, from `cubeW`). -/
example : ∀ T : Finset (Fin 8), IsVertexSeparator cube 0 7 T → 3 ≤ T.card :=
  (exists_internallyDisjoint_iff_forall_isVertexSeparator cube 0 7 3).mp
    ⟨cubeW, cubeW_isPath, cubeW_internallyDisjoint⟩

example : ¬ ∃ W : Fin 4 → cube.Walk 0 7, (∀ i, (W i).IsPath) ∧
    InternallyDisjoint 0 7 fun i => (W i).support := by
  rw [exists_internallyDisjoint_iff_forall_isVertexSeparator]
  intro h
  have := h _ cube_sep
  simp at this

/-- The matching-cut form of Menger, used as stated: it yields internally disjoint `0`-`7` paths
and a separator of the same size `m`, and weak duality against `cubeW` and `cube_sep` pins
`m = 3`. -/
example : ∃ (m : ℕ) (W : Fin m → cube.Walk 0 7), m = 3 ∧ (∀ i, (W i).IsPath) ∧
    (InternallyDisjoint 0 7 fun i => (W i).support) ∧
    ∃ T : Finset (Fin 8), IsVertexSeparator cube 0 7 T ∧ T.card = m := by
  obtain ⟨m, W, hW, hdisj, T, hT, hTm⟩ :=
    exists_internallyDisjoint_eq_isVertexSeparator cube (u := 0) (v := 7) (by decide) (by decide)
  refine ⟨m, W, ?_, hW, hdisj, T, hT, hTm⟩
  have h1 := card_le_card_of_internallyDisjoint_of_isVertexSeparator hW hdisj cube_sep
  have h2 := card_le_card_of_internallyDisjoint_of_isVertexSeparator cubeW_isPath
    cubeW_internallyDisjoint hT
  have h3 : ({1, 2, 4} : Finset (Fin 8)).card = 3 := by decide
  omega

/-! ### 2. A small digraph -/

/-- A small digraph: arcs `0 → 1`, `0 → 2`, `1 → 2`, `1 → 3`, `2 → 3`. -/
def dg : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4))

instance : DecidableRel dg.Adj := fun i j =>
  inferInstanceAs (Decidable ((i, j) ∈ ([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)] :
    List (Fin 4 × Fin 4))))

/-- Two arc-disjoint, internally disjoint `0`-`3` paths in `dg`. -/
def dgP : Fin 2 → List (Fin 4)
  | 0 => [0, 1, 3]
  | 1 => [0, 2, 3]

theorem dgP_isDipath : ∀ i, IsDipath dg 0 3 (dgP i) := by decide

theorem dgP_arcDisjoint : ArcDisjoint dgP := by
  intro i j
  revert i j
  decide

theorem dgP_internallyDisjoint : InternallyDisjoint 0 3 dgP := by
  intro i j
  revert i j
  decide

example : (outArcs dg {0}).card = 2 := by decide

/-- Every `0`-`3` arc cut of `dg` has at least two arcs (Menger, from `dgP`). -/
example : ∀ C : Finset (Fin 4 × Fin 4), IsArcCut dg 0 3 C → 2 ≤ C.card :=
  (exists_arcDisjoint_iff_forall_isArcCut dg 0 3 2).mp ⟨dgP, dgP_isDipath, dgP_arcDisjoint⟩

example : ¬ ∃ P : Fin 3 → List (Fin 4), (∀ i, IsDipath dg 0 3 (P i)) ∧ ArcDisjoint P := by
  rw [exists_arcDisjoint_iff_forall_isArcCut]
  intro h
  have := h _ (isArcCut_outArcs dg (S := {0}) (by decide) (by decide))
  revert this
  decide

example : ¬ ∃ P : Fin 3 → List (Fin 4), (∀ i, IsDipath dg 0 3 (P i)) ∧
    InternallyDisjoint 0 3 P := by
  rw [exists_internallyDisjoint_iff_forall_isVertexCut]
  intro h
  have := h {1, 2} (isVertexCut_of_forall_adj (S := {0}) (by decide) (by decide) (by decide)
    (by decide) (by decide))
  simp at this

end ComplexityTests.Menger
