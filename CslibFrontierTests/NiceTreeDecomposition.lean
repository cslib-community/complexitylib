/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Nice
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-! # Nice tree decompositions on small graphs

Kernel-checked tests (with no `native_decide`) exercising:

1. Concrete `SimpleGraph.NiceTree (Fin 3)` trees — valid constructions, `LocalValid` violations
   (duplicate introduce, missing forget, mismatched join bags), `CoversFinset`, `bag`,
   `subtreeVerts`, `size`, and `width`.
2. `SimpleGraph.RootedTreeDecomposition.toNiceTree`, `.prune`, `.toNiceTreePruned`, and `.toNice`
   on the path graph `P₄` and on a redundant 6-node decomposition, verifying
   `toNiceTreePruned_width_le`, `toNiceTreePruned_size_le`, and `(3 * width + 5) * (|V| + 1)`.
3. Clique covering (`exists_coversFinset_of_isClique`) on `K₃`.
-/

public section

namespace Cslib.Tests.NiceTreeDecomposition

open SimpleGraph

/-! ### 1. Concrete `NiceTree` validity and negative cases -/

/-- A valid bottom-up `NiceTree` over `Fin 3` covering edges `0 - 1` and `1 - 2` and ending at
`∅`. -/
def validPathNiceTree : NiceTree (Fin 3) :=
  .forget 1 (.forget 2 (.introduce 2 (.forget 0 (.introduce 1 (.introduce 0 .leaf)))))

example : validPathNiceTree.LocalValid := by decide
example : validPathNiceTree.bag = ∅ := by decide
example : validPathNiceTree.subtreeVerts = {0, 1, 2} := by decide
example : validPathNiceTree.width = 1 := by decide
example : validPathNiceTree.size = 7 := by decide

example : NiceTree.CoversFinset ({0, 1} : Finset (Fin 3)) validPathNiceTree := by
  simp only [validPathNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
    NiceTree.CoversFinset.eq_3, NiceTree.bag]
  decide

example : NiceTree.CoversFinset ({1, 2} : Finset (Fin 3)) validPathNiceTree := by
  simp only [validPathNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
    NiceTree.CoversFinset.eq_3, NiceTree.bag]
  decide

example : ¬NiceTree.CoversFinset ({0, 2} : Finset (Fin 3)) validPathNiceTree := by
  simp only [validPathNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
    NiceTree.CoversFinset.eq_3, NiceTree.bag]
  decide

/-- Negative `LocalValid` cases: duplicate introduce, forgetting an absent vertex, and joining
distinct bags are all rejected by `decide`. -/
example : ¬(NiceTree.introduce (0 : Fin 3) (.introduce 0 .leaf)).LocalValid := by decide
example : ¬(NiceTree.forget (0 : Fin 3) .leaf).LocalValid := by decide
example : ¬(NiceTree.join (NiceTree.introduce (0 : Fin 3) .leaf) .leaf).LocalValid := by decide

/-- `pathGraph 3` nice tree decomposition assembled directly from `validPathNiceTree`. -/
def path3Nice : (pathGraph 3).NiceTreeDecomposition where
  tree := validPathNiceTree
  localValid := by decide
  bag_root := by decide
  exists_mem_bag := by decide
  exists_adj_mem_bag := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      first
      | exact absurd huv (by decide)
      | (simp only [validPathNiceTree, NiceTree.CoversFinset.eq_1, NiceTree.CoversFinset.eq_2,
          NiceTree.CoversFinset.eq_3, NiceTree.bag]; decide)

example : path3Nice.width = 1 := by decide
example : path3Nice.size = 7 := by decide

/-! ### 2. `toNiceTree`, `prune`, `toNiceTreePruned`, and `toNice` on `P₄` -/

/-- Width-1 rooted tree decomposition of the 4-vertex path `0 - 1 - 2 - 3`. -/
def pathRooted : (pathGraph 4).RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- A bloated rooted decomposition of `P₄` with 6 nodes (duplicate bags `{0, 1}`, `{2, 3}`, and
an extra leaf `{1}`), used to check that pruning bounds size via `(3 * width + 5) * (|V| + 1)`. -/
def bloatedPathRooted : (pathGraph 4).RootedTreeDecomposition 5 where
  parent := ![0, 0, 1, 2, 2, 3]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {0, 1}, {1, 2}, {2, 3}, {1}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

/-- Certified width and size properties of `pathRooted.toNiceTreePruned`. -/
def pathNicePruned : (pathGraph 4).NiceTreeDecomposition :=
  pathRooted.toNiceTreePruned

example : pathNicePruned.tree.LocalValid := pathNicePruned.localValid
example : pathNicePruned.bag_root = pathNicePruned.bag_root := rfl
example : pathNicePruned.width ≤ 1 := by
  dsimp only [pathNicePruned]
  have h1 := RootedTreeDecomposition.toNiceTreePruned_width_le pathRooted
  have h2 : pathRooted.width = 1 := by
    refine le_antisymm (pathRooted.width_le_iff.mpr (by decide)) ?_
    have hcard := pathRooted.card_bag_le 0
    have h0 : (pathRooted.bag 0).card = 2 := by decide
    omega
  omega

example : pathNicePruned.size ≤ 40 := by
  dsimp only [pathNicePruned]
  have h1 := RootedTreeDecomposition.toNiceTreePruned_size_le pathRooted
  have h2 : pathRooted.width = 1 := by
    refine le_antisymm (pathRooted.width_le_iff.mpr (by decide)) ?_
    have hcard := pathRooted.card_bag_le 0
    have h0 : (pathRooted.bag 0).card = 2 := by decide
    omega
  have hc : Fintype.card (Fin 4) = 4 := by decide
  rw [h2, hc] at h1
  exact h1

/-- Pruning `bloatedPathRooted` reduces its size to at most `40` while keeping width `≤ 1`. -/
example :
    bloatedPathRooted.toNiceTreePruned.size ≤ 40 ∧
      bloatedPathRooted.toNiceTreePruned.width ≤ 1 ∧
      bloatedPathRooted.toNiceTreePruned.tree.bag = ∅ := by
  have hw : bloatedPathRooted.width = 1 := by
    refine le_antisymm (bloatedPathRooted.width_le_iff.mpr (by decide)) ?_
    have hcard := bloatedPathRooted.card_bag_le 0
    have h0 : (bloatedPathRooted.bag 0).card = 2 := by decide
    omega
  have hc : Fintype.card (Fin 4) = 4 := by decide
  have hs := RootedTreeDecomposition.toNiceTreePruned_size_le bloatedPathRooted
  rw [hw, hc] at hs
  have hwp := RootedTreeDecomposition.toNiceTreePruned_width_le bloatedPathRooted
  rw [hw] at hwp
  exact ⟨hs, hwp, bloatedPathRooted.toNiceTreePruned.bag_root⟩

/-- `toNice` preserves width and produces a valid nice decomposition. -/
example :
    pathRooted.toNice.width ≤ pathRooted.width ∧
      pathRooted.toNice.tree.LocalValid ∧
      pathRooted.toNice.tree.bag = ∅ :=
  ⟨RootedTreeDecomposition.toNice_width_le pathRooted,
   pathRooted.toNice.localValid, pathRooted.toNice.bag_root⟩

/-! ### 3. Clique covering in `NiceTreeDecomposition` -/

/-- A single-bag decomposition of `K₃` covers `{0, 1, 2}` in some bag of its nice decomposition. -/
def k3Rooted : (completeGraph (Fin 3)).RootedTreeDecomposition 0 where
  parent := ![0]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1, 2}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

example :
    NiceTree.CoversFinset (Finset.univ : Finset (Fin 3)) k3Rooted.toNiceTreePruned.tree :=
  k3Rooted.toNiceTreePruned.exists_coversFinset_of_isClique
    (K := Finset.univ) (fun _ _ _ _ huv => huv)

end Cslib.Tests.NiceTreeDecomposition
