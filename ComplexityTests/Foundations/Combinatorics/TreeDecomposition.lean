/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Bounds
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-! # Tree decompositions and treewidth on small graphs

A concrete width-one rooted decomposition of the path on four vertices, checked by `decide`, and
the resulting treewidth; parent and bag data that violate connectivity and so form no rooted
decomposition; and the closed forms for complete graphs, cycles and edgeless graphs, together with
the characterization of forests by treewidth at most one. The empty vertex type has treewidth `0`,
and extended treewidth is `⊤` on the edgeless graph on `ℕ`.
-/

public section

namespace Cslib.Tests.TreeDecomposition

open SimpleGraph

/-- The path `0 - 1 - 2 - 3` with bags `{0, 1}`, `{1, 2}`, `{2, 3}` along the node path
`0 - 1 - 2`. Every field is checked by `decide`. -/
def pathDecomposition : (pathGraph 4).RootedTreeDecomposition 2 where
  parent := ![0, 0, 1]
  parent_zero := by decide
  parent_lt := by decide
  bag := ![{0, 1}, {1, 2}, {2, 3}]
  exists_mem_bag := by decide
  exists_adj_mem_bag := by decide
  top_unique := by decide

example : pathDecomposition.width = 1 :=
  le_antisymm (pathDecomposition.width_le_iff.2 (by decide)) (by
    have h := pathDecomposition.card_bag_le 0
    have h2 : (pathDecomposition.bag 0).card = 2 := by decide
    omega)

/-- The path on four vertices has treewidth one. -/
example : (pathGraph 4).treewidth = 1 := by
  refine le_antisymm (treewidth_le_iff_exists_rooted.2
    ⟨2, pathDecomposition, pathDecomposition.width_le_iff.2 (by decide)⟩) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, treewidth_eq_zero_iff]
  intro h
  have h01 : (pathGraph 4).Adj 0 1 := by decide
  rw [h] at h01
  exact h01

/-- Acyclicity of the path follows from its width-one decomposition. -/
example : (pathGraph 4).IsAcyclic :=
  treewidth_le_one_iff.1 (treewidth_le_iff_exists_rooted.2
    ⟨2, pathDecomposition, pathDecomposition.width_le_iff.2 (by decide)⟩)

/-- Vertex `0` occurs at nodes `0` and `2` but not at node `1` between them, so this data violates
connectivity and is not a rooted decomposition. -/
example : ¬∃ R : (⊥ : SimpleGraph (Fin 2)).RootedTreeDecomposition 2,
    R.parent = ![0, 0, 1] ∧ R.bag = ![{0}, {1}, {0}] := by
  rintro ⟨R, hp, hb⟩
  have h := R.top_unique 0 0 2
  rw [hp, hb] at h
  exact absurd (h (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- The complete graph on four vertices has treewidth three. -/
example : (⊤ : SimpleGraph (Fin 4)).treewidth = 3 := by
  rw [treewidth_top, Fintype.card_fin]

/-- The five-cycle has treewidth two, so it is not a forest. -/
example : (cycleGraph 5).treewidth = 2 := treewidth_cycleGraph 2

example : ¬(cycleGraph 5).IsAcyclic := fun h => by
  have h1 := treewidth_le_one_iff.2 h
  rw [treewidth_cycleGraph 2] at h1
  omega

/-- The edgeless graph has treewidth zero. -/
example : (⊥ : SimpleGraph (Fin 3)).treewidth = 0 := treewidth_bot

/-- The empty vertex type has treewidth zero, not `-1`. -/
example : (⊥ : SimpleGraph (Fin 0)).treewidth = 0 := treewidth_bot

/-- Extended treewidth is `⊤` on every infinite vertex type, even for the edgeless graph: it
records only that no decomposition with finitely many nodes exists. -/
example : (⊥ : SimpleGraph ℕ).etreewidth = ⊤ := etreewidth_eq_top_iff.2 inferInstance

end Cslib.Tests.TreeDecomposition
