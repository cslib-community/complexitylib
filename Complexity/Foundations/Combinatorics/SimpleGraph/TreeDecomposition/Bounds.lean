/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Bounds.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Basic treewidth bounds

Lower bounds on treewidth from cliques and degrees, and the graphs of treewidth `0` and at most
`1`.

* A clique lies in one bag, so `cliqueNum G ≤ treewidth G + 1`, and the complete graph on `n`
  vertices has treewidth `n - 1`.
* Some vertex has all its neighbours in its topmost bag, so `minDegree G ≤ treewidth G`.
* A graph has treewidth `0` exactly when it has no edges, and a cycle has treewidth `2`.
* A graph has treewidth at most `1` exactly when it is a forest (`SimpleGraph.IsAcyclic`). A tree
  rooted at `r` has the decomposition with bags `{t, parent t}`; conversely the vertex of a cycle
  whose topmost node is numbered last would need a bag with three vertices.

## Main definitions

* `SimpleGraph.IsTree.treeDecomposition`: the width-one decomposition of a tree.
* `SimpleGraph.RootedTreeDecomposition.ofBot`: the width-zero decomposition of the edgeless graph.

## Main results

* `SimpleGraph.cliqueNum_le_treewidth_add_one`, `SimpleGraph.treewidth_top`.
* `SimpleGraph.minDegree_le_treewidth`.
* `SimpleGraph.treewidth_eq_zero_iff`: treewidth `0` means edgeless.
* `SimpleGraph.treewidth_le_one_iff`: treewidth at most `1` means acyclic.
* `SimpleGraph.treewidth_cycleGraph`: the cycle on `n + 3` vertices has treewidth `2`.

## References

* [N. Robertson and P. D. Seymour, *Graph Minors. II. Algorithmic Aspects of
  Tree-Width*][RobertsonSeymour1986]
* [M. Cygan et al., *Parameterized Algorithms*, Section 7.2][CyganEtAl2015]
-/

public section

namespace SimpleGraph

universe uV

variable {V : Type uV} {G : SimpleGraph V}

open TreeDecomposition

/-- The clique number is at most the treewidth plus one. -/
theorem cliqueNum_le_treewidth_add_one [Finite V] : G.cliqueNum ≤ G.treewidth + 1 := by
  obtain ⟨K, hK⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨n, D, hD⟩ := exists_width_eq_treewidth (G := G)
  rw [← hK.card_eq, ← hD]
  exact D.card_le_width_add_one_of_isClique hK.isClique

/-- The complete graph on a finite vertex type `V` has treewidth `card V - 1`. -/
theorem treewidth_top [Fintype V] : (⊤ : SimpleGraph V).treewidth = Fintype.card V - 1 := by
  classical
  refine le_antisymm treewidth_le_card (le_treewidth_iff.2 fun n D => ?_)
  have := D.card_le_width_add_one_of_isClique (K := Finset.univ) (by simp)
  rw [Finset.card_univ] at this
  omega

/-- The minimum degree is at most the treewidth. -/
theorem minDegree_le_treewidth [Fintype V] [DecidableRel G.Adj] : G.minDegree ≤ G.treewidth := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp only [minDegree, Finset.univ_eq_empty, Finset.image_empty, Finset.min_empty,
      WithTop.untopD_top, zero_le]
  · obtain ⟨n, D, hD⟩ := exists_width_eq_treewidth (G := G)
    obtain ⟨u, -, hu⟩ := D.exists_card_filter_adj_le_width (S := Finset.univ) Finset.univ_nonempty
    rw [← hD]
    refine (G.minDegree_le_degree u).trans ?_
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    exact hu

/-! ### Trees and forests -/

/-- The width-one tree decomposition of a tree `G` rooted at `r`, indexed by `G` itself: the bag
at `t` is `{t, parent t}`. -/
noncomputable def IsTree.treeDecomposition [DecidableEq V] (hG : G.IsTree) (r : V) :
    G.TreeDecomposition V where
  tree := G
  isTree := hG
  bag t := {t, hG.parent r t}
  exists_mem_bag v := ⟨v, Finset.mem_insert_self _ _⟩
  exists_adj_mem_bag u v huv := by
    rcases (hG.adj_iff_parent r).1 huv with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨u, by simp [h]⟩
    · exact ⟨v, by simp [h]⟩
  preconnected_bag v := by
    -- Every node whose bag contains `v` is `v` or a child of `v`.
    have hreach : ∀ (t : V) (ht : v ∈ ({t, hG.parent r t} : Finset V)),
        (G.induce {t | v ∈ ({t, hG.parent r t} : Finset V)}).Reachable ⟨t, ht⟩
          ⟨v, by simp⟩ := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | hv
      · rfl
      · rw [Finset.mem_singleton] at hv
        by_cases htr : t = r
        · subst htr
          have hvt : v = t := hv.trans (hG.parent_self t)
          subst hvt
          rfl
        · have hadj := hG.adj_parent r htr
          rw [← hv] at hadj
          exact Adj.reachable (G := G.induce _) hadj
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact (hreach a ha).trans (hreach b hb).symm

theorem IsTree.width_treeDecomposition_le [Fintype V] [DecidableEq V] (hG : G.IsTree) (r : V) :
    (hG.treeDecomposition r).width ≤ 1 :=
  (hG.treeDecomposition r).width_le_iff.2 fun _ => by
    unfold IsTree.treeDecomposition
    exact Finset.card_insert_le _ _

/-- A finite tree has treewidth at most `1`. -/
theorem IsTree.treewidth_le_one [Finite V] (hG : G.IsTree) : G.treewidth ≤ 1 := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨r⟩ := hG.connected.nonempty
  exact (treewidth_le_width _).trans (hG.width_treeDecomposition_le r)

/-- A finite forest has treewidth at most `1`. -/
theorem IsAcyclic.treewidth_le_one [Finite V] (hG : G.IsAcyclic) : G.treewidth ≤ 1 := by
  have := Fintype.ofFinite V
  rcases isEmpty_or_nonempty V with hV | hV
  · exact treewidth_le_card.trans (by rw [Fintype.card_eq_zero]; omega)
  · obtain ⟨F, hGF, -, hF⟩ := (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      le_top hG
    exact (treewidth_mono hGF).trans hF.treewidth_le_one

/-- A graph on a finite vertex type has treewidth at most `1` if and only if it is a forest. -/
theorem treewidth_le_one_iff [Finite V] : G.treewidth ≤ 1 ↔ G.IsAcyclic := by
  classical
  refine ⟨fun h => ?_, IsAcyclic.treewidth_le_one⟩
  intro v c hc
  obtain ⟨n, D, hD⟩ := treewidth_le_iff.1 h
  -- The vertex of the cycle whose topmost node is numbered last has both cycle neighbours in its
  -- bag, so that bag has three vertices.
  obtain ⟨u, hu, hcard⟩ := D.exists_card_filter_adj_le_width (S := c.support.toFinset)
    ⟨v, List.mem_toFinset.2 c.start_mem_support⟩
  rw [List.mem_toFinset] at hu
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hu
  have hsub : c.toSubgraph.neighborSet u ⊆ ↑(c.support.toFinset.filter (G.Adj u)) := by
    intro w hw
    rw [Subgraph.mem_neighborSet] at hw
    rw [Finset.coe_filter, Set.mem_ofPred_eq, List.mem_toFinset, ← Walk.mem_verts_toSubgraph]
    exact ⟨hw.snd_mem, hw.adj_sub⟩
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [h2, Set.ncard_coe_finset] at this
  omega

/-! ### Cycles -/

private theorem cycleGraph_adj_iff_val {n : ℕ} {u v : Fin (n + 3)} :
    (cycleGraph (n + 3)).Adj u v ↔
      u.val = v.val + 1 ∨ v.val = u.val + 1 ∨ (u.val = 0 ∧ v.val = n + 2) ∨
        (v.val = 0 ∧ u.val = n + 2) := by
  have key : ∀ a b : Fin (n + 3),
      (a - b).val = 1 ↔ a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val = n + 2) := by
    intro a b
    rw [Fin.val_sub]
    have ha := a.isLt
    have hb := b.isLt
    rcases le_or_gt b.val a.val with hab | hab
    · have : n + 3 - b.val + a.val = (a.val - b.val) + (n + 3) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  rw [cycleGraph_adj', key, key]
  omega

/-- The bag `{0, i + 1, i + 2}` of the fan decomposition of the cycle. -/
private def cycleGraphBag (n : ℕ) (i : Fin (n + 1)) : Finset (Fin (n + 3)) :=
  {0, ⟨i.val + 1, by omega⟩, ⟨i.val + 2, by omega⟩}

private theorem mem_cycleGraphBag {n : ℕ} {i : Fin (n + 1)} {v : Fin (n + 3)} :
    v ∈ cycleGraphBag n i ↔ v.val = 0 ∨ v.val = i.val + 1 ∨ v.val = i.val + 2 := by
  simp only [cycleGraphBag, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]

/-- The fan decomposition of the cycle `0, 1, …, n + 2`: a path of nodes `0, …, n` with bags
`{0, i + 1, i + 2}`. -/
private def cycleGraphDecomposition (n : ℕ) : (cycleGraph (n + 3)).RootedTreeDecomposition n where
  parent i := ⟨i.val - 1, by omega⟩
  parent_zero := Fin.ext (by simp)
  parent_lt i hi := by
    have : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [Fin.lt_def]
    dsimp only
    omega
  bag := cycleGraphBag n
  exists_mem_bag v := by
    refine ⟨⟨min (v.val - 1) n, by omega⟩, ?_⟩
    rw [mem_cycleGraphBag]
    dsimp only
    omega
  exists_adj_mem_bag u v huv := by
    rw [cycleGraph_adj_iff_val] at huv
    rcases huv with h | h | h | h
    · refine ⟨⟨v.val - 1, by omega⟩, ?_, ?_⟩ <;>
      · rw [mem_cycleGraphBag]
        dsimp only
        omega
    · refine ⟨⟨u.val - 1, by omega⟩, ?_, ?_⟩ <;>
      · rw [mem_cycleGraphBag]
        dsimp only
        omega
    · refine ⟨⟨n, by omega⟩, ?_, ?_⟩ <;>
      · rw [mem_cycleGraphBag]
        dsimp only
        omega
    · refine ⟨⟨n, by omega⟩, ?_, ?_⟩ <;>
      · rw [mem_cycleGraphBag]
        dsimp only
        omega
  top_unique v i j hi hit hj hjt := by
    rw [mem_cycleGraphBag] at hi hj
    rw [mem_cycleGraphBag] at hit hjt
    rw [Fin.ext_iff] at hit hjt ⊢
    simp only [Fin.val_zero] at hit hjt
    omega

/-- A cycle has treewidth `2`: the fan decomposition has width `2`, and every vertex has degree
`2`. -/
theorem treewidth_cycleGraph (n : ℕ) : (cycleGraph (n + 3)).treewidth = 2 := by
  refine le_antisymm (treewidth_le_iff_exists_rooted.2 ⟨n, cycleGraphDecomposition n, ?_⟩) ?_
  · refine (RootedTreeDecomposition.width_le_iff _).2 fun i => ?_
    exact Finset.card_le_three
  · refine le_trans ?_ minDegree_le_treewidth
    exact le_minDegree_of_forall_le_degree _ _ fun v => (cycleGraph_degree_three_le).ge

/-! ### Edgeless graphs -/

/-- The edgeless graph on a finite vertex type has a decomposition of width zero: a star whose root
has an empty bag and whose leaves carry one vertex each. -/
noncomputable def RootedTreeDecomposition.ofBot [Fintype V] :
    (⊥ : SimpleGraph V).RootedTreeDecomposition (Fintype.card V) where
  parent _ := 0
  parent_zero := rfl
  parent_lt i hi := Fin.pos_iff_ne_zero.2 hi
  bag i := Finset.univ.filter fun v => (Fintype.equivFin V v).succ = i
  exists_mem_bag v := ⟨(Fintype.equivFin V v).succ, by simp⟩
  exists_adj_mem_bag u v h := absurd h (by simp)
  top_unique v i j hi _ hj _ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hi.symm.trans hj

theorem RootedTreeDecomposition.width_ofBot [Fintype V] :
    (RootedTreeDecomposition.ofBot (V := V)).width = 0 := by
  refine Nat.le_zero.1 ((RootedTreeDecomposition.width_le_iff _).2 fun i => ?_)
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  unfold RootedTreeDecomposition.ofBot at ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact (Fintype.equivFin V).injective (Fin.succ_injective _ (ha.trans hb.symm))

/-- The edgeless graph has treewidth `0`. -/
theorem treewidth_bot [Finite V] : (⊥ : SimpleGraph V).treewidth = 0 := by
  have := Fintype.ofFinite V
  refine Nat.le_zero.1 (treewidth_le_iff_exists_rooted.2 ⟨_, RootedTreeDecomposition.ofBot,
    RootedTreeDecomposition.width_ofBot.le⟩)

/-- A graph on a finite vertex type has treewidth `0` if and only if it has no edges. -/
theorem treewidth_eq_zero_iff [Finite V] : G.treewidth = 0 ↔ G = ⊥ := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ treewidth_bot⟩
  ext u v
  simp only [bot_adj, iff_false]
  intro huv
  obtain ⟨n, D, hD⟩ := exists_width_eq_treewidth (G := G)
  obtain ⟨t, hu, hv⟩ := D.exists_adj_mem_bag huv
  have h2 : ({u, v} : Finset V).card ≤ D.width + 1 :=
    (Finset.card_le_card (Finset.insert_subset_iff.2 ⟨hu, Finset.singleton_subset_iff.2 hv⟩)).trans
      (D.card_bag_le t)
  rw [Finset.card_pair huv.ne, hD, h] at h2
  omega

end SimpleGraph
