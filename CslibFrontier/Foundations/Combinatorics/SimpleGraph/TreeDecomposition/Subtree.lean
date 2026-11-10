/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Subtree.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted

/-!
# Subtrees of rooted tree decompositions

For a rooted tree decomposition `R : G.RootedTreeDecomposition n`, this file describes the
subtree below a node: its descendants, its children and the vertices in its bags. These are the
separation facts used by dynamic programming over tree decompositions. A bag separates the
vertices first introduced below each child from the rest of the graph, and different children
introduce disjoint sets of vertices.

## Main definitions

* `SimpleGraph.RootedTreeDecomposition.IsDescendant R j i`: climbing from `j` reaches `i`.
* `SimpleGraph.RootedTreeDecomposition.children R i`: the children of node `i`.
* `SimpleGraph.RootedTreeDecomposition.subtreeVerts R i`: the vertices in the bags of the subtree
  rooted at `i`.

## Main results

* `SimpleGraph.RootedTreeDecomposition.mem_bag_of_mem_subtreeVerts_of_mem_bag_parent`: a vertex
  below a child `c` that also lies in the parent's bag lies in the bag of `c`.
* `SimpleGraph.RootedTreeDecomposition.mem_subtreeVerts_of_adj`: a neighbour of a vertex below `c`
  that is not in the parent's bag also lies below `c`.
* `SimpleGraph.RootedTreeDecomposition.eq_of_mem_subtreeVerts_of_mem_children` and
  `SimpleGraph.RootedTreeDecomposition.exists_mem_children_of_mem_subtreeVerts`: the vertices
  below `i` that are not in its bag are partitioned among the children of `i`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 7.2][CyganEtAl2015]
-/

public section

namespace SimpleGraph.RootedTreeDecomposition

universe uV

variable {V : Type uV} {G : SimpleGraph V} {n : ℕ} (R : G.RootedTreeDecomposition n)

/-! ### Descendants -/

/-- `j` lies in the subtree rooted at `i`: climbing from `j` reaches `i`. -/
def IsDescendant (j i : Fin (n + 1)) : Prop :=
  ∃ a, R.parent^[a] j = i

theorem isDescendant_refl (i : Fin (n + 1)) : R.IsDescendant i i :=
  ⟨0, rfl⟩

theorem isDescendant_parent (i : Fin (n + 1)) : R.IsDescendant i (R.parent i) :=
  ⟨1, rfl⟩

variable {R}

theorem IsDescendant.trans {i j k : Fin (n + 1)} (hkj : R.IsDescendant k j)
    (hji : R.IsDescendant j i) : R.IsDescendant k i := by
  obtain ⟨a, rfl⟩ := hkj
  obtain ⟨b, rfl⟩ := hji
  exact ⟨b + a, Function.iterate_add_apply _ _ _ _⟩

theorem IsDescendant.le {i j : Fin (n + 1)} (h : R.IsDescendant j i) : i ≤ j := by
  obtain ⟨a, rfl⟩ := h
  exact R.parent_iterate_le a j

theorem IsDescendant.antisymm {i j : Fin (n + 1)} (hji : R.IsDescendant j i)
    (hij : R.IsDescendant i j) : i = j :=
  le_antisymm hji.le hij.le

/-- Two ancestors of a common node are comparable. -/
theorem IsDescendant.total {i j k : Fin (n + 1)} (hi : R.IsDescendant k i)
    (hj : R.IsDescendant k j) : R.IsDescendant i j ∨ R.IsDescendant j i := by
  obtain ⟨a, rfl⟩ := hi
  obtain ⟨b, rfl⟩ := hj
  rcases le_total a b with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hab
    exact .inl ⟨c, (Function.iterate_add_apply _ _ _ _).symm⟩
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hab
    exact .inr ⟨c, (Function.iterate_add_apply _ _ _ _).symm⟩

variable (R)

private theorem parent_iterate_val (j : Fin (n + 1)) (a : ℕ) :
    (R.parent^[a] j).val + a ≤ j.val ∨ R.parent^[a] j = 0 := by
  induction a with
  | zero => exact .inl le_rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : R.parent^[a] j = 0
    · exact .inr (by rw [hx, R.parent_zero])
    · have hlt := R.parent_lt _ hx
      rw [Fin.lt_def] at hlt
      rcases ih with ih | ih
      · exact .inl (by omega)
      · exact absurd ih hx

/-- Every node lies in the subtree of the root. -/
theorem isDescendant_zero (j : Fin (n + 1)) : R.IsDescendant j 0 := by
  refine ⟨j.val, ?_⟩
  rcases R.parent_iterate_val j j.val with h | h
  · exact Fin.ext (by simp only [Fin.val_zero]; omega)
  · exact h

/-! ### Children -/

/-- The children of node `i`: the nonroot nodes whose parent is `i`. -/
def children (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun c => c ≠ 0 ∧ R.parent c = i

variable {R}

theorem mem_children {i c : Fin (n + 1)} : c ∈ R.children i ↔ c ≠ 0 ∧ R.parent c = i := by
  simp [children]

theorem lt_of_mem_children {i c : Fin (n + 1)} (h : c ∈ R.children i) : i < c := by
  obtain ⟨hc, rfl⟩ := mem_children.1 h
  exact R.parent_lt c hc

theorem isDescendant_of_mem_children {i c : Fin (n + 1)} (h : c ∈ R.children i) :
    R.IsDescendant c i :=
  ⟨1, (mem_children.1 h).2⟩

/-- A strict descendant of `i` lies below some child of `i`. -/
theorem exists_mem_children_of_isDescendant {i j : Fin (n + 1)} (h : R.IsDescendant j i)
    (hne : j ≠ i) : ∃ c ∈ R.children i, R.IsDescendant j c := by
  obtain ⟨a, ha⟩ := h
  induction a with
  | zero => exact absurd ha hne
  | succ a ih =>
    rw [Function.iterate_succ_apply'] at ha
    by_cases hx : R.parent^[a] j = i
    · exact ih hx
    · refine ⟨R.parent^[a] j, mem_children.2 ⟨fun h0 => hx ?_, ha⟩, a, rfl⟩
      rw [← ha, h0, R.parent_zero]

private theorem eq_of_mem_children_of_isDescendant {i c c' : Fin (n + 1)}
    (hc : c ∈ R.children i) (hc' : c' ∈ R.children i) (h : R.IsDescendant c c') : c = c' := by
  by_contra hne
  obtain ⟨a, ha⟩ := h
  rcases a with _ | a
  · exact hne ha
  · rw [Function.iterate_succ_apply, (mem_children.1 hc).2] at ha
    have hle := R.parent_iterate_le a i
    rw [ha] at hle
    exact absurd (lt_of_mem_children hc') (not_lt.2 hle)

/-- A node lies below at most one child of a given node. -/
theorem eq_of_mem_children {i c c' j : Fin (n + 1)} (hc : c ∈ R.children i)
    (hc' : c' ∈ R.children i) (hj : R.IsDescendant j c) (hj' : R.IsDescendant j c') : c = c' := by
  rcases hj.total hj' with h | h
  · exact eq_of_mem_children_of_isDescendant hc hc' h
  · exact (eq_of_mem_children_of_isDescendant hc' hc h).symm

/-! ### Vertices of a subtree -/

variable (R)

open scoped Classical in
/-- The vertices in the bags of the subtree rooted at `i`. -/
noncomputable def subtreeVerts (i : Fin (n + 1)) : Finset V :=
  (Finset.univ.filter (R.IsDescendant · i)).biUnion R.bag

variable {R}

theorem mem_subtreeVerts {i : Fin (n + 1)} {v : V} :
    v ∈ R.subtreeVerts i ↔ ∃ j, R.IsDescendant j i ∧ v ∈ R.bag j := by
  classical
  simp [subtreeVerts]

variable (R)

theorem bag_subset_subtreeVerts (i : Fin (n + 1)) : R.bag i ⊆ R.subtreeVerts i :=
  fun _ hv => mem_subtreeVerts.2 ⟨i, R.isDescendant_refl i, hv⟩

/-- Every vertex lies in the subtree of the root. -/
theorem mem_subtreeVerts_zero (v : V) : v ∈ R.subtreeVerts 0 := by
  obtain ⟨i, hi⟩ := R.exists_mem_bag v
  exact mem_subtreeVerts.2 ⟨i, R.isDescendant_zero i, hi⟩

variable {R}

theorem subtreeVerts_mono {i j : Fin (n + 1)} (h : R.IsDescendant j i) :
    R.subtreeVerts j ⊆ R.subtreeVerts i := fun _ hv => by
  obtain ⟨d, hd, hv⟩ := mem_subtreeVerts.1 hv
  exact mem_subtreeVerts.2 ⟨d, hd.trans h, hv⟩

theorem isDescendant_top {v : V} {d : Fin (n + 1)} (hd : v ∈ R.bag d) :
    R.IsDescendant d (R.top v) :=
  R.exists_iterate_eq_top hd

/-- Every bag between a node containing `v` and the topmost node for `v` contains `v`. -/
theorem mem_bag_of_isDescendant {v : V} {c d : Fin (n + 1)} (hd : v ∈ R.bag d)
    (hdc : R.IsDescendant d c) (hc : R.IsDescendant c (R.top v)) : v ∈ R.bag c := by
  obtain ⟨a, rfl⟩ := hdc
  obtain ⟨b, hb⟩ := hc
  rw [← Function.iterate_add_apply] at hb
  exact R.mem_bag_parent_iterate hd hb (Nat.le_add_left a b)

/-- The parent's bag meets the subtree of `c` only inside the bag of `c`. -/
theorem mem_bag_of_mem_subtreeVerts_of_mem_bag_parent {v : V} {c : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∈ R.bag (R.parent c)) : v ∈ R.bag c := by
  by_cases hc : c = 0
  · subst hc
    rwa [R.parent_zero] at hp
  obtain ⟨d, hdc, hd⟩ := mem_subtreeVerts.1 hv
  rcases hdc.total (isDescendant_top hd) with h | h
  · exact mem_bag_of_isDescendant hd hdc h
  · exact absurd (R.parent_lt c hc) (not_lt.2 (h.le.trans (isDescendant_top hp).le))

/-- A vertex below `c` that is not in the parent's bag has its topmost node below `c`. -/
theorem isDescendant_top_of_notMem_bag_parent {v : V} {c : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∉ R.bag (R.parent c)) : R.IsDescendant (R.top v) c := by
  obtain ⟨d, hdc, hd⟩ := mem_subtreeVerts.1 hv
  rcases hdc.total (isDescendant_top hd) with ⟨a, ha⟩ | h
  · rcases a with _ | a
    · exact ⟨0, ha.symm⟩
    · rw [Function.iterate_succ_apply] at ha
      exact absurd (mem_bag_of_isDescendant hd (hdc.trans (R.isDescendant_parent c)) ⟨a, ha⟩) hp
  · exact h

/-- A vertex below `c` that is not in the parent's bag occurs only in bags below `c`. -/
theorem isDescendant_of_mem_bag_of_notMem_bag_parent {v : V} {c d : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts c) (hp : v ∉ R.bag (R.parent c)) (hd : v ∈ R.bag d) :
    R.IsDescendant d c :=
  (isDescendant_top hd).trans (isDescendant_top_of_notMem_bag_parent hv hp)

/-- The parent's bag separates the vertices introduced below `c` from the rest of the graph:
every neighbour of such a vertex also lies below `c`. -/
theorem mem_subtreeVerts_of_adj {u x : V} {c : Fin (n + 1)} (hu : u ∈ R.subtreeVerts c)
    (hp : u ∉ R.bag (R.parent c)) (hux : G.Adj u x) : x ∈ R.subtreeVerts c := by
  obtain ⟨d, hud, hxd⟩ := R.exists_adj_mem_bag hux
  exact mem_subtreeVerts.2 ⟨d, isDescendant_of_mem_bag_of_notMem_bag_parent hu hp hud, hxd⟩

theorem subtreeVerts_subset_of_mem_children {i c : Fin (n + 1)} (hc : c ∈ R.children i) :
    R.subtreeVerts c ⊆ R.subtreeVerts i :=
  subtreeVerts_mono (isDescendant_of_mem_children hc)

/-- Different children of `i` introduce disjoint sets of vertices outside the bag of `i`. -/
theorem eq_of_mem_subtreeVerts_of_mem_children {v : V} {i c c' : Fin (n + 1)}
    (hc : c ∈ R.children i) (hc' : c' ∈ R.children i) (hv : v ∈ R.subtreeVerts c)
    (hv' : v ∈ R.subtreeVerts c') (hvi : v ∉ R.bag i) : c = c' := by
  obtain ⟨d, -, hd⟩ := mem_subtreeVerts.1 hv
  have hpc : v ∉ R.bag (R.parent c) := by rwa [(mem_children.1 hc).2]
  have hpc' : v ∉ R.bag (R.parent c') := by rwa [(mem_children.1 hc').2]
  exact eq_of_mem_children hc hc' (isDescendant_of_mem_bag_of_notMem_bag_parent hv hpc hd)
    (isDescendant_of_mem_bag_of_notMem_bag_parent hv' hpc' hd)

/-- Every vertex below `i` that is not in the bag of `i` lies below some child of `i`. -/
theorem exists_mem_children_of_mem_subtreeVerts {v : V} {i : Fin (n + 1)}
    (hv : v ∈ R.subtreeVerts i) (hvi : v ∉ R.bag i) : ∃ c ∈ R.children i, v ∈ R.subtreeVerts c := by
  obtain ⟨d, hdi, hd⟩ := mem_subtreeVerts.1 hv
  have hne : d ≠ i := by
    rintro rfl
    exact hvi hd
  obtain ⟨c, hc, hdc⟩ := exists_mem_children_of_isDescendant hdi hne
  exact ⟨c, hc, mem_subtreeVerts.2 ⟨d, hdc, hd⟩⟩

end SimpleGraph.RootedTreeDecomposition
