/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Rooted.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.Acyclic
public import Complexity.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Sort

/-!
# Rooted tree decompositions

A `SimpleGraph.RootedTreeDecomposition G n` is a tree decomposition whose nodes are `Fin (n + 1)`
and whose tree is given by a parent array: `parent 0 = 0` and `parent i < i` for `i ≠ 0`, so the
root is `0` and every parent precedes its children. This is the input format of dynamic
programming over tree decompositions: processing the nodes in decreasing order handles every
child before its parent.

Instead of the connectivity condition, the structure asks that each vertex `v` have a unique
*topmost* node: a node whose bag contains `v` and which is the root or whose parent's bag does not
contain `v`. This condition is decidable for concrete data and is equivalent to connectivity
(`SimpleGraph.RootedTreeDecomposition.preconnected_bag` and
`SimpleGraph.RootedTreeDecomposition.ofPreconnected`).

Every finite tree decomposition can be rooted and renumbered into this form with the same bags
(`SimpleGraph.TreeDecomposition.exists_rooted`). As an application, every finite clique lies in a
single bag (`SimpleGraph.TreeDecomposition.exists_subset_bag_of_isClique`).

## Main definitions

* `SimpleGraph.RootedTreeDecomposition G n`: a tree decomposition given by a parent array on
  `Fin (n + 1)`.
* `SimpleGraph.RootedTreeDecomposition.top`: the topmost node whose bag contains a vertex.
* `SimpleGraph.RootedTreeDecomposition.toTreeDecomposition`: the underlying tree decomposition.

## Main results

* `SimpleGraph.TreeDecomposition.exists_rooted`: every finite tree decomposition is the
  renumbering of a rooted one with the same bags.
* `SimpleGraph.treewidth_le_iff_exists_rooted`: `G` has treewidth at most `k` if and only if it
  has a rooted decomposition of width at most `k`.
* `SimpleGraph.TreeDecomposition.exists_subset_bag_of_isClique`: every finite clique lies in some
  bag.
* `SimpleGraph.TreeDecomposition.card_le_width_add_one_of_isClique`: so a decomposition has width
  at least the size of any clique minus one.

## References

* [N. Robertson and P. D. Seymour, *Graph Minors. II. Algorithmic Aspects of
  Tree-Width*][RobertsonSeymour1986]
* [M. Cygan et al., *Parameterized Algorithms*, Section 7.2][CyganEtAl2015]
-/

public section

namespace SimpleGraph

universe uV uι

variable {V : Type uV} {ι : Type uι} {G : SimpleGraph V}

/-- A rooted tree decomposition of `G` on the nodes `Fin (n + 1)`, given by a parent array with
root `0` in which every parent precedes its children. Each vertex has a unique topmost node: a
node whose bag contains it and which is the root or whose parent's bag does not contain it. -/
structure RootedTreeDecomposition (G : SimpleGraph V) (n : ℕ) where
  /-- The parent of each node; the root `0` is its own parent. -/
  parent : Fin (n + 1) → Fin (n + 1)
  /-- The root is its own parent. -/
  parent_zero : parent 0 = 0
  /-- Parents precede their children. -/
  parent_lt (i : Fin (n + 1)) : i ≠ 0 → parent i < i
  /-- The bag of vertices at each node. -/
  bag : Fin (n + 1) → Finset V
  /-- Every vertex lies in some bag. -/
  exists_mem_bag (v : V) : ∃ i, v ∈ bag i
  /-- Both endpoints of every edge lie in a common bag. -/
  exists_adj_mem_bag ⦃u v : V⦄ : G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- Each vertex has at most one topmost node. -/
  top_unique (v : V) (i j : Fin (n + 1)) :
    v ∈ bag i → (i = 0 ∨ v ∉ bag (parent i)) →
    v ∈ bag j → (j = 0 ∨ v ∉ bag (parent j)) → i = j

namespace RootedTreeDecomposition

variable {n : ℕ} (R : G.RootedTreeDecomposition n)

/-- `i` is a topmost node for `v`: its bag contains `v`, and it is the root or its parent's bag
does not contain `v`. -/
def IsTop (v : V) (i : Fin (n + 1)) : Prop :=
  v ∈ R.bag i ∧ (i = 0 ∨ v ∉ R.bag (R.parent i))

theorem isTop_iff_mem {v : V} {i : Fin (n + 1)} :
    R.IsTop v i ↔ v ∈ R.bag i ∧ (i = 0 ∨ v ∉ R.bag (R.parent i)) :=
  Iff.rfl

theorem parent_le (i : Fin (n + 1)) : R.parent i ≤ i := by
  by_cases hi : i = 0
  · rw [hi, R.parent_zero]
  · exact (R.parent_lt i hi).le

theorem parent_iterate_le (a : ℕ) (i : Fin (n + 1)) : R.parent^[a] i ≤ i := by
  induction a generalizing i with
  | zero => exact le_rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (R.parent_le i)

theorem parent_iterate_antitone (i : Fin (n + 1)) {a b : ℕ} (hab : a ≤ b) :
    R.parent^[b] i ≤ R.parent^[a] i := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hab
  rw [Function.iterate_add_apply]
  exact R.parent_iterate_le c _

/-- Climbing from a node whose bag contains `v` reaches a topmost node for `v` through bags that
all contain `v`. -/
theorem exists_isTop_of_mem {v : V} {i : Fin (n + 1)} (hi : v ∈ R.bag i) :
    ∃ a, R.IsTop v (R.parent^[a] i) ∧ ∀ b ≤ a, v ∈ R.bag (R.parent^[b] i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases htop : i = 0 ∨ v ∉ R.bag (R.parent i)
    · exact ⟨0, ⟨hi, htop⟩, fun b hb => by rw [Nat.le_zero.1 hb]; exact hi⟩
    · push Not at htop
      obtain ⟨a, ha, hle⟩ := ih (R.parent i) (R.parent_lt i htop.1) htop.2
      refine ⟨a + 1, by rwa [Function.iterate_succ_apply], fun b hb => ?_⟩
      rcases b with _ | b
      · exact hi
      · rw [Function.iterate_succ_apply]
        exact hle b (by omega)

theorem isTop_unique {v : V} {i j : Fin (n + 1)} (hi : R.IsTop v i) (hj : R.IsTop v j) :
    i = j :=
  R.top_unique v i j hi.1 hi.2 hj.1 hj.2

theorem exists_isTop (v : V) : ∃ i, R.IsTop v i := by
  obtain ⟨i, hi⟩ := R.exists_mem_bag v
  obtain ⟨a, ha, -⟩ := R.exists_isTop_of_mem hi
  exact ⟨_, ha⟩

/-- The topmost node whose bag contains `v`. -/
noncomputable def top (v : V) : Fin (n + 1) := (R.exists_isTop v).choose

theorem isTop_top (v : V) : R.IsTop v (R.top v) := (R.exists_isTop v).choose_spec

theorem isTop_iff {v : V} {i : Fin (n + 1)} : R.IsTop v i ↔ i = R.top v :=
  ⟨fun h => R.isTop_unique h (R.isTop_top v), fun h => h ▸ R.isTop_top v⟩

theorem mem_bag_top (v : V) : v ∈ R.bag (R.top v) := (R.isTop_top v).1

theorem exists_iterate_eq_top {v : V} {s : Fin (n + 1)} (hs : v ∈ R.bag s) :
    ∃ a, R.parent^[a] s = R.top v := by
  obtain ⟨a, ha, -⟩ := R.exists_isTop_of_mem hs
  exact ⟨a, R.isTop_iff.1 ha⟩

theorem top_le_of_mem {v : V} {s : Fin (n + 1)} (hs : v ∈ R.bag s) : R.top v ≤ s := by
  obtain ⟨a, ha⟩ := R.exists_iterate_eq_top hs
  exact ha ▸ R.parent_iterate_le a s

/-- Climbing from a node whose bag contains `v`, every bag up to the topmost node for `v`
contains `v`. -/
theorem mem_bag_parent_iterate {v : V} {s : Fin (n + 1)} (hs : v ∈ R.bag s) {a : ℕ}
    (ha : R.parent^[a] s = R.top v) {b : ℕ} (hb : b ≤ a) :
    v ∈ R.bag (R.parent^[b] s) := by
  obtain ⟨a', ha', hle⟩ := R.exists_isTop_of_mem hs
  rw [R.isTop_iff] at ha'
  rcases le_or_gt b a' with hba' | hba'
  · exact hle b hba'
  · have h1 : R.parent^[b] s ≤ R.parent^[a'] s := R.parent_iterate_antitone s hba'.le
    have h2 : R.parent^[a] s ≤ R.parent^[b] s := R.parent_iterate_antitone s hb
    rw [ha'] at h1
    rw [ha] at h2
    rw [le_antisymm h1 h2]
    exact R.mem_bag_top v

/-- If `u` and `w` are adjacent and the topmost node for `w` is numbered no later than the topmost
node for `u`, then the bag at the topmost node for `u` contains `w`. -/
theorem mem_bag_top_of_adj {u w : V} (huw : G.Adj u w) (h : R.top w ≤ R.top u) :
    w ∈ R.bag (R.top u) := by
  obtain ⟨s, hus, hws⟩ := R.exists_adj_mem_bag huw
  obtain ⟨a, ha⟩ := R.exists_iterate_eq_top hus
  obtain ⟨b, hb⟩ := R.exists_iterate_eq_top hws
  rcases le_or_gt a b with hab | hab
  · rw [← ha]
    exact R.mem_bag_parent_iterate hws hb hab
  · have h1 : R.top u ≤ R.top w := by
      rw [← ha, ← hb]
      exact R.parent_iterate_antitone s hab.le
    rw [le_antisymm h1 h]
    exact R.mem_bag_top w

/-- Every finite clique lies in some bag of a rooted tree decomposition: the topmost node of the
clique vertex whose topmost node is numbered last. -/
theorem exists_subset_bag_of_isClique {K : Finset V} (hK : G.IsClique (K : Set V)) :
    ∃ i, K ⊆ R.bag i := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, Finset.empty_subset _⟩
  obtain ⟨u, huK, hu⟩ := K.exists_max_image R.top hne
  refine ⟨R.top u, fun w hwK => ?_⟩
  by_cases hwu : w = u
  · subst hwu
    exact R.mem_bag_top w
  exact R.mem_bag_top_of_adj (hK huK hwK (Ne.symm hwu)) (hu w hwK)

/-- The index tree of a rooted tree decomposition. -/
def tree : SimpleGraph (Fin (n + 1)) := parentTree R.parent

theorem tree_eq : R.tree = parentTree R.parent := by
  unfold tree
  rfl

theorem reachable_top {v : V} {i : Fin (n + 1)} (hi : v ∈ R.bag i) :
    (R.tree.induce {j | v ∈ R.bag j}).Reachable ⟨i, hi⟩ ⟨R.top v, R.mem_bag_top v⟩ := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases htop : i = 0 ∨ v ∉ R.bag (R.parent i)
    · have : i = R.top v := R.isTop_iff.1 ⟨hi, htop⟩
      subst this
      rfl
    · push Not at htop
      have hadj : (R.tree.induce {j | v ∈ R.bag j}).Adj ⟨i, hi⟩ ⟨R.parent i, htop.2⟩ := by
        change R.tree.Adj i (R.parent i)
        rw [tree_eq]
        exact parentTree_adj_self R.parent_lt htop.1
      exact hadj.reachable.trans (ih _ (R.parent_lt i htop.1) htop.2)

/-- The nodes whose bags contain a given vertex induce a connected subtree. -/
theorem preconnected_bag (v : V) : (R.tree.induce {j | v ∈ R.bag j}).Preconnected := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  exact (R.reachable_top hi).trans (R.reachable_top hj).symm

/-- The tree decomposition underlying a rooted tree decomposition. -/
def toTreeDecomposition : G.TreeDecomposition (Fin (n + 1)) where
  tree := R.tree
  isTree := R.tree_eq ▸ parentTree_isTree R.parent_lt
  bag := R.bag
  exists_mem_bag := R.exists_mem_bag
  exists_adj_mem_bag := R.exists_adj_mem_bag
  preconnected_bag := R.preconnected_bag

@[simp] theorem toTreeDecomposition_bag : R.toTreeDecomposition.bag = R.bag := by
  unfold toTreeDecomposition
  rfl

@[simp] theorem toTreeDecomposition_tree : R.toTreeDecomposition.tree = parentTree R.parent := by
  unfold toTreeDecomposition
  exact R.tree_eq

/-- Build a rooted tree decomposition from the connectivity condition of tree decompositions in
place of the uniqueness of topmost nodes. -/
def ofPreconnected (parent : Fin (n + 1) → Fin (n + 1)) (parent_zero : parent 0 = 0)
    (parent_lt : ∀ i, i ≠ 0 → parent i < i) (bag : Fin (n + 1) → Finset V)
    (exists_mem_bag : ∀ v, ∃ i, v ∈ bag i)
    (exists_adj_mem_bag : ∀ ⦃u v⦄, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
    (preconnected_bag : ∀ v, ((parentTree parent).induce {i | v ∈ bag i}).Preconnected) :
    G.RootedTreeDecomposition n where
  parent := parent
  parent_zero := parent_zero
  parent_lt := parent_lt
  bag := bag
  exists_mem_bag := exists_mem_bag
  exists_adj_mem_bag := exists_adj_mem_bag
  top_unique v _ _ hi hit hj hjt :=
    eq_of_preconnected_parentTree parent_zero parent_lt (preconnected_bag v) hi hit hj hjt

/-- The width of a rooted tree decomposition: the largest bag size minus one. -/
def width : ℕ := R.toTreeDecomposition.width

@[simp] theorem width_toTreeDecomposition : R.toTreeDecomposition.width = R.width := by
  unfold width
  rfl

theorem width_le_iff {k : ℕ} : R.width ≤ k ↔ ∀ i, (R.bag i).card ≤ k + 1 := by
  rw [← width_toTreeDecomposition, TreeDecomposition.width_le_iff, toTreeDecomposition_bag]

theorem card_bag_le (i : Fin (n + 1)) : (R.bag i).card ≤ R.width + 1 :=
  R.width_le_iff.1 le_rfl i

/-- In every nonempty finite vertex set `S` some vertex `u` has a small neighbourhood inside `S`:
`u` and its neighbours in `S` all lie in one bag. Take `u ∈ S` whose topmost node is numbered
last. -/
theorem exists_card_filter_adj_add_one_le [DecidableRel G.Adj] {S : Finset V}
    (hS : S.Nonempty) : ∃ u ∈ S, (S.filter (G.Adj u)).card + 1 ≤ R.width + 1 := by
  classical
  obtain ⟨u, huS, hu⟩ := S.exists_max_image R.top hS
  refine ⟨u, huS, ?_⟩
  have hsub : insert u (S.filter (G.Adj u)) ⊆ R.bag (R.top u) := by
    refine Finset.insert_subset (R.mem_bag_top u) fun w hw => ?_
    rw [Finset.mem_filter] at hw
    exact R.mem_bag_top_of_adj hw.2 (hu w hw.1)
  have hnot : u ∉ S.filter (G.Adj u) := fun h => G.loopless.irrefl u (Finset.mem_filter.1 h).2
  rw [← Finset.card_insert_of_notMem hnot]
  exact (Finset.card_le_card hsub).trans (R.card_bag_le _)

end RootedTreeDecomposition

/-! ### Rooting a tree decomposition -/

namespace TreeDecomposition

/-- Every tree decomposition with finitely many nodes can be rooted and renumbered: it is the
renumbering of a rooted tree decomposition with the same bags. -/
theorem exists_rooted [Finite ι] (D : G.TreeDecomposition ι) :
    ∃ n, ∃ R : G.RootedTreeDecomposition n, ∃ e : Fin (n + 1) ≃ ι,
      ∀ i, R.bag i = D.bag (e i) := by
  classical
  have := Fintype.ofFinite ι
  -- Root the index tree at some `r` and number the nodes by depth, breaking ties arbitrarily:
  -- parents then precede their children.
  have hne : Nonempty ι := D.isTree.connected.nonempty
  obtain ⟨r⟩ := id hne
  let par := D.isTree.parent r
  let depth : ι → ℕ := fun t => (D.isTree.pathTo r t).length
  let key : ι → ℕ ×ₗ Fin (Fintype.card ι) := fun t => toLex (depth t, Fintype.equivFin ι t)
  have hkey : Function.Injective key := fun a b h => by
    have := congrArg (fun x => (ofLex x).2) h
    exact (Fintype.equivFin ι).injective this
  let _ : LinearOrder ι := LinearOrder.lift' key hkey
  have hlt_iff : ∀ a b : ι, a < b ↔ key a < key b := fun _ _ => Iff.rfl
  have hpar : ∀ t, t ≠ r → par t < t := by
    intro t ht
    rw [hlt_iff, Prod.Lex.toLex_lt_toLex]
    left
    have := D.isTree.length_pathTo_parent r ht
    simp only [depth, par]
    omega
  have hcard : Fintype.card ι = Fintype.card ι - 1 + 1 := by
    have := Fintype.card_pos (α := ι)
    omega
  set n := Fintype.card ι - 1
  let e : Fin (n + 1) ≃o ι := monoEquivOfFin ι hcard
  have hr_le : ∀ t, r ≤ t := by
    intro t
    by_cases ht : t = r
    · rw [ht]
    · refine le_of_lt ?_
      rw [hlt_iff, Prod.Lex.toLex_lt_toLex]
      left
      have h1 := D.isTree.length_pathTo_parent r ht
      have h2 : depth r = 0 := by simp only [depth, D.isTree.pathTo_self, Walk.length_nil]
      simp only [depth] at h2 ⊢
      omega
  have he0 : e 0 = r := by
    have h1 : e.symm r ≤ 0 := by
      rw [← e.le_iff_le, e.apply_symm_apply]
      exact hr_le _
    have h2 : e.symm r = 0 := le_antisymm h1 (Fin.zero_le _)
    rw [← h2, e.apply_symm_apply]
  have he_iff : ∀ i, i = 0 ↔ e i = r := fun i =>
    ⟨fun h => h ▸ he0, fun h => e.injective (h.trans he0.symm)⟩
  let parent : Fin (n + 1) → Fin (n + 1) := fun i => e.symm (par (e i))
  have parent_zero : parent 0 = 0 := by
    simp only [parent, he0, par, D.isTree.parent_self]
    rw [← he0, e.symm_apply_apply]
  have parent_lt : ∀ i, i ≠ 0 → parent i < i := by
    intro i hi
    have := hpar (e i) (fun h => hi ((he_iff i).2 h))
    rw [← e.lt_iff_lt, e.apply_symm_apply]
    exact this
  refine ⟨n, RootedTreeDecomposition.ofPreconnected parent parent_zero parent_lt
    (fun i => D.bag (e i)) (fun v => ?_) (fun u v huv => ?_) (fun v => ?_), e.toEquiv,
    fun i => by unfold RootedTreeDecomposition.ofPreconnected; rfl⟩
  · obtain ⟨t, ht⟩ := D.exists_mem_bag v
    exact ⟨e.symm t, by simpa using ht⟩
  · obtain ⟨t, ht⟩ := D.exists_adj_mem_bag huv
    exact ⟨e.symm t, by simpa using ht⟩
  · -- Renumbering is an isomorphism from the index tree onto the parent-array tree.
    let f : D.tree.induce {t | v ∈ D.bag t} →g
        (parentTree parent).induce {i | v ∈ D.bag (e i)} :=
      { toFun := fun t => ⟨e.symm t, by
          change v ∈ D.bag (e (e.symm t))
          rw [e.apply_symm_apply]
          exact t.2⟩
        map_rel' := fun {a b} h => by
          change (parentTree parent).Adj (e.symm a) (e.symm b)
          have h' : D.tree.Adj a b := h
          rw [parentTree_adj parent_lt]
          rcases (D.isTree.adj_iff_parent r).1 h' with ⟨ha, hab⟩ | ⟨hb, hba⟩
          · left
            refine ⟨fun h0 => ha ?_, ?_⟩
            · rw [← e.apply_symm_apply (a : ι), (he_iff _).1 h0]
            · simp only [parent, OrderIso.apply_symm_apply]
              exact congrArg e.symm hab
          · right
            refine ⟨fun h0 => hb ?_, ?_⟩
            · rw [← e.apply_symm_apply (b : ι), (he_iff _).1 h0]
            · simp only [parent, OrderIso.apply_symm_apply]
              exact congrArg e.symm hba }
    refine (D.preconnected_bag v).map f ?_
    rintro ⟨i, hi⟩
    exact ⟨⟨e i, hi⟩, Subtype.ext (e.symm_apply_apply i)⟩

/-- Every tree decomposition with finitely many nodes has a rooted one of the same width. -/
theorem exists_rooted_width_eq [Fintype ι] (D : G.TreeDecomposition ι) :
    ∃ n, ∃ R : G.RootedTreeDecomposition n, R.width = D.width := by
  obtain ⟨n, R, e, he⟩ := D.exists_rooted
  refine ⟨n, R, le_antisymm (R.width_le_iff.2 fun i => ?_) (D.width_le_iff.2 fun t => ?_)⟩
  · rw [he]
    exact D.card_bag_le _
  · have := R.card_bag_le (e.symm t)
    rwa [he, e.apply_symm_apply] at this

/-- Every finite clique lies in a single bag of a tree decomposition with finitely many nodes. -/
theorem exists_subset_bag_of_isClique [Finite ι] (D : G.TreeDecomposition ι) {K : Finset V}
    (hK : G.IsClique (K : Set V)) : ∃ t, K ⊆ D.bag t := by
  obtain ⟨n, R, e, he⟩ := D.exists_rooted
  obtain ⟨i, hi⟩ := R.exists_subset_bag_of_isClique hK
  exact ⟨e i, he i ▸ hi⟩

/-- In every nonempty finite vertex set `S` some vertex has at most `width` neighbours in `S`. -/
theorem exists_card_filter_adj_le_width [Fintype ι] [DecidableRel G.Adj]
    (D : G.TreeDecomposition ι) {S : Finset V} (hS : S.Nonempty) :
    ∃ u ∈ S, (S.filter (G.Adj u)).card ≤ D.width := by
  obtain ⟨n, R, hR⟩ := D.exists_rooted_width_eq
  obtain ⟨u, huS, hu⟩ := R.exists_card_filter_adj_add_one_le hS
  exact ⟨u, huS, by omega⟩

/-- A tree decomposition has width at least the size of any finite clique minus one. -/
theorem card_le_width_add_one_of_isClique [Fintype ι] (D : G.TreeDecomposition ι) {K : Finset V}
    (hK : G.IsClique (K : Set V)) : K.card ≤ D.width + 1 := by
  obtain ⟨t, ht⟩ := D.exists_subset_bag_of_isClique hK
  exact (Finset.card_le_card ht).trans (D.card_bag_le t)

end TreeDecomposition

/-- A graph on a finite vertex type has treewidth at most `k` if and only if it has a rooted tree
decomposition of width at most `k`. -/
theorem treewidth_le_iff_exists_rooted [Finite V] {k : ℕ} :
    G.treewidth ≤ k ↔ ∃ n, ∃ R : G.RootedTreeDecomposition n, R.width ≤ k := by
  refine ⟨fun h => ?_, fun ⟨_, R, hR⟩ => ?_⟩
  · obtain ⟨m, D, hD⟩ := treewidth_le_iff.1 h
    obtain ⟨n, R, hR⟩ := D.exists_rooted_width_eq
    exact ⟨n, R, hR.trans_le hD⟩
  · rw [← R.width_toTreeDecomposition] at hR
    exact (treewidth_le_width _).trans hR

end SimpleGraph
