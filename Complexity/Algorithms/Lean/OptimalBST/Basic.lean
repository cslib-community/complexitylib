/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.SearchTree.Cost
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SplitIfs

/-!
# Optimal binary search trees: the interval recurrence

A binary search tree on the keys `i + 1, …, j` is a `BinaryTree ℕ` satisfying `IsBST i j`. For an
interval weight `w : ℕ → ℕ → β`, the cost `treeCost w i j t` charges `w i' j'` at every node whose
subtree holds the keys `i' + 1, …, j'`. With Knuth's weight
`knuthWeight p q i j = ∑_{i < k ≤ j} p k + ∑_{i ≤ g ≤ j} q g`, this is the weighted search cost
of Knuth's optimum-search-tree problem: each key `k` costs `p k · (depth of k + 1)`, and each gap
`g` costs `q g` times the number of keys compared by an unsuccessful search in that gap
(`treeCost_knuthWeight`, stated with the node-visit counts of `Cslib.DataStructure.SearchTree`).
Gap `g` holds the values strictly between keys `g` and `g + 1`. The expected cost `e[1, n]` of
CLRS counts the dummy leaf of each unsuccessful search as one more level, so it equals `treeCost`
plus `∑ q g`.

The interval recurrence `c(i, i) = 0`,
`c(i, j) = w(i, j) + min_{i < k ≤ j} (c(i, k - 1) + c(k, j))` is `optCost`. Its value is the least
cost of a tree on the keys `i + 1, …, j` (`isLeast_optCost`), attained by the tree `optTree` read
off the largest minimizing roots `optRoot`. The recurrence and its optimality hold for every weight;
no hypothesis on `w` is needed here.

## Main definitions

* `Cslib.Algorithms.Lean.OptimalBST.IsBST`: binary search trees on the keys `i + 1, …, j`.
* `Cslib.Algorithms.Lean.OptimalBST.treeCost`: the interval-weighted cost of a tree.
* `Cslib.Algorithms.Lean.OptimalBST.knuthWeight`: Knuth's weight from access and failure weights.
* `Cslib.Algorithms.Lean.OptimalBST.optCost`, `optRoot`, `optTree`: the optimal cost, the largest
  optimal root and the tree read off it.

## Main results

* `Cslib.Algorithms.Lean.OptimalBST.isBST_iff`: `IsBST` is the search-tree invariant of
  `Cslib.DataStructure.SearchTree` with key set `(i, j]`.
* `Cslib.Algorithms.Lean.OptimalBST.treeCost_knuthWeight`: Knuth's weight gives the weighted search
  cost.
* `Cslib.Algorithms.Lean.OptimalBST.optCost_le_treeCost`, `treeCost_optTree`,
  `isLeast_optCost`: the recurrence is the minimum cost over all trees, attained by `optTree`.

## References

* [D. E. Knuth, *Optimum binary search trees*][Knuth1971]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Section 15.5][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.OptimalBST

open Finset

/-- `IsBST i j t`: `t` is a binary search tree whose keys are exactly `i + 1, …, j`. -/
inductive IsBST : ℕ → ℕ → BinaryTree ℕ → Prop
  | nil (i : ℕ) : IsBST i i .nil
  | node {i j k : ℕ} {l r : BinaryTree ℕ} (hik : i < k) (hkj : k ≤ j) :
      IsBST i (k - 1) l → IsBST k j r → IsBST i j (.node k l r)

theorem IsBST.le {i j : ℕ} {t : BinaryTree ℕ} (h : IsBST i j t) : i ≤ j := by
  induction h <;> omega

open Cslib.DataStructure.SearchTree in
/-- `IsBST i j` is the search-tree invariant with key set `(i, j]`. -/
theorem isBST_iff {i j : ℕ} {t : BinaryTree ℕ} :
    IsBST i j t ↔ i ≤ j ∧ Ordered t ∧ elements t = Ioc i j := by
  constructor
  · intro h
    induction h with
    | nil i => exact ⟨le_rfl, trivial, by rw [elements, Ioc_self]⟩
    | @node i j k l r hik hkj _ _ ihl ihr =>
      obtain ⟨-, hol, hel⟩ := ihl
      obtain ⟨-, hor, her⟩ := ihr
      refine ⟨by omega, ⟨hol, hor, ?_, ?_⟩, ?_⟩
      · intro x hx
        rw [hel, mem_Ioc] at hx
        omega
      · intro x hx
        rw [her, mem_Ioc] at hx
        omega
      · ext x
        simp only [mem_elements_node, hel, her, mem_Ioc]
        omega
  · induction t generalizing i j with
    | nil =>
      rintro ⟨hij, -, he⟩
      have : j ≤ i := by
        by_contra hc
        have : j ∈ Ioc i j := mem_Ioc.2 ⟨by omega, le_rfl⟩
        rw [← he, elements] at this
        exact absurd this (notMem_empty j)
      obtain rfl : i = j := le_antisymm hij this
      exact .nil i
    | node a l r ihl ihr =>
      rintro ⟨hij, ⟨hol, hor, hla, hra⟩, he⟩
      have hmem : ∀ x, x ∈ elements (.node a l r) ↔ i < x ∧ x ≤ j := fun x => by
        rw [he, mem_Ioc]
      have ha := (hmem a).1 (mem_elements_node.2 (Or.inl rfl))
      have hel : elements l = Ioc i (a - 1) := by
        ext x
        rw [mem_Ioc]
        constructor
        · intro hx
          have h1 := hla x hx
          have h2 := (hmem x).1 (mem_elements_node.2 (Or.inr (Or.inl hx)))
          omega
        · intro hx
          have h2 := (hmem x).2 (by omega)
          rw [mem_elements_node] at h2
          rcases h2 with h2 | h2 | h2
          · omega
          · exact h2
          · have := hra x h2; omega
      have her : elements r = Ioc a j := by
        ext x
        rw [mem_Ioc]
        constructor
        · intro hx
          have h1 := hra x hx
          have h2 := (hmem x).1 (mem_elements_node.2 (Or.inr (Or.inr hx)))
          omega
        · intro hx
          have h2 := (hmem x).2 (by omega)
          rw [mem_elements_node] at h2
          rcases h2 with h2 | h2 | h2
          · omega
          · have := hla x h2; omega
          · exact h2
      exact .node ha.1 ha.2 (ihl ⟨by omega, hol, hel⟩) (ihr ⟨ha.2, hor, her⟩)

variable {β : Type*}

section Cost

variable [AddCommMonoid β]

/-- The interval-weighted cost of a tree on the keys `i + 1, …, j`: every node whose subtree holds
the keys `i' + 1, …, j'` contributes `w i' j'`. -/
@[expose] def treeCost (w : ℕ → ℕ → β) : ℕ → ℕ → BinaryTree ℕ → β
  | _, _, .nil => 0
  | i, j, .node k l r => w i j + treeCost w i (k - 1) l + treeCost w k j r

/-- Knuth's interval weight: the access weights `p k` of the keys `i < k ≤ j` and the failure
weights `q g` of the gaps `i ≤ g ≤ j`. -/
@[expose] def knuthWeight (p q : ℕ → β) (i j : ℕ) : β :=
  ∑ k ∈ Ioc i j, p k + ∑ g ∈ Icc i j, q g

open Cslib.DataStructure.SearchTree in
/-- **Knuth's weight gives the weighted search cost**: each key `k` is charged its access weight
once per node visited by a search for `k`, and each gap `g` its failure weight once per node
visited by an unsuccessful search between keys `g` and `g + 1`. -/
theorem treeCost_knuthWeight (p q : ℕ → β) {i j : ℕ} {t : BinaryTree ℕ} (h : IsBST i j t) :
    treeCost (knuthWeight p q) i j t =
      ∑ k ∈ Ioc i j, searchVisits k t • p k + ∑ g ∈ Icc i j, successorVisits g t • q g := by
  induction h with
  | nil i =>
    simp only [treeCost, searchVisits, successorVisits, zero_nsmul, sum_const_zero, add_zero]
  | @node i j k l r hik hkj hl hr ihl ihr =>
    obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ihl ⊢
    have hl' := hl.le
    simp only [Nat.add_sub_cancel] at hl'
    -- split the key range `(i, j]` at the root
    have hIoc : ∀ f : ℕ → β, ∑ x ∈ Ioc i j, f x =
        ∑ x ∈ Ioc i s, f x + f (s + 1) + ∑ x ∈ Ioc (s + 1) j, f x := by
      intro f
      rw [← sum_Ioc_consecutive f hl' (by omega : s ≤ j),
        ← sum_Ioc_consecutive f (by omega : s ≤ s + 1) hkj, Nat.Ioc_succ_singleton, sum_singleton,
        add_assoc]
    have hIcc : ∀ f : ℕ → β, ∑ x ∈ Icc i j, f x =
        ∑ x ∈ Icc i s, f x + ∑ x ∈ Icc (s + 1) j, f x := by
      intro f
      rw [← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc,
        sum_Ico_consecutive f (by omega : i ≤ s + 1) (by omega : s + 1 ≤ j + 1)]
    rw [hIoc, hIcc]
    have e1 : ∑ x ∈ Ioc i s, searchVisits x (.node (s + 1) l r) • p x =
        ∑ x ∈ Ioc i s, p x + ∑ x ∈ Ioc i s, searchVisits x l • p x := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x hx => ?_
      rw [mem_Ioc] at hx
      rw [searchVisits, ite_eq_left (by omega), add_nsmul, one_nsmul]
    have e2 : searchVisits (s + 1) (.node (s + 1) l r) • p (s + 1) = p (s + 1) := by
      rw [searchVisits, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), add_zero, one_nsmul]
    have e3 : ∑ x ∈ Ioc (s + 1) j, searchVisits x (.node (s + 1) l r) • p x =
        ∑ x ∈ Ioc (s + 1) j, p x + ∑ x ∈ Ioc (s + 1) j, searchVisits x r • p x := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x hx => ?_
      rw [mem_Ioc] at hx
      rw [searchVisits, ite_eq_right (by omega), ite_eq_left (by omega), add_nsmul, one_nsmul]
    have e4 : ∑ x ∈ Icc i s, successorVisits x (.node (s + 1) l r) • q x =
        ∑ x ∈ Icc i s, q x + ∑ x ∈ Icc i s, successorVisits x l • q x := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x hx => ?_
      rw [mem_Icc] at hx
      rw [successorVisits, ite_eq_left (by omega), add_nsmul, one_nsmul]
    have e5 : ∑ x ∈ Icc (s + 1) j, successorVisits x (.node (s + 1) l r) • q x =
        ∑ x ∈ Icc (s + 1) j, q x + ∑ x ∈ Icc (s + 1) j, successorVisits x r • q x := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x hx => ?_
      rw [mem_Icc] at hx
      rw [successorVisits, ite_eq_right (by omega), add_nsmul, one_nsmul]
    rw [e1, e2, e3, e4, e5, treeCost, Nat.add_sub_cancel, ihl, ihr, knuthWeight, hIoc, hIcc]
    abel

end Cost

section DP

variable [AddCommMonoid β] [LinearOrder β]

/-- The interval recurrence with explicit fuel. -/
def optCostAux (w : ℕ → ℕ → β) : ℕ → ℕ → ℕ → β
  | 0, _, _ => 0
  | f + 1, i, j =>
    if h : i < j then
      w i j + (Ioc i j).inf' (nonempty_Ioc.2 h) fun k =>
        optCostAux w f i (k - 1) + optCostAux w f k j
    else 0

/-- The optimal cost `c(i, j)` of the interval recurrence
`c(i, j) = w(i, j) + min_{i < k ≤ j} (c(i, k - 1) + c(k, j))`, with `c(i, j) = 0` for `j ≤ i`. -/
def optCost (w : ℕ → ℕ → β) (i j : ℕ) : β := optCostAux w (j - i) i j

theorem optCostAux_eq (w : ℕ → ℕ → β) {f g i j : ℕ} (hf : j - i ≤ f) (hg : j - i ≤ g) :
    optCostAux w f i j = optCostAux w g i j := by
  induction f generalizing g i j with
  | zero =>
    cases g with
    | zero => rfl
    | succ g => rw [optCostAux, optCostAux, dite_eq_right (by omega)]
  | succ f ih =>
    cases g with
    | zero => rw [optCostAux, optCostAux, dite_eq_right (by omega)]
    | succ g =>
      simp only [optCostAux]
      split_ifs with h
      · congr 1
        refine inf'_congr _ rfl fun k hk => ?_
        rw [mem_Ioc] at hk
        rw [ih (g := g) (by omega) (by omega), ih (g := g) (by omega) (by omega)]
      · rfl

theorem optCostAux_eq_optCost (w : ℕ → ℕ → β) {f i j : ℕ} (hf : j - i ≤ f) :
    optCostAux w f i j = optCost w i j :=
  optCostAux_eq w hf le_rfl

/-- The cost of choosing root `k` for the keys `i + 1, …, j`, beyond the weight `w i j`. -/
@[expose] def splitCost (w : ℕ → ℕ → β) (i j k : ℕ) : β := optCost w i (k - 1) + optCost w k j

theorem optCost_of_le (w : ℕ → ℕ → β) {i j : ℕ} (h : j ≤ i) : optCost w i j = 0 := by
  rw [optCost, show j - i = 0 by omega, optCostAux]

/-- The recurrence for `optCost`. -/
theorem optCost_eq (w : ℕ → ℕ → β) {i j : ℕ} (h : i < j) :
    optCost w i j = w i j + (Ioc i j).inf' (nonempty_Ioc.2 h) (splitCost w i j) := by
  rw [optCost, show j - i = (j - i - 1) + 1 by omega, optCostAux, dite_eq_left h]
  congr 1
  refine inf'_congr _ rfl fun k hk => ?_
  rw [mem_Ioc] at hk
  rw [splitCost, optCostAux_eq_optCost w (by omega), optCostAux_eq_optCost w (by omega)]

/-- The largest optimal root of the keys `i + 1, …, j` (and `0` when `j ≤ i`). -/
def optRoot (w : ℕ → ℕ → β) (i j : ℕ) : ℕ :=
  ((Ioc i j).filter fun k => ∀ k' ∈ Ioc i j, splitCost w i j k ≤ splitCost w i j k').sup id

theorem optRoot_spec (w : ℕ → ℕ → β) {i j : ℕ} (h : i < j) :
    optRoot w i j ∈ Ioc i j ∧
      ∀ k ∈ Ioc i j, splitCost w i j (optRoot w i j) ≤ splitCost w i j k := by
  obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_inf' (nonempty_Ioc.2 h) (splitCost w i j)
  have hne : ((Ioc i j).filter fun k => ∀ k' ∈ Ioc i j,
      splitCost w i j k ≤ splitCost w i j k').Nonempty :=
    ⟨k, mem_filter.2 ⟨hk, fun k' hk' => hkeq ▸ inf'_le _ hk'⟩⟩
  obtain ⟨r, hr, hreq⟩ := exists_mem_eq_sup _ hne id
  rw [optRoot, hreq]
  exact (mem_filter.1 hr)

theorem optRoot_mem (w : ℕ → ℕ → β) {i j : ℕ} (h : i < j) : optRoot w i j ∈ Ioc i j :=
  (optRoot_spec w h).1

theorem splitCost_optRoot_le (w : ℕ → ℕ → β) {i j k : ℕ} (hk : k ∈ Ioc i j) :
    splitCost w i j (optRoot w i j) ≤ splitCost w i j k :=
  (optRoot_spec w (by rw [mem_Ioc] at hk; omega)).2 k hk

/-- Every optimal root is at most `optRoot`. -/
theorem le_optRoot (w : ℕ → ℕ → β) {i j k : ℕ} (hk : k ∈ Ioc i j)
    (hopt : ∀ k' ∈ Ioc i j, splitCost w i j k ≤ splitCost w i j k') : k ≤ optRoot w i j :=
  le_sup (f := id) (mem_filter.2 ⟨hk, hopt⟩)

theorem optRoot_of_le (w : ℕ → ℕ → β) {i j : ℕ} (h : j ≤ i) : optRoot w i j = 0 := by
  rw [optRoot, Ioc_eq_empty (by omega), filter_empty, sup_empty]
  rfl

theorem optCost_eq_optRoot (w : ℕ → ℕ → β) {i j : ℕ} (h : i < j) :
    optCost w i j = w i j + splitCost w i j (optRoot w i j) := by
  rw [optCost_eq w h]
  congr 1
  exact le_antisymm (inf'_le _ (optRoot_mem w h))
    (le_inf' _ _ fun k hk => splitCost_optRoot_le w hk)

/-- The tree read off a root table `R`, with fuel: the root of the keys `i + 1, …, j` is
`R i j`. -/
@[expose] def buildTree (R : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → BinaryTree ℕ
  | 0, _, _ => .nil
  | f + 1, i, j =>
    if i < j then .node (R i j) (buildTree R f i (R i j - 1)) (buildTree R f (R i j) j) else .nil

/-- An optimal tree on the keys `i + 1, …, j`, read off the largest optimal roots. -/
@[expose] def optTree (w : ℕ → ℕ → β) (i j : ℕ) : BinaryTree ℕ := buildTree (optRoot w) (j - i) i j

/-- Two root tables that agree on all subintervals of `(i, j]` and choose roots inside them build
the same tree. -/
theorem buildTree_congr {R R' : ℕ → ℕ → ℕ} {f i j : ℕ}
    (hR : ∀ a b, i ≤ a → a < b → b ≤ j → R a b = R' a b)
    (hmem : ∀ a b, i ≤ a → a < b → b ≤ j → R a b ∈ Ioc a b) :
    buildTree R f i j = buildTree R' f i j := by
  induction f generalizing i j with
  | zero => rfl
  | succ f ih =>
    simp only [buildTree]
    split_ifs with h
    · have hm := mem_Ioc.1 (hmem i j le_rfl h le_rfl)
      rw [← hR i j le_rfl h le_rfl,
        ih (fun a b h₁ h₂ h₃ => hR a b h₁ h₂ (by omega))
          (fun a b h₁ h₂ h₃ => hmem a b h₁ h₂ (by omega)),
        ih (fun a b h₁ h₂ h₃ => hR a b (by omega) h₂ h₃)
          (fun a b h₁ h₂ h₃ => hmem a b (by omega) h₂ h₃)]
    · rfl

theorem buildTree_optRoot_spec (w : ℕ → ℕ → β) {f i j : ℕ} (hf : j - i ≤ f) (hij : i ≤ j) :
    IsBST i j (buildTree (optRoot w) f i j) ∧
      treeCost w i j (buildTree (optRoot w) f i j) = optCost w i j := by
  induction f generalizing i j with
  | zero =>
    obtain rfl : i = j := by omega
    exact ⟨.nil i, by rw [buildTree, treeCost, optCost_of_le w le_rfl]⟩
  | succ f ih =>
    rw [buildTree]
    split_ifs with h
    · have hm := mem_Ioc.1 (optRoot_mem w h)
      obtain ⟨hl, hlc⟩ := ih (i := i) (j := optRoot w i j - 1) (by omega) (by omega)
      obtain ⟨hr, hrc⟩ := ih (i := optRoot w i j) (j := j) (by omega) (by omega)
      refine ⟨.node hm.1 hm.2 hl hr, ?_⟩
      rw [treeCost, hlc, hrc, optCost_eq_optRoot w h, splitCost, add_assoc]
    · obtain rfl : i = j := by omega
      exact ⟨.nil i, by rw [treeCost, optCost_of_le w le_rfl]⟩

theorem isBST_optTree (w : ℕ → ℕ → β) {i j : ℕ} (hij : i ≤ j) : IsBST i j (optTree w i j) :=
  (buildTree_optRoot_spec w le_rfl hij).1

theorem treeCost_optTree (w : ℕ → ℕ → β) {i j : ℕ} (hij : i ≤ j) :
    treeCost w i j (optTree w i j) = optCost w i j :=
  (buildTree_optRoot_spec w le_rfl hij).2

variable [IsOrderedAddMonoid β]

theorem optCost_le (w : ℕ → ℕ → β) {i j k : ℕ} (hk : k ∈ Ioc i j) :
    optCost w i j ≤ w i j + splitCost w i j k := by
  rw [optCost_eq_optRoot w (by rw [mem_Ioc] at hk; omega)]
  exact add_le_add le_rfl (splitCost_optRoot_le w hk)

/-- The recurrence is at most the cost of every tree. -/
theorem optCost_le_treeCost (w : ℕ → ℕ → β) {i j : ℕ} {t : BinaryTree ℕ} (h : IsBST i j t) :
    optCost w i j ≤ treeCost w i j t := by
  induction h with
  | nil i => rw [optCost_of_le w le_rfl, treeCost]
  | @node i j k l r hik hkj _ _ ihl ihr =>
    calc optCost w i j ≤ w i j + splitCost w i j k := optCost_le w (mem_Ioc.2 ⟨hik, hkj⟩)
      _ ≤ w i j + (treeCost w i (k - 1) l + treeCost w k j r) :=
        add_le_add le_rfl (add_le_add ihl ihr)
      _ = treeCost w i j (.node k l r) := by rw [treeCost, add_assoc]

/-- **Optimality of the interval recurrence**: `optCost w i j` is the least cost of a binary search
tree on the keys `i + 1, …, j`, attained by `optTree w i j`. -/
theorem isLeast_optCost (w : ℕ → ℕ → β) {i j : ℕ} (hij : i ≤ j) :
    IsLeast {c | ∃ t, IsBST i j t ∧ treeCost w i j t = c} (optCost w i j) :=
  ⟨⟨optTree w i j, isBST_optTree w hij, treeCost_optTree w hij⟩,
    fun _ ⟨_, ht, hc⟩ => hc ▸ optCost_le_treeCost w ht⟩

end DP

end Cslib.Algorithms.Lean.OptimalBST
