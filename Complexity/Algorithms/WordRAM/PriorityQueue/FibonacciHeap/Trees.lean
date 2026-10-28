/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.Model

/-!
# Chronological heap-tree model for a static-array Fibonacci heap

This file defines the raw field view `RawState n` of a static-array Fibonacci heap together with an
inductive rose-tree witness `FHTree n` whose children lists record the chronological linking order
used in Fredman and Tarjan's child-loss rank invariant [Fredman and Tarjan][FredmanTarjan1987].

Representing trees inductively rather than by pointer reachability makes framing across disjoint
subtrees structural: `ValidSubtree` inspects `par`, `left`, and `right` only at strict descendants
of a subtree's root, so linking roots, rotating or splicing root lists, and updating the degree
consolidation table leave existing subtrees valid by direct structural induction.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.RawState`: abstract view of the eight
  `n`-word node arrays, `(n + 1)`-word consolidation array, and four scalar heap counters.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.FHTree`: rose tree over `Fin n` with
  chronological child lists.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.ValidSubtree`, `ValidRoot`: heap-order,
  pointer-realization, and Fredman–Tarjan chronological rank invariants (allowing at most one
  transient `pending` node during cascading cuts).

## Main results

* `ValidSubtree.fib_le_size`, `ValidSubtree.deg_bounds`: `fib (T.deg + 2) ≤ T.size`, yielding both
  `T.deg ≤ 2 * Nat.log 2 m + 1` and `T.deg + 1 ≤ m` whenever `T.size ≤ m`.
* `ValidRoot.singleton`, `ValidRoot.link`: creation of singleton root trees and degree-preserving
  root linking during consolidation.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.Algorithms.Lean

/-! ## Raw array/scalar state and marked-node counting -/

/-- Decoded view of the static arrays and persistent scalar registers of a Fibonacci heap on `n`
handles. -/
structure RawState (n : ℕ) where
  /-- Key array `key[v]` (`v < n`). -/
  key : Fin n → ℕ
  /-- Nullable parent pointer array `par[v]` (`0` = root, `p + 1` = parent `p`). -/
  par : Fin n → ℕ
  /-- Nullable first-child pointer array `child[v]` (`0` = leaf, `c + 1` = child `c`). -/
  child : Fin n → ℕ
  /-- Circular doubly-linked sibling predecessor array `left[v]`. -/
  left : Fin n → ℕ
  /-- Circular doubly-linked sibling successor array `right[v]`. -/
  right : Fin n → ℕ
  /-- Child-list degree array `deg[v]`. -/
  deg : Fin n → ℕ
  /-- Cascading-cut mark array `mark[v]` (`0` = unmarked, `1` = marked). -/
  mark : Fin n → ℕ
  /-- Heap membership array `inHeap[v]` (`0` = absent, `1` = present). -/
  inHeap : Fin n → ℕ
  /-- Degree-consolidation scratch table `A[d]` (`0` = empty, `u + 1` = root `u`). -/
  cons : ℕ → ℕ
  /-- Nullable minimum-root pointer `minRoot` (`0` = empty, `r + 1` = root `r`). -/
  minRoot : ℕ
  /-- Number of trees in the root list. -/
  numRoots : ℕ
  /-- Number of currently live, marked handles. -/
  numMarked : ℕ
  /-- Total number of live handles in the heap. -/
  sz : ℕ

/-- Set of currently live, marked handles. -/
def markedSet {n : ℕ} (st : RawState n) : Finset (Fin n) :=
  Finset.univ.filter fun u => st.inHeap u ≠ 0 ∧ st.mark u ≠ 0

/-- Number of currently live, marked handles. -/
def markedCount {n : ℕ} (st : RawState n) : ℕ :=
  (markedSet st).card

theorem markedCount_le_n {n : ℕ} (st : RawState n) : markedCount st ≤ n := by
  unfold markedCount markedSet
  exact (Finset.card_le_univ _).trans (by simp only [Fintype.card_fin, le_rfl])

theorem markedCount_congr {n : ℕ} {st st' : RawState n}
    (h : ∀ u : Fin n, (st'.inHeap u ≠ 0 ∧ st'.mark u ≠ 0) ↔ (st.inHeap u ≠ 0 ∧ st.mark u ≠ 0)) :
    markedCount st' = markedCount st := by
  unfold markedCount markedSet
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h u]

theorem markedCount_clear_one {n : ℕ} {st st' : RawState n} {u : Fin n}
    (hin : st.inHeap u ≠ 0) (hm : st.mark u ≠ 0)
    (hu : st'.mark u = 0)
    (hother : ∀ x : Fin n, x ≠ u →
      ((st'.inHeap x ≠ 0 ∧ st'.mark x ≠ 0) ↔ (st.inHeap x ≠ 0 ∧ st.mark x ≠ 0))) :
    markedCount st' + 1 = markedCount st := by
  have hmem : u ∈ markedSet st := by
    simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hin, hm⟩
  have heq : markedSet st' = (markedSet st).erase u := by
    ext x
    by_cases hxu : x = u
    · subst hxu
      simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and, hu, ne_eq,
        not_true_eq_false, and_false, Finset.mem_erase, false_and]
    · simp only [Finset.mem_erase, ne_eq, hxu, not_false_eq_true, true_and, markedSet,
        Finset.mem_filter, Finset.mem_univ, hother x hxu]
  unfold markedCount
  rw [heq, Finset.card_erase_add_one hmem]

theorem markedCount_set_one {n : ℕ} {st st' : RawState n} {u : Fin n}
    (hin : st'.inHeap u ≠ 0) (hm0 : st.mark u = 0) (hm1 : st'.mark u ≠ 0)
    (hother : ∀ x : Fin n, x ≠ u →
      ((st'.inHeap x ≠ 0 ∧ st'.mark x ≠ 0) ↔ (st.inHeap x ≠ 0 ∧ st.mark x ≠ 0))) :
    markedCount st' = markedCount st + 1 := by
  have hnotmem : u ∉ markedSet st := by
    simp only [markedSet, Finset.mem_filter, Finset.mem_univ, hm0, ne_eq,
      not_true_eq_false, and_false, not_false_eq_true]
  have heq : markedSet st' = insert u (markedSet st) := by
    ext x
    by_cases hxu : x = u
    · subst hxu
      simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and, hin, ne_eq, hm1,
        not_false_eq_true, and_self, Finset.mem_insert, true_or]
    · simp only [Finset.mem_insert, hxu, false_or, markedSet, Finset.mem_filter, Finset.mem_univ,
        true_and, hother x hxu]
  unfold markedCount
  rw [heq, Finset.card_insert_of_notMem hnotmem]

/-! ## Forward pointer chains for consolidation traversal -/

/-- One-way `right`-pointer chain through a remaining list of roots or children. -/
def RightChain {n : ℕ} (right : Fin n → ℕ) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => right x = y.val ∧ RightChain right (y :: xs)

theorem RightChain.frame {n : ℕ} {right right' : Fin n → ℕ} {L : List (Fin n)}
    (hL : RightChain right L) (heq : ∀ x ∈ L, right' x = right x) :
    RightChain right' L := by
  induction L with
  | nil => trivial
  | cons x xs ih =>
    rcases xs with _ | ⟨y, rest⟩
    · trivial
    · simp only [RightChain] at hL ⊢
      exact ⟨(heq x List.mem_cons_self).trans hL.1,
        ih hL.2 (fun z hz => heq z (List.mem_cons_of_mem x hz))⟩

private theorem ChainLinks.rightChain {n : ℕ} {left right : Fin n → ℕ} {first : Fin n} :
    ∀ (prev : Fin n) (xs : List (Fin n)),
      ChainLinks left right first prev xs → RightChain right (prev :: xs)
  | _, [], _ => trivial
  | _, x :: xs, hc => ⟨hc.1, ChainLinks.rightChain x xs hc.2.2⟩

/-- Every circular doubly-linked list forms a `RightChain`. -/
theorem IsCircList.rightChain {n : ℕ} {left right : Fin n → ℕ} {L : List (Fin n)}
    (hL : IsCircList left right L) : RightChain right L := by
  rcases L with _ | ⟨h, tail⟩
  · trivial
  · exact ChainLinks.rightChain h tail hL.2

/-! ## Chronological rose-tree witnesses -/

/-- Rose tree over `Fin n` whose `children` list is ordered chronologically by linking time. -/
inductive FHTree (n : ℕ) : Type where
  | node (root : Fin n) (children : List (FHTree n)) : FHTree n

/-- Root handle of `T`. -/
def FHTree.root {n : ℕ} : FHTree n → Fin n
  | .node u _ => u

/-- Chronological child list of `T`. -/
def FHTree.children {n : ℕ} : FHTree n → List (FHTree n)
  | .node _ cs => cs

/-- Root degree of `T`. -/
def FHTree.deg {n : ℕ} (T : FHTree n) : ℕ :=
  T.children.length

@[simp]
theorem FHTree.root_node {n : ℕ} (u : Fin n) (cs : List (FHTree n)) :
    (FHTree.node u cs).root = u :=
  rfl

@[simp]
theorem FHTree.children_node {n : ℕ} (u : Fin n) (cs : List (FHTree n)) :
    (FHTree.node u cs).children = cs :=
  rfl

@[simp]
theorem FHTree.deg_node {n : ℕ} (u : Fin n) (cs : List (FHTree n)) :
    (FHTree.node u cs).deg = cs.length :=
  rfl

mutual
/-- Preorder list of all handles in `T`. -/
def FHTree.nodes {n : ℕ} : FHTree n → List (Fin n)
  | .node u cs => u :: forestNodes cs

/-- Concatenated handle lists of a forest `ts`. -/
def forestNodes {n : ℕ} : List (FHTree n) → List (Fin n)
  | [] => []
  | T :: ts => T.nodes ++ forestNodes ts
end

/-- Number of nodes in `T`. -/
def FHTree.size {n : ℕ} (T : FHTree n) : ℕ :=
  T.nodes.length

theorem FHTree.nodes_eq {n : ℕ} (T : FHTree n) : T.nodes = T.root :: forestNodes T.children := by
  cases T
  rfl

theorem FHTree.root_mem_nodes {n : ℕ} (T : FHTree n) : T.root ∈ T.nodes := by
  cases T
  exact List.mem_cons_self

theorem FHTree.size_pos {n : ℕ} (T : FHTree n) : 1 ≤ T.size := by
  cases T
  simp only [FHTree.size, FHTree.nodes, List.length_cons]
  omega

theorem forestNodes_append {n : ℕ} (ts₁ ts₂ : List (FHTree n)) :
    forestNodes (ts₁ ++ ts₂) = forestNodes ts₁ ++ forestNodes ts₂ := by
  induction ts₁ with
  | nil => simp only [List.nil_append, forestNodes]
  | cons T ts ih =>
    simp only [List.cons_append, forestNodes, ih, List.append_assoc]

theorem mem_forestNodes_iff {n : ℕ} {ts : List (FHTree n)} {x : Fin n} :
    x ∈ forestNodes ts ↔ ∃ T ∈ ts, x ∈ T.nodes := by
  induction ts with
  | nil => simp only [forestNodes, List.not_mem_nil, false_and, exists_false]
  | cons T rest ih =>
    simp only [forestNodes, List.mem_append, ih, List.mem_cons, exists_eq_or_imp]

theorem forestNodes_perm {n : ℕ} {ts₁ ts₂ : List (FHTree n)} (hp : ts₁.Perm ts₂) :
    (forestNodes ts₁).Perm (forestNodes ts₂) := by
  induction hp with
  | nil => exact List.Perm.nil
  | cons T _ ih =>
    simp only [forestNodes]
    exact List.Perm.append_left T.nodes ih
  | swap T₁ T₂ ts =>
    simp only [forestNodes, ← List.append_assoc]
    exact List.Perm.append_right (forestNodes ts) List.perm_append_comm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem forestNodes_length_ge {n : ℕ} (ts : List (FHTree n)) :
    ts.length ≤ (forestNodes ts).length := by
  induction ts with
  | nil => simp only [List.length_nil, forestNodes, le_rfl]
  | cons T rest ih =>
    simp only [List.length_cons, forestNodes, List.length_append]
    have hpos := T.size_pos
    unfold FHTree.size at hpos
    omega

theorem forestNodes_nodup_tree {n : ℕ} {ts : List (FHTree n)} (hnd : (forestNodes ts).Nodup)
    {T : FHTree n} (hT : T ∈ ts) : T.nodes.Nodup := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hT
  rw [forestNodes_append, forestNodes] at hnd
  exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1

theorem forestNodes_nodup_disjoint {n : ℕ} {ts : List (FHTree n)} (hnd : (forestNodes ts).Nodup)
    {T₁ T₂ : FHTree n} (h₁ : T₁ ∈ ts) (h₂ : T₂ ∈ ts) (hne : T₁ ≠ T₂)
    {x : Fin n} (hx₁ : x ∈ T₁.nodes) (hx₂ : x ∈ T₂.nodes) : False := by
  induction ts with
  | nil => exact absurd h₁ List.not_mem_nil
  | cons hd tl ih =>
    simp only [forestNodes] at hnd
    obtain ⟨_, hnd_tl, hdisj⟩ := List.nodup_append.mp hnd
    rcases List.mem_cons.mp h₁ with rfl | h₁_tl
    · rcases List.mem_cons.mp h₂ with rfl | h₂_tl
      · exact hne rfl
      · exact hdisj x hx₁ x (mem_forestNodes_iff.mpr ⟨T₂, h₂_tl, hx₂⟩) rfl
    · rcases List.mem_cons.mp h₂ with rfl | h₂_tl
      · exact hdisj x hx₂ x (mem_forestNodes_iff.mpr ⟨T₁, h₁_tl, hx₁⟩) rfl
      · exact ih hnd_tl h₁_tl h₂_tl

/-! ## Subtree and root invariants -/

/-- Structural heap-order, child-list, and chronological rank invariant on a subtree `T`
(`hrank`, a strengthening of [Fredman and Tarjan][FredmanTarjan1987], Lemma 1, p. 604;
[Cormen et al.][CLRS2009], Lemma 19.1).
When `pending = some w`, `w` has just lost a child during cascading cuts and is permitted one extra
unit of slack before either being cut itself (`mark w = 1`) or becoming marked (`mark w = 0`). -/
inductive ValidSubtree {n : ℕ} (st : RawState n) (pending : Option (Fin n)) : FHTree n → Prop where
  | mk {u : Fin n} {cs : List (FHTree n)}
      (hin : st.inHeap u ≠ 0)
      (hmark : st.mark u ≤ 1)
      (hdeg : st.deg u = cs.length)
      (hchild :
        (cs = [] ∧ st.child u = 0) ∨
        (∃ (h : Fin n) (tail : List (Fin n)),
          st.child u = h.val + 1 ∧
          IsCircList st.left st.right (h :: tail) ∧
          (h :: tail).Perm (cs.map FHTree.root)))
      (hpar : ∀ T ∈ cs, st.par T.root = u.val + 1)
      (hprio : ∀ T ∈ cs, IndexedMinPQ.PrioLT (u, st.key u) (T.root, st.key T.root))
      (hrank : ∀ (i : ℕ) (hi : i < cs.length),
        i ≤ st.deg (cs[i]).root + st.mark (cs[i]).root +
          (if some (cs[i]).root = pending then 1 else 0))
      (hsub : ∀ T ∈ cs, ValidSubtree st pending T) :
      ValidSubtree st pending (.node u cs)

/-- A valid root tree is a valid subtree whose root has `par = 0` and `mark = 0`. -/
def ValidRoot {n : ℕ} (st : RawState n) (pending : Option (Fin n)) (T : FHTree n) : Prop :=
  ValidSubtree st pending T ∧ st.par T.root = 0 ∧ st.mark T.root = 0

/-- `ValidSubtree` inspects `par`, `left`, `right`, and `pending` only on strict descendants
`forestNodes T.children`, never on `T.root` itself. -/
theorem ValidSubtree.frame {n : ℕ} {st st' : RawState n} {pending pending' : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T)
    (hnode : ∀ x ∈ T.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.deg x = st.deg x ∧
      st'.child x = st.child x ∧ st'.key x = st.key x)
    (hdesc : ∀ x ∈ forestNodes T.children,
      st'.par x = st.par x ∧ st'.left x = st.left x ∧ st'.right x = st.right x ∧
      ((some x = pending') ↔ (some x = pending))) :
    ValidSubtree st' pending' T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank _ ih =>
    have hu := hnode u List.mem_cons_self
    have hc_root_desc : ∀ c ∈ cs, c.root ∈ forestNodes cs := fun c hc =>
      mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩
    refine ⟨by rw [hu.1]; exact hin, by rw [hu.2.1]; exact hmark, by rw [hu.2.2.1]; exact hdeg,
      ?_, ?_, ?_, ?_, ?_⟩
    · rcases hchild with ⟨rfl, hc0⟩ | ⟨h, tail, hcu, hcirc, hperm⟩
      · exact Or.inl ⟨rfl, hu.2.2.2.1.trans hc0⟩
      · refine Or.inr ⟨h, tail, hu.2.2.2.1.trans hcu, hcirc.frame fun x hx => ?_, hperm⟩
        have hx_map : x ∈ cs.map FHTree.root := hperm.subset hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx_map
        have hd := hdesc c.root (hc_root_desc c hc)
        exact ⟨hd.2.1, hd.2.2.1⟩
    · intro c hc
      exact (hdesc c.root (hc_root_desc c hc)).1.trans (hpar c hc)
    · intro c hc
      have hcn := hnode c.root (List.mem_cons_of_mem u (hc_root_desc c hc))
      rw [hu.2.2.2.2, hcn.2.2.2.2]
      exact hprio c hc
    · intro i hi
      have hmem : cs[i] ∈ cs := List.getElem_mem hi
      have hcn := hnode (cs[i]).root (List.mem_cons_of_mem u (hc_root_desc cs[i] hmem))
      have hd := hdesc (cs[i]).root (hc_root_desc cs[i] hmem)
      have hiff := hd.2.2.2
      have hite : (if some (cs[i]).root = pending' then 1 else 0) =
          (if some (cs[i]).root = pending then 1 else 0) := by
        simp only [hiff]
      rw [hcn.2.2.1, hcn.2.1, hite]
      exact hrank i hi
    · intro c hc
      exact ih c hc
        (fun x hx => hnode x (List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, hx⟩)))
        (fun x hx => hdesc x (mem_forestNodes_iff.mpr ⟨c, hc,
          c.nodes_eq ▸ List.mem_cons_of_mem c.root hx⟩))

theorem ValidSubtree.weaken_pending {n : ℕ} {st : RawState n} (pending : Option (Fin n))
    {T : FHTree n} (hT : ValidSubtree st none T) : ValidSubtree st pending T := by
  induction hT with
  | @mk u cs hin hmark hdeg hchild hpar hprio hrank _ ih =>
    refine ⟨hin, hmark, hdeg, hchild, hpar, hprio, fun i hi => ?_, ih⟩
    have hr := hrank i hi
    simp only [reduceCtorEq, ↓reduceIte, Nat.add_zero] at hr
    omega

theorem ValidSubtree.clear_pending {n : ℕ} {st : RawState n} {z : Fin n} {T : FHTree n}
    (hT : ValidSubtree st (some z) T) (hz : z ∉ forestNodes T.children) :
    ValidSubtree st none T :=
  hT.frame (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) fun x hx =>
    ⟨rfl, rfl, rfl, by
      have hne : x ≠ z := fun e => hz (e ▸ hx)
      simp only [reduceCtorEq, Option.some.injEq, hne]⟩

theorem ValidSubtree.prioLT_of_mem_children {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) :
    ∀ x ∈ forestNodes T.children, IndexedMinPQ.PrioLT (T.root, st.key T.root) (x, st.key x) := by
  induction hT with
  | @mk u cs _ _ _ _ _ hprio _ _ ih =>
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_forestNodes_iff.mp hx
    cases hc_eq : c with
    | node w cs_w =>
      rw [hc_eq] at hc hxc
      have hlt_uw : IndexedMinPQ.PrioLT (u, st.key u) (w, st.key w) := hprio (.node w cs_w) hc
      rcases List.mem_cons.mp hxc with rfl | hdesc
      · exact hlt_uw
      · exact hlt_uw.trans (ih (.node w cs_w) hc x hdesc)

theorem ValidSubtree.prioLE_of_mem {n : ℕ} {st : RawState n} {pending : Option (Fin n)}
    {T : FHTree n} (hT : ValidSubtree st pending T) {x : Fin n} (hx : x ∈ T.nodes) :
    IndexedMinPQ.PrioLE (T.root, st.key T.root) (x, st.key x) := by
  cases T with
  | node u cs =>
    rcases List.mem_cons.mp hx with rfl | hdesc
    · exact IndexedMinPQ.PrioLE.refl _
    · exact (hT.prioLT_of_mem_children x hdesc).le

/-! ## Fibonacci subtree-size and degree bounds -/

theorem deg_add_one_le_fib (d : ℕ) : d + 1 ≤ Nat.fib (d + 2) := by
  induction d with
  | zero => decide
  | succ m ih =>
    rcases m with _ | m
    · decide
    · have hstep : m + 1 + 1 + 2 = (m + 2) + 2 := by omega
      have hfib : Nat.fib ((m + 2) + 2) = Nat.fib (m + 2) + Nat.fib ((m + 2) + 1) :=
        Nat.fib_add_two
      have hpos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
      have h1 : m + 1 + 2 = (m + 2) + 1 := by omega
      rw [h1] at ih
      rw [hstep, hfib]
      omega

private theorem fib_range_le_forestNodes {n : ℕ} :
    ∀ (k : ℕ) (cs : List (FHTree n)),
      (∀ (j : ℕ) (hj : j < cs.length), Nat.fib ((k + j - 1) + 2) ≤ (cs[j]).size) →
      ∑ j ∈ Finset.range cs.length, Nat.fib ((k + j - 1) + 2) ≤ (forestNodes cs).length
  | _, [], _ => by
    simp only [List.length_nil, Finset.range_zero, Finset.sum_empty, forestNodes, le_rfl]
  | k, c :: rest, h => by
    rw [List.length_cons, Finset.sum_range_succ']
    have h0 := h 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero, List.getElem_cons_zero, FHTree.size] at h0
    have hrest := fib_range_le_forestNodes (k + 1) rest fun j hj => by
      have hj' := h (j + 1) (Nat.succ_lt_succ hj)
      have hk : k + (j + 1) = k + 1 + j := by omega
      simpa only [hk, List.getElem_cons_succ] using hj'
    have hsum_eq : (∑ j ∈ Finset.range rest.length, Nat.fib (k + (j + 1) - 1 + 2)) =
        ∑ j ∈ Finset.range rest.length, Nat.fib (k + 1 + j - 1 + 2) :=
      Finset.sum_congr rfl fun j _ => by congr 1; omega
    rw [hsum_eq]
    simp only [Nat.add_zero, forestNodes, List.length_append]
    omega

/-- Fredman–Tarjan subtree size lower bound ([Fredman and Tarjan][FredmanTarjan1987], Corollary 1,
p. 604; [Cormen et al.][CLRS2009], Lemma 19.4): in any subtree with no pending cascading cut,
`Nat.fib (T.deg + 2) ≤ T.size`. -/
theorem ValidSubtree.fib_le_size {n : ℕ} {st : RawState n} {T : FHTree n}
    (hT : ValidSubtree st none T) : Nat.fib (T.deg + 2) ≤ T.size := by
  induction hT with
  | @mk u cs _ _ _ _ _ _ hrank hsub ih =>
    have hsum_le : ∑ j ∈ Finset.range cs.length, Nat.fib ((0 + j - 1) + 2) ≤
        (forestNodes cs).length := by
      refine fib_range_le_forestNodes 0 cs fun i hi => ?_
      have hmem : cs[i] ∈ cs := List.getElem_mem hi
      have hc_sub := hsub cs[i] hmem
      cases hci : cs[i] with
      | node w cs_w =>
        rw [hci] at hc_sub
        rcases hc_sub with ⟨_, hmw, hdw, _, _, _, _, _⟩
        have hr := hrank i hi
        simp only [hci, FHTree.root, reduceCtorEq, ↓reduceIte, Nat.add_zero] at hr
        have hidx : (0 + i - 1) + 2 ≤ cs_w.length + 2 := by omega
        have hmono : Nat.fib ((0 + i - 1) + 2) ≤ Nat.fib ((.node w cs_w : FHTree n).deg + 2) :=
          Nat.fib_mono hidx
        exact hmono.trans (ih (.node w cs_w) (hci ▸ hmem))
    simp only [Nat.zero_add] at hsum_le
    have hident := fib_sum_pred_add_two cs.length
    have hsize : (.node u cs : FHTree n).size = 1 + (forestNodes cs).length := by
      simp only [FHTree.size, FHTree.nodes, List.length_cons]
      omega
    rw [FHTree.deg, FHTree.children, hsize]
    omega

/-- Any valid subtree of size at most `m` has degree `≤ 2 * Nat.log 2 m + 1` and `deg + 1 ≤ m`. -/
theorem ValidSubtree.deg_bounds {n : ℕ} {st : RawState n} {T : FHTree n}
    (hT : ValidSubtree st none T) {m : ℕ} (hm : T.size ≤ m) :
    T.deg ≤ 2 * Nat.log 2 m + 1 ∧ T.deg + 1 ≤ m := by
  have hfib : Nat.fib (T.deg + 2) ≤ m := hT.fib_le_size.trans hm
  exact ⟨deg_le_two_mul_log_add_one hfib, (deg_add_one_le_fib T.deg).trans hfib⟩

/-! ## Constructing and linking root trees -/

/-- Creating a singleton root tree `.node v []`. -/
theorem ValidRoot.singleton {n : ℕ} {st : RawState n} {v : Fin n}
    (hin : st.inHeap v ≠ 0) (hpar : st.par v = 0) (hchild : st.child v = 0)
    (hdeg : st.deg v = 0) (hmark : st.mark v = 0) :
    ValidRoot st none (.node v []) := by
  refine ⟨⟨hin, by omega, hdeg, Or.inl ⟨rfl, hchild⟩, ?_, ?_, ?_, ?_⟩, hpar, hmark⟩
  · intro _ h; exact absurd h List.not_mem_nil
  · intro _ h; exact absurd h List.not_mem_nil
  · intro i hi; simp at hi
  · intro _ h; exact absurd h List.not_mem_nil

theorem link_nodes_eq {n : ℕ} (u : Fin n) (cs₁ : List (FHTree n)) (T₂ : FHTree n) :
    (FHTree.node u (cs₁ ++ [T₂])).nodes = (FHTree.node u cs₁).nodes ++ T₂.nodes := by
  simp only [FHTree.nodes, forestNodes_append, forestNodes, List.append_nil, List.cons_append]

/-- Linking an equal-degree root tree `T₂` as the newest child of `T₁` preserves `ValidRoot`
when `(T₁.root, key₁)` strictly precedes `(T₂.root, key₂)` under `IndexedMinPQ.PrioLT`. -/
theorem ValidRoot.link {n : ℕ} {st st' : RawState n} {T₁ T₂ : FHTree n}
    (h₁ : ValidRoot st none T₁) (h₂ : ValidRoot st none T₂)
    (hnd : (T₁.nodes ++ T₂.nodes).Nodup)
    (hdeg_eq : T₁.deg = T₂.deg)
    (hprio_lt : IndexedMinPQ.PrioLT (T₁.root, st.key T₁.root) (T₂.root, st.key T₂.root))
    (hunch : ∀ x ∈ T₁.nodes ++ T₂.nodes,
      st'.inHeap x = st.inHeap x ∧ st'.mark x = st.mark x ∧ st'.key x = st.key x)
    (hdeg' : st'.deg T₁.root = T₁.deg + 1 ∧
      ∀ x ∈ T₁.nodes ++ T₂.nodes, x ≠ T₁.root → st'.deg x = st.deg x)
    (hpar' : st'.par T₁.root = 0 ∧ st'.par T₂.root = T₁.root.val + 1 ∧
      ∀ x ∈ T₁.nodes ++ T₂.nodes, x ≠ T₂.root → st'.par x = st.par x)
    (hchild' : (∃ (h : Fin n) (tail : List (Fin n)),
        st'.child T₁.root = h.val + 1 ∧
        IsCircList st'.left st'.right (h :: tail) ∧
        (h :: tail).Perm ((T₁.children ++ [T₂]).map FHTree.root)) ∧
      ∀ x ∈ T₁.nodes ++ T₂.nodes, x ≠ T₁.root → st'.child x = st.child x)
    (hlr' : ∀ x ∈ T₁.nodes ++ T₂.nodes, x ≠ T₂.root → (∀ c ∈ T₁.children, x ≠ c.root) →
      st'.left x = st.left x ∧ st'.right x = st.right x) :
    ValidRoot st' none (.node T₁.root (T₁.children ++ [T₂])) := by
  cases T₁ with
  | node u cs₁ =>
    cases T₂ with
    | node v cs₂ =>
      rcases h₁ with ⟨⟨hin₁, hm₁, hd₁, _, hpar₁, hprio₁, hrank₁, hsub₁⟩, _, hm₁0⟩
      rcases h₂ with ⟨hsub₂_self, _, hm₂0⟩
      rcases hsub₂_self with ⟨hin₂, hm₂, hd₂, hchild₂, hpar₂, hprio₂, hrank₂, hsub₂⟩
      simp only [FHTree.root_node, FHTree.deg_node] at hdeg_eq hprio_lt hdeg'
      simp only [FHTree.root_node] at hpar'
      simp only [ValidRoot, FHTree.root_node, FHTree.children_node] at hchild' hlr' hm₁0 hm₂0 ⊢
      have hnd₁ : (u :: forestNodes cs₁).Nodup := (List.nodup_append.mp hnd).1
      have hnd₂ : (v :: forestNodes cs₂).Nodup := (List.nodup_append.mp hnd).2.1
      have hdisj_all : ∀ x ∈ u :: forestNodes cs₁, ∀ y ∈ v :: forestNodes cs₂, x ≠ y :=
        (List.nodup_append.mp hnd).2.2
      have hu_mem : u ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
        List.mem_append_left _ List.mem_cons_self
      have hv_mem : v ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
        List.mem_append_right _ List.mem_cons_self
      have hu_unch := hunch u hu_mem
      have hv_unch := hunch v hv_mem
      have hu_not_desc₁ : u ∉ forestNodes cs₁ := (List.nodup_cons.mp hnd₁).1
      have hv_not_desc₂ : v ∉ forestNodes cs₂ := (List.nodup_cons.mp hnd₂).1
      refine ⟨⟨by rw [hu_unch.1]; exact hin₁, by rw [hu_unch.2.1]; exact hm₁,
        by rw [hdeg'.1, List.length_append, List.length_singleton],
        Or.inr hchild'.1, ?_, ?_, ?_, ?_⟩, hpar'.1, by rw [hu_unch.2.1]; exact hm₁0⟩
      · intro T hT
        rcases List.mem_append.mp hT with hT₁ | hT₂
        · have hr_desc : T.root ∈ forestNodes cs₁ :=
            mem_forestNodes_iff.mpr ⟨T, hT₁, T.root_mem_nodes⟩
          have hr_mem : T.root ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
            List.mem_append_left _ (List.mem_cons_of_mem u hr_desc)
          have hr_ne_v : T.root ≠ v :=
            hdisj_all T.root (List.mem_cons_of_mem u hr_desc) v List.mem_cons_self
          exact (hpar'.2.2 T.root hr_mem hr_ne_v).trans (hpar₁ T hT₁)
        · rw [List.mem_singleton.mp hT₂]
          exact hpar'.2.1
      · intro T hT
        rcases List.mem_append.mp hT with hT₁ | hT₂
        · have hr_mem : T.root ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
            List.mem_append_left _
              (List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨T, hT₁, T.root_mem_nodes⟩))
          rw [hu_unch.2.2, (hunch T.root hr_mem).2.2]
          exact hprio₁ T hT₁
        · rw [List.mem_singleton.mp hT₂]
          simp only [FHTree.root]
          rw [hu_unch.2.2, hv_unch.2.2]
          exact hprio_lt
      · intro i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hi₁ : i < cs₁.length
        · rw [List.getElem_append_left hi₁]
          have hc_mem : cs₁[i] ∈ cs₁ := List.getElem_mem hi₁
          have hr_desc : (cs₁[i]).root ∈ forestNodes cs₁ :=
            mem_forestNodes_iff.mpr ⟨cs₁[i], hc_mem, (cs₁[i]).root_mem_nodes⟩
          have hr_mem : (cs₁[i]).root ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
            List.mem_append_left _ (List.mem_cons_of_mem u hr_desc)
          have hr_ne_u : (cs₁[i]).root ≠ u := fun e => hu_not_desc₁ (e ▸ hr_desc)
          rw [hdeg'.2 (cs₁[i]).root hr_mem hr_ne_u, (hunch (cs₁[i]).root hr_mem).2.1]
          exact hrank₁ i hi₁
        · have hi_eq : i = cs₁.length := by omega
          subst hi_eq
          simp only [List.getElem_append_right (le_refl cs₁.length), Nat.sub_self,
            List.getElem_singleton, FHTree.root, reduceCtorEq, ↓reduceIte, Nat.add_zero]
          have hv_ne_u : v ≠ u := (hdisj_all u List.mem_cons_self v List.mem_cons_self).symm
          rw [hdeg'.2 v hv_mem hv_ne_u, hv_unch.2.1, hd₂, ← hdeg_eq, hm₂0]
          omega
      · intro T hT
        rcases List.mem_append.mp hT with hT₁ | hT₂
        · refine (hsub₁ T hT₁).frame (fun x hx => ?_) (fun x hx => ?_)
          · have hx_desc : x ∈ forestNodes cs₁ := mem_forestNodes_iff.mpr ⟨T, hT₁, hx⟩
            have hx_mem : x ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
              List.mem_append_left _ (List.mem_cons_of_mem u hx_desc)
            have hx_ne_u : x ≠ u := fun e => hu_not_desc₁ (e ▸ hx_desc)
            have hu_x := hunch x hx_mem
            exact ⟨hu_x.1, hu_x.2.1, hdeg'.2 x hx_mem hx_ne_u, hchild'.2 x hx_mem hx_ne_u,
              hu_x.2.2⟩
          · have hx_in_T : x ∈ T.nodes := by
              cases T; exact List.mem_cons_of_mem _ hx
            have hx_desc : x ∈ forestNodes cs₁ := mem_forestNodes_iff.mpr ⟨T, hT₁, hx_in_T⟩
            have hx_mem : x ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
              List.mem_append_left _ (List.mem_cons_of_mem u hx_desc)
            have hx_ne_v : x ≠ v :=
              hdisj_all x (List.mem_cons_of_mem u hx_desc) v List.mem_cons_self
            have hnd_cs : (forestNodes cs₁).Nodup := (List.nodup_cons.mp hnd₁).2
            have hx_not_sib : ∀ c ∈ cs₁, x ≠ c.root := by
              intro c hc hxc
              by_cases hcT : c = T
              · subst hcT
                have hnd_c := forestNodes_nodup_tree hnd_cs hT₁
                rw [c.nodes_eq] at hnd_c
                exact (List.nodup_cons.mp hnd_c).1 (hxc ▸ hx)
              · exact forestNodes_nodup_disjoint hnd_cs hT₁ hc (Ne.symm hcT) hx_in_T
                  (hxc ▸ c.root_mem_nodes)
            have hlr := hlr' x hx_mem hx_ne_v hx_not_sib
            exact ⟨hpar'.2.2 x hx_mem hx_ne_v, hlr.1, hlr.2, Iff.rfl⟩
        · rw [List.mem_singleton.mp hT₂]
          refine (ValidSubtree.mk hin₂ hm₂ hd₂ hchild₂ hpar₂ hprio₂ hrank₂ hsub₂).frame
            (fun x hx => ?_) (fun x hx => ?_)
          · have hx_mem : x ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
              List.mem_append_right _ hx
            have hx_ne_u : x ≠ u := fun e =>
              hdisj_all u List.mem_cons_self x hx e.symm
            have hu_x := hunch x hx_mem
            exact ⟨hu_x.1, hu_x.2.1, hdeg'.2 x hx_mem hx_ne_u, hchild'.2 x hx_mem hx_ne_u,
              hu_x.2.2⟩
          · have hx_in_2 : x ∈ v :: forestNodes cs₂ := List.mem_cons_of_mem v hx
            have hx_mem : x ∈ (FHTree.node u cs₁).nodes ++ (FHTree.node v cs₂).nodes :=
              List.mem_append_right _ hx_in_2
            have hx_ne_v : x ≠ v := fun e => hv_not_desc₂ (e ▸ hx)
            have hx_not_sib : ∀ c ∈ cs₁, x ≠ c.root := fun c hc e =>
              hdisj_all c.root
                (List.mem_cons_of_mem u (mem_forestNodes_iff.mpr ⟨c, hc, c.root_mem_nodes⟩))
                x hx_in_2 e.symm
            have hlr := hlr' x hx_mem hx_ne_v hx_not_sib
            exact ⟨hpar'.2.2 x hx_mem hx_ne_v, hlr.1, hlr.2, Iff.rfl⟩

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
