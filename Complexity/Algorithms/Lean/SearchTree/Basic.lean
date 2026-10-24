/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Tree.Basic
public import Complexity.Foundations.Data.OrderedSet

/-!
# Unbalanced binary search trees

An ordinary binary search tree reuses Mathlib's `BinaryTree`. Keys strictly smaller than the
root occur on the left, larger keys on the right. Inserting a duplicate leaves the tree unchanged.
These are the textbook search and insertion algorithms of [Cormen et al., Chapter 12][CLRS2009].

## Main definitions

* `elements`: the finite set represented by a tree.
* `Ordered`: the strict binary-search-tree invariant.
* `contains`, `insert`, `minimum`, `successor`: executable search-tree operations.

## Main results

* `contains_eq_true`: membership is exactly finite-set membership.
* `elements_insert`, `ordered_insert`: insertion has set semantics and preserves the invariant.
* `minimum_spec`, `successor_spec`: queries return the least eligible key, or `none`.

Trees are not balanced. Cost bounds in the companion module depend on their actual height.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*, Chapter 12][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.SearchTree

open Cslib.OrderedSet

variable {α : Type*} [LinearOrder α]

/-- The finite set of keys stored at internal nodes. -/
def elements : BinaryTree α → Finset α
  | .nil => ∅
  | .node a l r => insert a (elements l ∪ elements r)

/-- Strict subtree separation rules out duplicate keys. -/
def Ordered : BinaryTree α → Prop
  | .nil => True
  | .node a l r => Ordered l ∧ Ordered r ∧
      (∀ x ∈ elements l, x < a) ∧ (∀ x ∈ elements r, a < x)

/-- Follow a single search path; no subtree is scanned. -/
def contains (x : α) : BinaryTree α → Bool
  | .nil => false
  | .node a l r => if x < a then contains x l else if a < x then contains x r else true

/-- Insert at the first empty child on the search path; equality preserves the existing node. -/
def insert (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | .node a l r =>
      if x < a then .node a (insert x l) r
      else if a < x then .node a l (insert x r) else .node a l r

/-- Follow left children to find the least key. -/
def minimum : BinaryTree α → Option α
  | .nil => none
  | .node a l _ => (minimum l).or (some a)

/-- The least stored key strictly greater than `x`, including when `x` is absent. -/
def successor (x : α) : BinaryTree α → Option α
  | .nil => none
  | .node a l r => if x < a then (successor x l).or (some a) else successor x r

/-- Membership in a node's element set splits across the root key and the two subtrees. -/
@[simp] theorem mem_elements_node {x a : α} {l r : BinaryTree α} :
    x ∈ elements (.node a l r) ↔ x = a ∨ x ∈ elements l ∨ x ∈ elements r := by
  simp [elements]

/-- Search is correct for any shape satisfying the invariant. -/
theorem contains_eq_true {t : BinaryTree α} (ht : Ordered t) (x : α) :
    contains x t = true ↔ x ∈ elements t := by
  induction t with
  | nil => simp [contains, elements]
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [contains, mem_elements_node]
    split <;> rename_i hx
    · rw [il hl]
      constructor
      · exact fun h => Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact (ne_of_lt hx h).elim
        · exact h
        · exact (lt_asymm hx (har x h)).elim
    · split <;> rename_i ha
      · rw [ir hr]
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact (ne_of_gt ha h).elim
          · exact (lt_asymm ha (hla x h)).elim
          · exact h
      · have he : x = a := le_antisymm (le_of_not_gt ha) (le_of_not_gt hx)
        simp [he]

/-- Insertion adds exactly the requested key, even when it was already present. -/
theorem elements_insert (x : α) (t : BinaryTree α) :
    elements (insert x t) = Insert.insert x (elements t) := by
  induction t with
  | nil => simp [insert, elements]
  | node a l r il ir =>
    simp only [insert]
    split <;> rename_i hx
    · ext y
      simp [elements, il, or_left_comm]
    · split <;> rename_i ha
      · ext y
        simp [elements, ir, or_left_comm]
      · have he : x = a := le_antisymm (le_of_not_gt ha) (le_of_not_gt hx)
        simp [elements, he]

/-- The binary-search-tree invariant survives insertion. -/
theorem ordered_insert {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (insert x t) := by
  induction t with
  | nil => simp [insert, Ordered, elements]
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [insert]
    split <;> rename_i hx
    · refine ⟨il hl, hr, ?_, har⟩
      intro y hy
      rw [elements_insert, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hla y hy
    · split <;> rename_i ha
      · refine ⟨hl, ir hr, hla, ?_⟩
        intro y hy
        rw [elements_insert, Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact ha
        · exact har y hy
      · exact ⟨hl, hr, hla, har⟩

/-- Re-inserting a present key preserves the entire tree, not just its represented set. -/
theorem insert_eq_self {t : BinaryTree α} (ht : Ordered t) {x : α}
    (hx : x ∈ elements t) : insert x t = t := by
  induction t with
  | nil => simp [elements] at hx
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [insert]
    split <;> rename_i hxa
    · have hxl : x ∈ elements l := by
        rcases mem_elements_node.mp hx with h | h | h
        · exact (ne_of_lt hxa h).elim
        · exact h
        · exact (lt_asymm hxa (har x h)).elim
      rw [il hl hxl]
    · split <;> rename_i hax
      · have hxr : x ∈ elements r := by
          rcases mem_elements_node.mp hx with h | h | h
          · exact (ne_of_gt hax h).elim
          · exact (lt_asymm hax (hla x h)).elim
          · exact h
        rw [ir hr hxr]
      · rfl

/-- A strict search tree stores each represented key in exactly one node. -/
theorem card_elements {t : BinaryTree α} (ht : Ordered t) :
    (elements t).card = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    have hdis : Disjoint (elements l) (elements r) := by
      apply Finset.disjoint_left.mpr
      intro x hxl hxr
      exact lt_asymm (hla x hxl) (har x hxr)
    have ha : a ∉ elements l ∪ elements r := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact lt_irrefl a (hla a h)
      · exact lt_irrefl a (har a h)
    simp only [elements, Finset.card_insert_of_notMem ha,
      Finset.card_union_of_disjoint hdis, il hl, ir hr, BinaryTree.numNodes]

/-- Left descent returns the least element, with the empty case accounted for. -/
theorem minimum_spec {t : BinaryTree α} (ht : Ordered t) :
    LeastResult (elements t) (minimum t) := by
  induction t with
  | nil => rfl
  | node a l r il _ =>
    obtain ⟨hl, _, hla, har⟩ := ht
    have ih := il hl
    cases he : minimum l with
    | none =>
      simp only [he, LeastResult] at ih
      simp only [minimum, he, Option.or, LeastResult]
      refine ⟨by simp, ?_⟩
      intro b hb
      rcases mem_elements_node.mp hb with rfl | hb | hb
      · exact le_rfl
      · simp [ih] at hb
      · exact (har b hb).le
    | some b =>
      simp only [he, LeastResult] at ih
      simp only [minimum, he, Option.or, LeastResult]
      refine ⟨by simp [ih.1], ?_⟩
      intro c hc
      rcases mem_elements_node.mp hc with rfl | hc | hc
      · exact (hla b ih.1).le
      · exact ih.2 c hc
      · exact (lt_trans (hla b ih.1) (har c hc)).le

/-- Successor is strict and does not require the query itself to belong to the tree. -/
theorem successor_spec {t : BinaryTree α} (ht : Ordered t) (x : α) :
    LeastResult ((elements t).filter (x < ·)) (successor x t) := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [successor]
    split <;> rename_i hx
    · have ih := il hl
      cases he : successor x l with
      | none =>
        simp only [he, LeastResult] at ih
        simp only [Option.or, LeastResult]
        refine ⟨by simp [hx], ?_⟩
        intro b hb
        obtain ⟨hb, hxb⟩ := Finset.mem_filter.mp hb
        rcases mem_elements_node.mp hb with rfl | hb | hb
        · exact le_rfl
        · have : b ∈ (elements l).filter (x < ·) := Finset.mem_filter.mpr ⟨hb, hxb⟩
          simp [ih] at this
        · exact (har b hb).le
      | some b =>
        simp only [he, LeastResult] at ih
        simp only [Option.or, LeastResult]
        obtain ⟨hbl, hxb⟩ := Finset.mem_filter.mp ih.1
        refine ⟨by simp [hbl, hxb], ?_⟩
        intro c hc
        obtain ⟨hc, hxc⟩ := Finset.mem_filter.mp hc
        rcases mem_elements_node.mp hc with rfl | hc | hc
        · exact (hla b hbl).le
        · exact ih.2 c (Finset.mem_filter.mpr ⟨hc, hxc⟩)
        · exact (lt_trans (hla b hbl) (har c hc)).le
    · have he : (elements (.node a l r)).filter (x < ·) =
          (elements r).filter (x < ·) := by
        ext b
        simp only [Finset.mem_filter, mem_elements_node]
        constructor
        · rintro ⟨rfl | hb | hb, hxb⟩
          · exact (hx hxb).elim
          · exact (hx (lt_trans hxb (hla b hb))).elim
          · exact ⟨hb, hxb⟩
        · rintro ⟨hb, hxb⟩
          exact ⟨Or.inr (Or.inr hb), hxb⟩
      rw [he]
      exact ir hr

end Cslib.Algorithms.Lean.SearchTree
