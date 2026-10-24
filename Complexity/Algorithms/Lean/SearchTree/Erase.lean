/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.SearchTree.Cost

/-!
# Deletion from unbalanced binary search trees

Deletion follows the search path to the key. A matching node with an empty right subtree is
replaced by its left subtree; otherwise its key is replaced by the leftmost key of the right
subtree, which is detached from there. This is the successor-splicing deletion of
[Cormen et al., Chapter 12][CLRS2009], except that a node with an empty left subtree is also
rebuilt around its successor rather than replaced by its right subtree. Deleting an absent key
leaves the tree unchanged.

## Main definitions

* `splitMin`: detach the leftmost key of a nonempty tree.
* `glue`: join the two subtrees of a deleted node.
* `erase`: delete a key.
* `eraseVisits`: internal-node visits of deletion, in the model of the companion cost module.

## Main results

* `elements_erase`, `ordered_erase`: deletion has set semantics and preserves the invariant.
* `erase_eq_of_notMem`: deleting an absent key preserves the entire tree.
* `searchVisits_le_eraseVisits`: deletion walks the search path of `contains` and `insert`, and
  then at most the left spine of the matched node's right subtree (`minimumVisits`).
* `eraseVisits_le_height`, `height_erase_le`: deletion visits at most the initial height and
  never increases the height.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*, Chapter 12][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.SearchTree

section Shape

variable {α : Type*}

/-- Detach the leftmost key of the nonempty tree `.node a l r`, returning it with the rest. -/
def splitMin (a : α) : BinaryTree α → BinaryTree α → α × BinaryTree α
  | .nil, r => (a, r)
  | .node b ll lr, r => ((splitMin b ll lr).1, .node a (splitMin b ll lr).2 r)

/-- Join the subtrees of a deleted node, promoting the leftmost key of the right subtree. -/
def glue (l : BinaryTree α) : BinaryTree α → BinaryTree α
  | .nil => l
  | .node b rl rr => .node (splitMin b rl rr).1 l (splitMin b rl rr).2

private theorem height_splitMin_le (a : α) (l r : BinaryTree α) :
    (splitMin a l r).2.height ≤ (BinaryTree.node a l r).height := by
  induction l generalizing a r with
  | nil => simp only [splitMin, BinaryTree.height]; omega
  | node b ll lr il _ =>
    have := il b lr
    simp only [splitMin, BinaryTree.height] at this ⊢
    omega

private theorem height_glue_le (a : α) (l r : BinaryTree α) :
    (glue l r).height ≤ (BinaryTree.node a l r).height := by
  cases r with
  | nil => simp only [glue, BinaryTree.height]; omega
  | node b rl rr =>
    have := height_splitMin_le b rl rr
    simp only [glue, BinaryTree.height] at this ⊢
    omega

end Shape

variable {α : Type*} [LinearOrder α]

/-- Delete `x` along its search path; a matching node is replaced by `glue` of its subtrees. -/
def erase (x : α) : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node a l r =>
      if x < a then .node a (erase x l) r
      else if a < x then .node a l (erase x r) else glue l r

/-- The detached key together with the remaining tree represents the original set. -/
private theorem elements_splitMin (a : α) (l r : BinaryTree α) :
    elements (.node a l r) = Insert.insert (splitMin a l r).1 (elements (splitMin a l r).2) := by
  induction l generalizing a r with
  | nil => simp [splitMin, elements]
  | node b ll lr il _ =>
    ext y
    have := Finset.ext_iff.mp (il b lr) y
    simp only [splitMin, mem_elements_node, Finset.mem_insert] at this ⊢
    tauto

/-- Gluing loses only the key of the deleted node. -/
private theorem elements_glue (l r : BinaryTree α) :
    elements (glue l r) = elements l ∪ elements r := by
  cases r with
  | nil => simp [glue, elements]
  | node b rl rr =>
    rw [elements_splitMin b rl rr, Finset.union_insert]
    simp [glue, elements]

/-- In an ordered tree the detached key is the least, and the remaining tree stays ordered. -/
private theorem ordered_splitMin {a : α} {l r : BinaryTree α} (ht : Ordered (.node a l r)) :
    Ordered (splitMin a l r).2 ∧ ∀ y ∈ elements (splitMin a l r).2, (splitMin a l r).1 < y := by
  induction l generalizing a r with
  | nil => exact ⟨ht.2.1, ht.2.2.2⟩
  | node b ll lr il _ =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    obtain ⟨ho, hlt⟩ := il hl
    have he := elements_splitMin b ll lr
    have hm : (splitMin b ll lr).1 < a :=
      hla _ (he ▸ Finset.mem_insert_self _ _)
    refine ⟨⟨ho, hr, fun y hy => hla y (he ▸ Finset.mem_insert_of_mem hy), har⟩, ?_⟩
    intro y hy
    rcases mem_elements_node.mp hy with rfl | hy | hy
    · exact hm
    · exact hlt y hy
    · exact lt_trans hm (har y hy)

/-- Gluing the subtrees of an ordered node yields an ordered tree. -/
private theorem ordered_glue {a : α} {l r : BinaryTree α} (ht : Ordered (.node a l r)) :
    Ordered (glue l r) := by
  obtain ⟨hl, hr, hla, har⟩ := ht
  cases r with
  | nil => exact hl
  | node b rl rr =>
    obtain ⟨ho, hlt⟩ := ordered_splitMin hr
    have hm : a < (splitMin b rl rr).1 :=
      har _ (elements_splitMin b rl rr ▸ Finset.mem_insert_self _ _)
    exact ⟨hl, ho, fun y hy => lt_trans (hla y hy) hm, hlt⟩

/-- Deletion removes exactly the requested key, even when it was absent. -/
theorem elements_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (erase x t) = (elements t).erase x := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [erase]
    split <;> rename_i hx
    · ext y
      simp only [elements, il hl, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hyx, hy⟩ | hy)
        · exact ⟨ne_of_gt hx, Or.inl rfl⟩
        · exact ⟨hyx, Or.inr (Or.inl hy)⟩
        · exact ⟨fun h => lt_asymm hx (h ▸ har y hy), Or.inr (Or.inr hy)⟩
      · rintro ⟨hyx, rfl | hy | hy⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hyx, hy⟩)
        · exact Or.inr (Or.inr hy)
    · split <;> rename_i ha
      · ext y
        simp only [elements, ir hr, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (rfl | hy | ⟨hyx, hy⟩)
          · exact ⟨ne_of_lt ha, Or.inl rfl⟩
          · exact ⟨fun h => lt_asymm ha (h ▸ hla y hy), Or.inr (Or.inl hy)⟩
          · exact ⟨hyx, Or.inr (Or.inr hy)⟩
        · rintro ⟨hyx, rfl | hy | hy⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr ⟨hyx, hy⟩)
      · have he : x = a := le_antisymm (le_of_not_gt ha) (le_of_not_gt hx)
        subst he
        have hx : x ∉ elements l ∪ elements r := by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact lt_irrefl x (hla x h)
          · exact lt_irrefl x (har x h)
        rw [elements_glue, elements, Finset.erase_insert hx]

/-- The binary-search-tree invariant survives deletion. -/
theorem ordered_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (erase x t) := by
  induction t with
  | nil => trivial
  | node a l r il ir =>
    have hn := ht
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [erase]
    split
    · refine ⟨il hl, hr, fun y hy => hla y ?_, har⟩
      rw [elements_erase hl] at hy
      exact Finset.mem_of_mem_erase hy
    · split
      · refine ⟨hl, ir hr, hla, fun y hy => har y ?_⟩
        rw [elements_erase hr] at hy
        exact Finset.mem_of_mem_erase hy
      · exact ordered_glue hn

/-- Deleting an absent key preserves the entire tree, not just its represented set. -/
theorem erase_eq_of_notMem {t : BinaryTree α} {x : α} (hx : x ∉ elements t) : erase x t = t := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [mem_elements_node, not_or] at hx
    obtain ⟨hxa, hxl, hxr⟩ := hx
    simp only [erase]
    split <;> rename_i h
    · rw [il hxl]
    · split <;> rename_i h'
      · rw [ir hxr]
      · exact (hxa (le_antisymm (le_of_not_gt h') (le_of_not_gt h))).elim

/-- Internal-node visits of deletion: the search path, then leftmost descent in the right
subtree of a matching node. -/
def eraseVisits (x : α) : BinaryTree α → Nat
  | .nil => 0
  | .node a l r =>
      1 + if x < a then eraseVisits x l else if a < x then eraseVisits x r else minimumVisits r

/-- Deletion pays for the full search path and possibly a successor descent on top. -/
theorem searchVisits_le_eraseVisits (x : α) (t : BinaryTree α) :
    searchVisits x t ≤ eraseVisits x t := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [searchVisits, eraseVisits]
    split
    · omega
    · split <;> omega

theorem eraseVisits_le_height (x : α) (t : BinaryTree α) :
    eraseVisits x t ≤ t.height := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    have := minimumVisits_le_height r
    simp only [eraseVisits, BinaryTree.height]
    split
    · omega
    · split <;> omega

/-- Unlike insertion, deletion never increases the height. -/
theorem height_erase_le (x : α) (t : BinaryTree α) : (erase x t).height ≤ t.height := by
  induction t with
  | nil => rfl
  | node a l r il ir =>
    simp only [erase]
    split
    · simp only [BinaryTree.height]
      omega
    · split
      · simp only [BinaryTree.height]
        omega
      · exact height_glue_le a l r

end Cslib.Algorithms.Lean.SearchTree
