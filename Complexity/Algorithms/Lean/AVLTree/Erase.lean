/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.AVLTree.Basic
public import Complexity.Algorithms.Lean.SearchTree.Erase

/-!
# Rebalancing deletion for AVL binary search trees

Deletion follows the search path to the target key. A matching node with an empty right child is
replaced by its left child; otherwise its leftmost right-subtree key is detached via rebalancing
`splitMin` and promoted, with `balance` restoring the `±1` sibling-height invariant at every
ancestor along the root-to-detached-node path.

Unlike [Cormen et al., Problem 13-3][CLRS2009], which covers the AVL invariant, Fibonacci height
bound, `balance`, and `insert`, this module extends the same `balance` combinator to
successor-splice deletion so that `AVLTree` supports the full `Cslib.OrderedSet.spec` interface
including `Op.erase` and `extractMin`.

## Main definitions

* `splitMin`: detach the minimum key of a nonempty subtree while rebalancing ancestors.
* `glue`: join the two children of a deleted node with rebalancing.
* `erase`: delete a key from an AVL tree while preserving `Valid`.
* `eraseVisits`: internal-node visits along the search and `splitMin` path.

## Main results

* `elements_erase`: `elements (erase x t) = (elements t).erase x` on ordered trees.
* `valid_erase`: `erase` preserves full AVL validity (`Ordered`, `HeightConsistent`, `Balanced`).
* `cachedHeight_erase_bounds`: deletion shrinks height by at most `1` and never increases height.
* `erase_eq_of_notMem`: deleting an absent key from a valid AVL tree leaves the tree unchanged.
* `searchVisits_le_eraseVisits`, `eraseVisits_le_cachedHeight`: deletion pays at least the downward
  search visits and visits at most `t.cachedHeight` path nodes.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 12 and Problem 13-3][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.AVLTree

section Shape

variable {α : Type*}

/-- Detach the leftmost key of `.node a _ l r`, rebalancing ancestors on the way back up. -/
@[expose] def splitMin (a : α) : AVLTree α → AVLTree α → α × AVLTree α
  | .nil, r => (a, r)
  | .node b _ ll lr, r =>
      let res := splitMin b ll lr
      (res.1, balance a res.2 r)

/-- Join the two children of a deleted node by promoting the minimum of `r` (when nonempty) and
rebalancing. -/
@[expose] def glue (l : AVLTree α) : AVLTree α → AVLTree α
  | .nil => l
  | .node b _ rl rr =>
      let res := splitMin b rl rr
      balance res.1 l res.2

end Shape

variable {α : Type*} [LinearOrder α]

/-- Delete `x` from `t`, rebalancing ancestors along the search path. -/
@[expose] def erase (x : α) : AVLTree α → AVLTree α
  | .nil => .nil
  | .node a _ l r =>
      if x < a then balance a (erase x l) r
      else if a < x then balance a l (erase x r)
      else glue l r

private theorem elements_splitMin (a : α) (ah : ℕ) (l r : AVLTree α) :
    elements (.node a ah l r) =
      Insert.insert (splitMin a l r).1 (elements (splitMin a l r).2) := by
  induction l generalizing a ah r with
  | nil => simp [splitMin]
  | node b bh ll lr ihl _ =>
    ext y
    have h := Finset.ext_iff.mp (ihl b bh lr) y
    simp only [splitMin, elements_balance, mem_elements_node, Finset.mem_insert,
      Finset.mem_union] at h ⊢
    tauto

private theorem elements_glue (l r : AVLTree α) :
    elements (glue l r) = elements l ∪ elements r := by
  cases r with
  | nil => simp [glue]
  | node b bh rl rr =>
    ext y
    have h := Finset.ext_iff.mp (elements_splitMin b bh rl rr) y
    simp only [glue, elements_balance, mem_elements_node, Finset.mem_insert,
      Finset.mem_union] at h ⊢
    tauto

private theorem valid_and_height_splitMin {a : α} {h : ℕ} {l r : AVLTree α}
    (ht : Valid (.node a h l r)) :
    Valid (splitMin a l r).2 ∧
      (∀ y ∈ elements (splitMin a l r).2, (splitMin a l r).1 < y) ∧
      (splitMin a l r).2.cachedHeight ≤ h ∧
      h ≤ (splitMin a l r).2.cachedHeight + 1 := by
  induction l generalizing a h r with
  | nil =>
    obtain ⟨⟨_, hor, _, ha_r⟩, ⟨hh, _, hcr⟩, ⟨_, hrl, _, hbr⟩⟩ := ht
    simp only [splitMin]
    simp only [cachedHeight_nil] at hh hrl
    exact ⟨⟨hor, hcr, hbr⟩, ha_r, by omega, by omega⟩
  | node b bh ll lr ihl _ =>
    obtain ⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    obtain ⟨⟨hol', hcl', hbl'⟩, hlt, hhi_l, hlo_l⟩ := ihl ⟨hol, hcl, hbl⟩
    simp only [cachedHeight_node] at hh hlr hrl
    have hm_mem : (splitMin b ll lr).1 ∈ elements (.node b bh ll lr) := by
      rw [elements_splitMin]
      exact Finset.mem_insert_self _ _
    have hm : (splitMin b ll lr).1 < a := hl_a _ hm_mem
    have ho' : Ordered (.node a 0 (splitMin b ll lr).2 r) := by
      refine ⟨hol', hor, ?_, ha_r⟩
      intro y hy
      have hy_mem : y ∈ elements (.node b bh ll lr) := by
        rw [elements_splitMin]
        exact Finset.mem_insert_of_mem hy
      exact hl_a y hy_mem
    obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
      balanced_and_height_balance a hcl' hcr hbl' hbr (by omega) (by omega)
    simp only [splitMin]
    refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl' hcr, hb_bal⟩, ?_, ?_, ?_⟩
    · intro y hy
      rw [elements_balance] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hm
      · rcases Finset.mem_union.mp hy with hy | hy
        · exact hlt y hy
        · exact lt_trans hm (ha_r y hy)
    · omega
    · by_cases hbal1 : r.cachedHeight ≤ (splitMin b ll lr).2.cachedHeight + 1
      · have heq := hb_eq (by omega) hbal1
        omega
      · omega

private theorem valid_and_height_glue {a : α} {h : ℕ} {l r : AVLTree α}
    (ht : Valid (.node a h l r)) :
    Valid (glue l r) ∧
      (glue l r).cachedHeight ≤ h ∧
      h ≤ (glue l r).cachedHeight + 1 := by
  cases r with
  | nil =>
    obtain ⟨⟨hol, _, _, _⟩, ⟨hh, hcl, _⟩, ⟨hlr, _, hbl, _⟩⟩ := ht
    simp only [glue]
    simp only [cachedHeight_nil] at hh hlr
    exact ⟨⟨hol, hcl, hbl⟩, by omega, by omega⟩
  | node b bh rl rr =>
    obtain ⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    obtain ⟨⟨hor', hcr', hbr'⟩, hlt, hhi_r, hlo_r⟩ :=
      valid_and_height_splitMin ⟨hor, hcr, hbr⟩
    simp only [cachedHeight_node] at hh hlr hrl
    have ham_mem : (splitMin b rl rr).1 ∈ elements (.node b bh rl rr) := by
      rw [elements_splitMin]
      exact Finset.mem_insert_self _ _
    have ham : a < (splitMin b rl rr).1 := ha_r _ ham_mem
    have ho' : Ordered (.node (splitMin b rl rr).1 0 l (splitMin b rl rr).2) :=
      ⟨hol, hor', fun y hy => lt_trans (hl_a y hy) ham, hlt⟩
    obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
      balanced_and_height_balance (splitMin b rl rr).1 hcl hcr' hbl hbr' (by omega) (by omega)
    simp only [glue]
    refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl hcr', hb_bal⟩, ?_, ?_⟩
    · omega
    · by_cases hbal1 : l.cachedHeight ≤ (splitMin b rl rr).2.cachedHeight + 1
      · have heq := hb_eq hbal1 (by omega)
        omega
      · omega

/-- Deletion removes `x` from the represented `Finset α` (including when `x` was absent). -/
@[simp]
theorem elements_erase {t : AVLTree α} (ht : Ordered t) (x : α) :
    elements (erase x t) = (elements t).erase x := by
  induction t with
  | nil => rfl
  | node a h l r ihl ihr =>
    obtain ⟨hol, hor, hl_a, ha_r⟩ := ht
    simp only [erase]
    split <;> rename_i hxa
    · ext y
      simp only [elements_balance, elements_node, ihl hol, Finset.mem_insert, Finset.mem_union,
        Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨hyx, hy⟩ | hy)
        · exact ⟨ne_of_gt hxa, Or.inl rfl⟩
        · exact ⟨hyx, Or.inr (Or.inl hy)⟩
        · exact ⟨fun heq => lt_asymm hxa (heq ▸ ha_r y hy), Or.inr (Or.inr hy)⟩
      · rintro ⟨hyx, rfl | hy | hy⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hyx, hy⟩)
        · exact Or.inr (Or.inr hy)
    · split <;> rename_i hax
      · ext y
        simp only [elements_balance, elements_node, ihr hor, Finset.mem_insert, Finset.mem_union,
          Finset.mem_erase]
        constructor
        · rintro (rfl | hy | ⟨hyx, hy⟩)
          · exact ⟨ne_of_lt hax, Or.inl rfl⟩
          · exact ⟨fun heq => lt_asymm hax (heq ▸ hl_a y hy), Or.inr (Or.inl hy)⟩
          · exact ⟨hyx, Or.inr (Or.inr hy)⟩
        · rintro ⟨hyx, rfl | hy | hy⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr ⟨hyx, hy⟩)
      · have heq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        subst heq
        have hx_notMem : x ∉ elements l ∪ elements r := by
          intro hm
          rcases Finset.mem_union.mp hm with hm | hm
          · exact lt_irrefl x (hl_a x hm)
          · exact lt_irrefl x (ha_r x hm)
        rw [elements_glue, elements_node, Finset.erase_insert hx_notMem]

private theorem valid_and_height_erase {t : AVLTree α} (ht : Valid t) (x : α) :
    Valid (erase x t) ∧
      (erase x t).cachedHeight ≤ t.cachedHeight ∧
      t.cachedHeight ≤ (erase x t).cachedHeight + 1 := by
  induction t with
  | nil => exact ⟨valid_nil, Nat.le_refl 0, Nat.zero_le 1⟩
  | node a h l r ihl ihr =>
    have hnode := ht
    obtain ⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    simp only [erase]
    split <;> rename_i hxa
    · obtain ⟨⟨hol', hcl', hbl'⟩, hhi, hlo⟩ := ihl ⟨hol, hcl, hbl⟩
      have ho' : Ordered (.node a 0 (erase x l) r) := by
        refine ⟨hol', hor, ?_, ha_r⟩
        intro y hy
        have hy' : y ∈ elements (erase x l) := hy
        rw [elements_erase hol] at hy'
        exact hl_a y (Finset.mem_of_mem_erase hy')
      obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
        balanced_and_height_balance a hcl' hcr hbl' hbr (by omega) (by omega)
      refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl' hcr, hb_bal⟩, ?_, ?_⟩
      · simp only [cachedHeight_node]
        omega
      · simp only [cachedHeight_node]
        by_cases hbal1 : r.cachedHeight ≤ (erase x l).cachedHeight + 1
        · have heq := hb_eq (by omega) hbal1
          omega
        · omega
    · split <;> rename_i hax
      · obtain ⟨⟨hor', hcr', hbr'⟩, hhi, hlo⟩ := ihr ⟨hor, hcr, hbr⟩
        have ho' : Ordered (.node a 0 l (erase x r)) := by
          refine ⟨hol, hor', hl_a, ?_⟩
          intro y hy
          have hy' : y ∈ elements (erase x r) := hy
          rw [elements_erase hor] at hy'
          exact ha_r y (Finset.mem_of_mem_erase hy')
        obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
          balanced_and_height_balance a hcl hcr' hbl hbr' (by omega) (by omega)
        refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl hcr', hb_bal⟩, ?_, ?_⟩
        · simp only [cachedHeight_node]
          omega
        · simp only [cachedHeight_node]
          by_cases hbal1 : l.cachedHeight ≤ (erase x r).cachedHeight + 1
          · have heq := hb_eq hbal1 (by omega)
            omega
          · omega
      · exact valid_and_height_glue hnode

/-- `erase` preserves full AVL validity (`Ordered`, `HeightConsistent`, and `Balanced`). -/
theorem valid_erase {t : AVLTree α} (ht : Valid t) (x : α) : Valid (erase x t) :=
  (valid_and_height_erase ht x).1

/-- Deletion shrinks cached height by at most `1` and never increases height. -/
theorem cachedHeight_erase_bounds {t : AVLTree α} (ht : Valid t) (x : α) :
    (erase x t).cachedHeight ≤ t.cachedHeight ∧
      t.cachedHeight ≤ (erase x t).cachedHeight + 1 :=
  (valid_and_height_erase ht x).2

/-- Deleting an absent key from a valid AVL tree leaves the entire tree unchanged. -/
theorem erase_eq_of_notMem {t : AVLTree α} (ht : Valid t) {x : α} (hx : x ∉ elements t) :
    erase x t = t := by
  induction t with
  | nil => rfl
  | node a h l r ihl ihr =>
    obtain ⟨⟨hol, hor, _, _⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    simp only [mem_elements_node, not_or] at hx
    obtain ⟨hxa, hxl, hxr⟩ := hx
    simp only [erase]
    split <;> rename_i hlt
    · rw [ihl ⟨hol, hcl, hbl⟩ hxl]
      exact balance_eq_node hh hlr hrl
    · split <;> rename_i hgt
      · rw [ihr ⟨hor, hcr, hbr⟩ hxr]
        exact balance_eq_node hh hlr hrl
      · exact absurd (le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)) hxa

/-- Internal-node visits of `erase`: the downward search path plus leftmost `splitMin` descent in
the matched node's right subtree. Rebalancing reads of `O(1)` off-path sibling/nephew cached
heights at visited ancestors are not counted separately. -/
@[expose] def eraseVisits (x : α) (t : AVLTree α) : ℕ :=
  SearchTree.eraseVisits x t.toBinaryTree

/-- Deletion pays for the downward search path and possibly a `splitMin` descent on top. -/
theorem searchVisits_le_eraseVisits (x : α) (t : AVLTree α) :
    searchVisits x t ≤ eraseVisits x t :=
  SearchTree.searchVisits_le_eraseVisits x t.toBinaryTree

/-- Deletion visits at most `t.cachedHeight` internal path nodes. -/
theorem eraseVisits_le_cachedHeight {t : AVLTree α} (hc : HeightConsistent t) (x : α) :
    eraseVisits x t ≤ t.cachedHeight := by
  rw [cachedHeight_eq_height hc]
  exact SearchTree.eraseVisits_le_height x t.toBinaryTree

end Cslib.Algorithms.Lean.AVLTree
