/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Chain
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Chains of matching entry and exit colors

Identity-colored seams can be removed when joining paths, including empty interiors.
For additive colors, the differences along an exact path telescope to its endpoint difference.
-/

public section

namespace List

variable {β : Type*}

/-- Deleting an identity entry preserves a chain of matching entry/exit colors. -/
theorem isChain_remove_identity {left right : List (β × β)} {b : β}
    (h : IsChain (fun p q : β × β => p.2 = q.1) (left ++ (b, b) :: right)) :
    IsChain (fun p q : β × β => p.2 = q.1) (left ++ right) := by
  induction left with
  | nil => exact h.tail
  | cons a left ih =>
    cases left with
    | nil =>
      cases right with
      | nil => exact IsChain.singleton a
      | cons c right =>
        simp only [cons_append, nil_append, isChain_cons_cons] at h ⊢
        exact ⟨h.1.trans h.2.1, h.2.2⟩
    | cons c left =>
      simp only [cons_append, isChain_cons_cons] at h ⊢
      exact ⟨h.1, ih h.2⟩

/-- Concatenate two exact corner-color paths and erase their common identity seam.
Either interior word may be empty. -/
theorem isChain_colorPairs_append {left right : List (β × β)} {a b c : β}
    (hl : IsChain (fun p q : β × β => p.2 = q.1) ((a, a) :: left ++ [(b, b)]))
    (hr : IsChain (fun p q : β × β => p.2 = q.1) ((b, b) :: right ++ [(c, c)])) :
    IsChain (fun p q : β × β => p.2 = q.1)
      ((a, a) :: (left ++ right) ++ [(c, c)]) := by
  have h := hl.append_overlap hr (cons_ne_nil (b, b) [])
  simp only [append_assoc, cons_append, nil_append] at h
  simpa only [append_assoc, cons_append, nil_append] using
    (isChain_remove_identity (b := b) (left := (a, a) :: left)
      (right := right ++ [(c, c)]) h)

/-- Substitute complete entry/exit paths into a path of matching endpoint pairs. Empty
interiors are allowed in any positions, including every substituted block. -/
theorem isChain_colorPairs_flatMap {α : Type*} (outer : List α) (blocks : α → List (β × β))
    (entry exit : α → β) {a b : β}
    (houter : IsChain (fun p q : β × β => p.2 = q.1)
      ((a, a) :: outer.map (fun s => (entry s, exit s)) ++ [(b, b)]))
    (hblocks : ∀ s ∈ outer, IsChain (fun p q : β × β => p.2 = q.1)
      ((entry s, entry s) :: blocks s ++ [(exit s, exit s)])) :
    IsChain (fun p q : β × β => p.2 = q.1)
      ((a, a) :: outer.flatMap blocks ++ [(b, b)]) := by
  induction outer generalizing a with
  | nil => simpa only [map_nil, flatMap_nil] using houter
  | cons s outer ih =>
    simp only [map_cons, cons_append, isChain_cons_cons] at houter
    have hrest : IsChain (fun p q : β × β => p.2 = q.1)
        ((exit s, exit s) :: outer.map (fun s => (entry s, exit s)) ++ [(b, b)]) := by
      simpa only [cons_append, isChain_cons] using houter.2
    have htail := ih hrest (fun s hs => hblocks s (mem_cons_of_mem _ hs))
    have h := isChain_colorPairs_append (hblocks s (mem_cons_self)) htail
    simpa only [flatMap_cons, houter.1] using h

/-- Differences along matching entry/exit pairs telescope to the endpoint difference,
including a path with no interior pairs. -/
theorem sum_sub_eq_of_isChain_colorPairs [AddCommGroup β] {word : List (β × β)} {a b : β}
    (h : IsChain (fun p q : β × β => p.2 = q.1) ((a, a) :: word ++ [(b, b)])) :
    (word.map fun p => p.2 - p.1).sum = b - a := by
  induction word generalizing a with
  | nil =>
    have he : a = b := by
      simpa only [cons_append, nil_append, isChain_pair] using h
    simp [he]
  | cons p word ih =>
    simp only [cons_append, isChain_cons_cons] at h
    have ht : IsChain (fun p q : β × β => p.2 = q.1)
        ((p.2, p.2) :: word ++ [(b, b)]) := by
      simpa only [cons_append, isChain_cons] using h.2
    rw [map_cons, sum_cons, ih ht, h.1]
    exact sub_add_sub_cancel' _ _ _

end List
