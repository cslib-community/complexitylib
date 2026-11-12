/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Log

/-!
# Bracketings of a list

A bracketing of a nonempty list is a way of grouping its entries by nested pairs of brackets: a
binary tree whose leaves, read from left to right, are the entries of the list
(`Cslib.Bracketing`). Every nonempty list of length `n` has a bracketing of height at most
`⌈lg n⌉` (`Cslib.Bracketing.exists_leaves_eq`), obtained by halving. Divide-and-conquer
arguments over a product of `n` factors in a fixed order go by induction on the height of the
subtrees of such a bracketing (`Cslib.Bracketing.subtrees`).

## Main definitions

* `Cslib.Bracketing`: binary trees with labelled leaves.
* `Cslib.Bracketing.leaves`, `Cslib.Bracketing.height`, `Cslib.Bracketing.subtrees`.

## Main results

* `Cslib.Bracketing.exists_leaves_eq`: a bracketing of height at most `⌈lg n⌉` of a list of
  length `n`.
* `Cslib.Bracketing.length_subtrees`: a bracketing of `n` entries has `2 n - 1` subtrees.
* `Cslib.Bracketing.sublist_leaves_of_mem_subtrees`: the leaves of a subtree form a sublist.
-/

@[expose] public section

namespace Cslib

/-- A bracketing: a binary tree with leaves labelled in `σ`. -/
inductive Bracketing (σ : Type*) where
  /-- A single entry. -/
  | leaf (i : σ) : Bracketing σ
  /-- Two bracketings side by side. -/
  | node (l r : Bracketing σ) : Bracketing σ

namespace Bracketing

variable {σ : Type*}

/-- The entries of a bracketing, from left to right. -/
def leaves : Bracketing σ → List σ
  | leaf i => [i]
  | node l r => l.leaves ++ r.leaves

/-- The height of a bracketing: the largest number of brackets around an entry. -/
def height : Bracketing σ → ℕ
  | leaf _ => 0
  | node l r => max l.height r.height + 1

/-- The subtrees of a bracketing, itself included. -/
def subtrees : Bracketing σ → List (Bracketing σ)
  | leaf i => [leaf i]
  | node l r => node l r :: (l.subtrees ++ r.subtrees)

theorem self_mem_subtrees : ∀ t : Bracketing σ, t ∈ t.subtrees
  | leaf _ => List.mem_singleton_self _
  | node _ _ => List.mem_cons_self

/-- The subtrees of a subtree are subtrees. -/
theorem subtrees_subset_of_mem : ∀ {t s : Bracketing σ}, s ∈ t.subtrees →
    s.subtrees ⊆ t.subtrees
  | leaf _, s, hs => by
    rw [List.mem_singleton.1 hs]
  | node l r, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact List.Subset.refl _
    · rcases List.mem_append.1 hs with h | h
      · exact fun x hx => List.mem_cons_of_mem _
          (List.mem_append_left _ (subtrees_subset_of_mem h hx))
      · exact fun x hx => List.mem_cons_of_mem _
          (List.mem_append_right _ (subtrees_subset_of_mem h hx))

/-- The two halves of a subtree are subtrees. -/
theorem mem_subtrees_of_node {t l r : Bracketing σ} (h : node l r ∈ t.subtrees) :
    l ∈ t.subtrees ∧ r ∈ t.subtrees :=
  ⟨subtrees_subset_of_mem h (List.mem_cons_of_mem _
      (List.mem_append_left _ l.self_mem_subtrees)),
    subtrees_subset_of_mem h (List.mem_cons_of_mem _
      (List.mem_append_right _ r.self_mem_subtrees))⟩

/-- A bracketing of `n` entries has `2 n - 1` subtrees. -/
theorem length_subtrees : ∀ t : Bracketing σ, t.subtrees.length + 1 = 2 * t.leaves.length
  | leaf _ => rfl
  | node l r => by
    have hl := l.length_subtrees
    have hr := r.length_subtrees
    simp only [subtrees, leaves, List.length_cons, List.length_append]
    omega

/-- The entries of a subtree form a sublist of the entries of the bracketing. -/
theorem sublist_leaves_of_mem_subtrees : ∀ {t s : Bracketing σ}, s ∈ t.subtrees →
    s.leaves.Sublist t.leaves
  | leaf _, s, hs => by
    rw [List.mem_singleton.1 hs]
  | node l r, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact List.Sublist.refl _
    · rcases List.mem_append.1 hs with h | h
      · exact (sublist_leaves_of_mem_subtrees h).trans (List.sublist_append_left _ _)
      · exact (sublist_leaves_of_mem_subtrees h).trans (List.sublist_append_right _ _)

/-- Every nonempty list of length `n` has a bracketing of height at most `⌈lg n⌉`. -/
theorem exists_leaves_eq (l : List σ) (hl : l ≠ []) :
    ∃ t : Bracketing σ, t.leaves = l ∧ t.height ≤ Nat.clog 2 l.length := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    subst h
    rcases Nat.lt_or_ge l.length 2 with h2 | h2
    · obtain ⟨i, rfl⟩ : ∃ i, l = [i] := List.length_eq_one_iff.1 (by
        have := List.length_pos_iff.2 hl
        omega)
      exact ⟨leaf i, rfl, Nat.zero_le _⟩
    · set k := (l.length + 1) / 2 with hk
      have hk1 : k < l.length := by omega
      have hk0 : 0 < k := by omega
      have htake : (l.take k).length = k := List.length_take_of_le hk1.le
      have hdrop : (l.drop k).length = l.length - k := List.length_drop
      obtain ⟨t₁, ht₁, hh₁⟩ := ih k hk1 (l.take k)
        (List.ne_nil_of_length_pos (by omega)) htake
      obtain ⟨t₂, ht₂, hh₂⟩ := ih (l.length - k) (by omega) (l.drop k)
        (List.ne_nil_of_length_pos (by omega)) hdrop
      refine ⟨node t₁ t₂, by rw [leaves, ht₁, ht₂, List.take_append_drop], ?_⟩
      have hclog : Nat.clog 2 l.length = Nat.clog 2 k + 1 := by
        rw [Nat.clog_of_two_le (le_refl 2) h2, hk]
        rfl
      rw [height, hclog]
      exact Nat.succ_le_succ (max_le hh₁ (hh₂.trans (Nat.clog_mono_right 2 (by omega))))

end Bracketing

end Cslib
