/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib Data/List)

public import CslibFrontier.Init
import Mathlib.Data.List.Infix

/-!
# Literal positions in a flat-mapped list

A position in a selected block is shifted by the length of the actual preceding blocks.
The intervals are bounded, disjoint and exhaustive, even when some blocks are empty or
values repeat. The getter retains the selected occurrence rather than locating its value.
-/

public section

namespace List

variable {α β : Type*}

/-- The selected block's actual prefix offset gives a valid flat-list position. -/
theorem flatMap_prefix_add_lt (l : List α) (f : α → List β) {i j : ℕ}
    (hi : i < l.length) (hj : j < (f l[i]).length) :
    ((l.take i).flatMap f).length + j < (l.flatMap f).length := by
  have hp := ((take_prefix (i + 1) l).flatMap f).length_le
  rw [take_succ_eq_append_getElem hi, flatMap_append, flatMap_singleton, length_append] at hp
  omega

/-- Reading a flat-list position at its prefix offset reads the original selected block. -/
theorem getElem_flatMap_prefix_add (l : List α) (f : α → List β) {i j : ℕ}
    (hi : i < l.length) (hj : j < (f l[i]).length) :
    (l.flatMap f)[((l.take i).flatMap f).length + j]'(flatMap_prefix_add_lt l f hi hj) =
      (f l[i])[j] := by
  have hp := (take_prefix (i + 1) l).flatMap f
  have hb : ((l.take i).flatMap f).length + j < ((l.take (i + 1)).flatMap f).length := by
    rw [take_succ_eq_append_getElem hi, flatMap_append, flatMap_singleton, length_append]
    omega
  rw [← hp.getElem hb]
  simp only [take_succ_eq_append_getElem hi, flatMap_append, flatMap_singleton,
    getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Taking a prefix through a selected block retains all earlier blocks and precisely the
selected local prefix. The selected block may be empty. -/
theorem take_flatMap_prefix_add (l : List α) (f : α → List β) {i j : ℕ}
    (hi : i < l.length) (hj : j ≤ (f l[i]).length) :
    (l.flatMap f).take (((l.take i).flatMap f).length + j) =
      (l.take i).flatMap f ++ (f l[i]).take j := by
  have hp := (take_prefix (i + 1) l).flatMap f
  rw [take_succ_eq_append_getElem hi, flatMap_append, flatMap_singleton] at hp
  obtain ⟨suffix, he⟩ := hp
  rw [← he, append_assoc, take_append, Nat.add_sub_cancel_left]
  rw [take_of_length_le (Nat.le_add_right _ _), take_append_of_le_length hj]

/-- The interval of any earlier block ends before every position of a later block. -/
theorem flatMap_prefix_add_lt_of_lt (l : List α) (f : α → List β) {i j k q : ℕ}
    (hi : i < l.length) (hj : j < (f l[i]).length) (hik : i < k) :
    ((l.take i).flatMap f).length + j < ((l.take k).flatMap f).length + q := by
  have hp := ((take_prefix_take_left (l := l) (Nat.succ_le_of_lt hik)).flatMap f).length_le
  rw [take_succ_eq_append_getElem hi, flatMap_append, flatMap_singleton, length_append] at hp
  omega

/-- Flat positions retain their original block and local position, independently of values. -/
theorem flatMap_prefix_add_injective (l : List α) (f : α → List β)
    {i j k q : ℕ} (hi : i < l.length) (hj : j < (f l[i]).length)
    (hk : k < l.length) (hq : q < (f l[k]).length)
    (he : ((l.take i).flatMap f).length + j = ((l.take k).flatMap f).length + q) :
    i = k ∧ j = q := by
  have hik : i = k := by
    rcases lt_trichotomy i k with h | h | h
    · have := flatMap_prefix_add_lt_of_lt (q := q) l f hi hj h
      omega
    · exact h
    · have := flatMap_prefix_add_lt_of_lt (q := j) l f hk hq h
      omega
  exact ⟨hik, by subst k; omega⟩

/-- Every flat-list position lies in an actual block at its literal prefix offset.
Empty blocks supply no positions, and no distinctness assumption on values is used. -/
theorem exists_flatMap_prefix_add (l : List α) (f : α → List β) {index : ℕ}
    (hindex : index < (l.flatMap f).length) :
    ∃ (i : ℕ) (hi : i < l.length) (j : ℕ), j < (f l[i]).length ∧
      index = ((l.take i).flatMap f).length + j := by
  induction l generalizing index with
  | nil => simp at hindex
  | cons a l ih =>
    by_cases ha : index < (f a).length
    · exact ⟨0, by simp, index, ha, by simp⟩
    · have hb : index - (f a).length < (l.flatMap f).length := by
        simp only [flatMap_cons, length_append] at hindex
        omega
      obtain ⟨i, hi, j, hj, he⟩ := ih hb
      refine ⟨i + 1, by simpa only [length_cons] using Nat.succ_lt_succ hi, j, hj, ?_⟩
      simp only [take_succ_cons, flatMap_cons, length_append]
      omega

end List
