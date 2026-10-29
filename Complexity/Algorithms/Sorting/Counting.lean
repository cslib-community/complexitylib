/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.EquivFin

/-!
# Stable counting-sort positions

## Main definitions

* `CountingSort.count`: occurrences of a key in an original input prefix.
* `CountingSort.offset`: occurrences of all smaller keys in the complete input.
* `CountingSort.position`: stable scatter position of an original occurrence.

## Main results

* `CountingSort.offset_succ`: the prefix-sum update used by a native counting pass.
* `CountingSort.position_injective`: every original position has a distinct destination.
* `CountingSort.position_bijective`: scatter destinations form a permutation of the input.

These finite counting identities are original supporting mathematics for the native router.
They assert no sorting program or execution cost.
-/

@[expose] public section

namespace Cslib.Algorithms.CountingSort

open Finset

/-- Number of occurrences of bucket `b` among the first `n` original positions. -/
def count (key : ℕ → ℕ) (n b : ℕ) : ℕ := ((range n).filter fun i => key i = b).card

/-- Starting position of bucket `b`, after all smaller keys in the complete input. -/
def offset (key : ℕ → ℕ) (n b : ℕ) : ℕ := ((range n).filter fun i => key i < b).card

/-- The stable destination of original position `i` in an input of length `n`. -/
def position (key : ℕ → ℕ) (n i : ℕ) : ℕ := offset key n (key i) + count key i (key i)

/-- Empty prefixes contain no occurrences. -/
@[simp]
theorem count_zero (key : ℕ → ℕ) (b : ℕ) : count key 0 b = 0 := by simp [count]

/-- Processing one original position increments just its bucket. -/
theorem count_succ (key : ℕ → ℕ) (n b : ℕ) :
    count key (n + 1) b = count key n b + if key n = b then 1 else 0 := by
  by_cases h : key n = b <;> simp [count, range_add_one, filter_insert, h]

/-- A prefix contains at most its original number of positions. -/
theorem count_le (key : ℕ → ℕ) (n b : ℕ) : count key n b ≤ n :=
  (card_filter_le _ _).trans_eq (card_range n)

/-- Extending the original prefix cannot remove an occurrence. -/
theorem count_mono (key : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') (b : ℕ) :
    count key n b ≤ count key n' b :=
  card_le_card (filter_subset_filter _ (range_mono h))

/-- The original occurrence at `i` has not yet been counted in its strict prefix. -/
theorem count_lt_of_lt (key : ℕ → ℕ) {i n : ℕ} (h : i < n) :
    count key i (key i) < count key n (key i) := by
  have hs := count_succ key i (key i)
  have hm := count_mono key (Nat.succ_le_of_lt h) (key i)
  change count key (i + 1) (key i) ≤ count key n (key i) at hm
  simp only [↓reduceIte] at hs
  omega

/-- The first bucket starts at zero. -/
@[simp]
theorem offset_zero (key : ℕ → ℕ) (n : ℕ) : offset key n 0 = 0 := by simp [offset]

/-- Every prefix offset lies inside the original input length. -/
theorem offset_le (key : ℕ → ℕ) (n b : ℕ) : offset key n b ≤ n :=
  (card_filter_le _ _).trans_eq (card_range n)

/-- Larger keys start no earlier. -/
theorem offset_mono (key : ℕ → ℕ) (n : ℕ) {b c : ℕ} (h : b ≤ c) :
    offset key n b ≤ offset key n c := by
  apply card_le_card
  intro i hi
  obtain ⟨hi, hb⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hi, hb.trans_le h⟩

/-- One prefix-sum step appends exactly the current bucket's cardinality. -/
theorem offset_succ (key : ℕ → ℕ) (n b : ℕ) :
    offset key n (b + 1) = offset key n b + count key n b := by
  have he : ((range n).filter fun i => key i < b + 1) =
      ((range n).filter fun i => key i < b) ∪ ((range n).filter fun i => key i = b) := by
    ext i
    simp only [mem_filter, mem_union, mem_range]
    omega
  unfold offset count
  rw [he, card_union_of_disjoint]
  exact disjoint_left.mpr (by
    intro i hi hj
    have := (mem_filter.mp hi).2
    have := (mem_filter.mp hj).2
    omega)

/-- Once every admitted key is below `B`, its terminal offset is exactly the input length. -/
theorem offset_full (key : ℕ → ℕ) (n B : ℕ) (h : ∀ i < n, key i < B) :
    offset key n B = n := by
  unfold offset
  rw [filter_eq_self.mpr, card_range]
  intro i hi
  exact h i (mem_range.mp hi)

/-- Each occurrence lands before the next bucket, and after its own bucket's start. -/
theorem position_mem (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    offset key n (key i) ≤ position key n i ∧
      position key n i < offset key n (key i + 1) := by
  have := count_lt_of_lt key hi
  rw [offset_succ]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ‹_› _⟩

/-- Stable scatter destinations are valid original-length indices. -/
theorem position_lt (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) : position key n i < n :=
  (position_mem key hi).2.trans_le (offset_le key n (key i + 1))

/-- Original order is retained inside a bucket. -/
theorem position_lt_same (key : ℕ → ℕ) (n : ℕ) {i j : ℕ} (hij : i < j)
    (hkey : key i = key j) : position key n i < position key n j := by
  have := count_lt_of_lt key hij
  simp only [position, hkey] at *
  omega

/-- Every position in a smaller bucket precedes every position in a larger bucket. -/
theorem position_lt_key (key : ℕ → ℕ) {n i j : ℕ} (hi : i < n)
    (hkey : key i < key j) : position key n i < position key n j :=
  ((position_mem key hi).2.trans_le
    (offset_mono key n (Nat.succ_le_of_lt hkey))).trans_le (Nat.le_add_right _ _)

/-- Distinct original positions never overwrite one another during stable scatter. -/
theorem position_injective (key : ℕ → ℕ) (n : ℕ) :
    Function.Injective (fun i : Fin n => position key n i.val) := by
  intro i j he
  change position key n i.val = position key n j.val at he
  rcases lt_trichotomy (key i) (key j) with hk | hk | hk
  · have := position_lt_key key i.isLt hk
    omega
  · rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have := position_lt_same key n hij hk
      omega
    · exact Fin.ext hij
    · have := position_lt_same key n hij hk.symm
      omega
  · have := position_lt_key key j.isLt hk
    omega

/-- All original occurrences, including equal keys, are a permutation of the output cells. -/
theorem position_bijective (key : ℕ → ℕ) (n : ℕ) :
    Function.Bijective (fun i : Fin n =>
      (⟨position key n i.val, position_lt key i.isLt⟩ : Fin n)) := by
  have hi : Function.Injective (fun i : Fin n =>
      (⟨position key n i.val, position_lt key i.isLt⟩ : Fin n)) :=
    fun i j h => position_injective key n (congrArg (fun j : Fin n => j.val) h)
  exact ⟨hi, Finite.surjective_of_injective hi⟩

end Cslib.Algorithms.CountingSort
