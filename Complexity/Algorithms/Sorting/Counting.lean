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
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Stable counting-sort positions

## Main definitions

* `CountingSort.position`: stable scatter position of an original occurrence.

## Main results

* `CountingSort.count_lt_succ`: the prefix-sum update used by a native counting pass.
* `CountingSort.position_injective`: every original position has a distinct destination.
* `CountingSort.position_bijective`: scatter destinations form a permutation of the input.
* `CountingSort.scatter_span_image`: an actual scattered array's bucket span has exactly
  the values whose original keys select that bucket.

These finite counting identities are original supporting mathematics for the native router.
They reuse Mathlib's `Nat.count` and its prefix-count APIs directly; only the stable-scatter
construction and cross-bucket theory are added. They assert no program or execution cost.
-/

@[expose] public section

namespace Cslib.Algorithms.CountingSort

open Finset

/-- The stable destination of original position `i` in an input of length `n`. -/
def position (key : ℕ → ℕ) (n i : ℕ) : ℕ :=
  Nat.count (fun k => key k < key i) n + Nat.count (fun k => key k = key i) i

/-- Larger keys start no earlier. -/
private theorem offset_mono (key : ℕ → ℕ) (n : ℕ) {b c : ℕ} (h : b ≤ c) :
    Nat.count (fun k => key k < b) n ≤ Nat.count (fun k => key k < c) n := by
  exact Nat.count_mono_left (fun _ _ hk => hk.trans_le h)

/-- One prefix-sum step appends exactly the current bucket's cardinality. -/
theorem count_lt_succ (key : ℕ → ℕ) (n b : ℕ) :
    Nat.count (fun k => key k < b + 1) n =
      Nat.count (fun k => key k < b) n + Nat.count (fun k => key k = b) n := by
  have he : ((range n).filter fun i => key i < b + 1) =
      ((range n).filter fun i => key i < b) ∪ ((range n).filter fun i => key i = b) := by
    ext i
    simp only [mem_filter, mem_union, mem_range]
    omega
  simp only [Nat.count_eq_card_filter_range]
  rw [he, card_union_of_disjoint]
  exact disjoint_left.mpr (by
    intro i hi hj
    have := (mem_filter.mp hi).2
    have := (mem_filter.mp hj).2
    omega)

/-- Each occurrence lands before the next bucket, and after its own bucket's start. -/
theorem position_mem (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    Nat.count (fun k => key k < key i) n ≤ position key n i ∧
      position key n i < Nat.count (fun k => key k < key i + 1) n := by
  have := Nat.count_strict_mono (p := fun j => key j = key i) rfl hi
  rw [count_lt_succ]
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ‹_› _⟩

/-- Stable scatter destinations are valid original-length indices. -/
theorem position_lt (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) : position key n i < n :=
  (position_mem key hi).2.trans_le (Nat.count_le _)

/-- Original order is retained inside a bucket. -/
theorem position_lt_same (key : ℕ → ℕ) (n : ℕ) {i j : ℕ} (hij : i < j)
    (hkey : key i = key j) : position key n i < position key n j := by
  have := Nat.count_strict_mono (p := fun j => key j = key i) rfl hij
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

/-- A stable destination belongs to a bucket's half-open span exactly when its key is that
bucket. Equal values or repeated original requests do not change the interval criterion. -/
theorem position_mem_iff (key : ℕ → ℕ) {n i : ℕ} (hi : i < n) (b : ℕ) :
    (Nat.count (fun k => key k < b) n ≤ position key n i ∧
      position key n i < Nat.count (fun k => key k < b + 1) n) ↔
      key i = b := by
  constructor
  · intro h
    rcases lt_trichotomy (key i) b with hb | hb | hb
    · have hp := (position_mem key hi).2.trans_le (offset_mono key n (Nat.succ_le_of_lt hb))
      omega
    · exact hb
    · have hp := (offset_mono key n (Nat.succ_le_of_lt hb)).trans (position_mem key hi).1
      change Nat.count (fun k => key k < b + 1) n ≤ position key n i at hp
      omega
  · intro h
    subst b
    exact position_mem key hi

/-- A memory array satisfying the stable-scatter equations has precisely the original
values selected by each bucket. No sorted list or permutation certificate is a premise. -/
theorem scatter_span_image {α : Type*} [DecidableEq α] (key : ℕ → ℕ) (n b : ℕ)
    (stored values : ℕ → α) (h : ∀ i < n, stored (position key n i) = values i) :
    (Ico (Nat.count (fun k => key k < b) n) (Nat.count (fun k => key k < b + 1) n)).image stored =
      ((range n).filter fun i => key i = b).image values := by
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj, hv⟩ := mem_image.mp hv
    have hjn : j < n := (mem_Ico.mp hj).2.trans_le (Nat.count_le _)
    obtain ⟨i, hi⟩ := (position_bijective key n).surjective ⟨j, hjn⟩
    have hpos : position key n i.val = j := congrArg (fun t : Fin n => t.val) hi
    have hkey : key i.val = b := (position_mem_iff key i.isLt b).mp (by
      rw [hpos]
      exact mem_Ico.mp hj)
    exact mem_image.mpr ⟨i.val, mem_filter.mpr ⟨mem_range.mpr i.isLt, hkey⟩,
      (h i.val i.isLt).symm.trans (by simpa only [hpos] using hv)⟩
  · intro hv
    obtain ⟨i, hi, hv⟩ := mem_image.mp hv
    obtain ⟨hin, hik⟩ := mem_filter.mp hi
    have hlt := mem_range.mp hin
    exact mem_image.mpr ⟨position key n i,
      mem_Ico.mpr ((position_mem_iff key hlt b).mpr hik), (h i hlt).trans hv⟩

end Cslib.Algorithms.CountingSort
