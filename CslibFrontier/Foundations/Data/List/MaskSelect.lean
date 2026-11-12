/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

/-!
# Selecting list entries by a mask

`Cslib.Complexity.maskSelect l w` keeps the entries of `l` at the positions where the bit string
`w` is `true`. Masks describe exactly the sublists of `l`, and therefore, up to order, exactly the
sub-multisets of `l`; this makes them polynomially long certificates for problems that ask for a
sub-multiset of the input numbers, such as subset sum, partition and knapsack. Unlike
`Cslib.Complexity.selectDistinct`, which selects each distinct entry at most once and so selects
sets, a repeated entry may be selected repeatedly.

## Main definitions

* `Cslib.Complexity.maskSelect`.

## Main results

* `Cslib.Complexity.maskSelect_sublist`, `Cslib.Complexity.exists_maskSelect_eq`: masks select
  exactly the sublists.
* `Cslib.Complexity.exists_le_coe_iff_exists_sublist`: sub-multisets are sublists up to order.
* `Cslib.Complexity.exists_le_iff_exists_maskSelect`: a property of sub-multisets holds for one of
  them exactly when it holds for the selection of some mask of any length at least the length of
  the list.
* `Cslib.Complexity.maskSelect_eq_map_filter_range`: the selection as the entries at the selected
  indices.
* `Cslib.Complexity.sum_maskSelect`: the sum of the selected numbers is the scalar product with
  the mask.
-/

@[expose] public section

namespace Cslib.Complexity

open scoped List

variable {α : Type*}

/-- The entries of `l` at the positions where `w` is `true`; positions beyond the end of `w` are
not selected. Repeated entries may be selected repeatedly, so masks select sub-multisets; for sets,
`Cslib.Complexity.selectDistinct` selects each entry at most once. -/
def maskSelect (l : List α) (w : List Bool) : List α :=
  (l.zipIdx.filter fun p => w.getD p.2 false).map Prod.fst

@[simp]
theorem maskSelect_nil (w : List Bool) : maskSelect ([] : List α) w = [] := rfl

theorem maskSelect_cons (a : α) (l : List α) (w : List Bool) :
    maskSelect (a :: l) w = (if w.headD false then [a] else []) ++ maskSelect l w.tail := by
  have hshift : (fun p : α × ℕ => w.getD p.2 false) ∘ Prod.map id (· + 1) =
      fun p => w.tail.getD p.2 false := by
    funext p
    cases w <;> simp
  simp only [maskSelect, List.zipIdx_cons', List.filter_cons, List.filter_map, hshift]
  cases w with
  | nil => simp
  | cons b w => cases b <;> simp [List.map_map, Function.comp_def]

/-- A mask selects a sublist. -/
theorem maskSelect_sublist (l : List α) (w : List Bool) : maskSelect l w <+ l := by
  simpa only [maskSelect, List.zipIdx_map_fst] using
    (List.filter_sublist (p := fun p : α × ℕ => w.getD p.2 false) (l := l.zipIdx)).map Prod.fst

/-- Every sublist is selected by a mask as long as the list. -/
theorem exists_maskSelect_eq {s l : List α} (h : s <+ l) :
    ∃ w : List Bool, w.length = l.length ∧ maskSelect l w = s := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    exact ⟨false :: w, by simp [hw], by simp [maskSelect_cons, hs]⟩
  | cons_cons a _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    exact ⟨true :: w, by simp [hw], by simp [maskSelect_cons, hs]⟩

/-- Unselected positions beyond the list do not change the selection. -/
theorem maskSelect_append_replicate_false (l : List α) (w : List Bool) (k : ℕ) :
    maskSelect l (w ++ List.replicate k false) = maskSelect l w := by
  unfold maskSelect
  congr 2 with p : 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rfl
  · rw [List.getElem?_eq_none (by lia : w.length ≤ p.2)]
    by_cases h : p.2 - w.length < k <;> simp [h]

/-- The selection of a mask is the list of entries at the selected indices. -/
theorem maskSelect_eq_map_filter_range (l : List α) (w : List Bool) (d : α) :
    maskSelect l w = ((List.range l.length).filter fun i => w.getD i false).map (l.getD · d) := by
  have hz : l.zipIdx = (List.range l.length).map fun i => (l.getD i d, i) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp [List.getElem?_eq_getElem (List.length_zipIdx ▸ h₁ : i < l.length)]
  simp only [maskSelect, hz, List.filter_map, List.map_map, Function.comp_def]

/-- The numbers selected by a mask sum to the scalar product with the mask. -/
theorem sum_maskSelect (a : List ℕ) (w : List Bool) :
    (maskSelect a w).sum =
      ∑ j ∈ Finset.range a.length, a.getD j 0 * (w.getD j false).toNat := by
  induction a generalizing w with
  | nil => simp
  | cons n a ih =>
    rw [maskSelect_cons, List.sum_append, ih, List.length_cons, Finset.sum_range_succ']
    cases w with
    | nil => simp
    | cons b w => cases b <;> simp [Nat.add_comm]

/-- The sub-multisets of a list are the sublists, up to order. -/
theorem exists_le_coe_iff_exists_sublist {l : List α} (P : Multiset α → Prop) :
    (∃ s ≤ (l : Multiset α), P s) ↔ ∃ s, s <+ l ∧ P s := by
  constructor
  · rintro ⟨s, hs, hP⟩
    induction s using Quotient.inductionOn with
    | h s =>
    obtain ⟨t, hts, htl⟩ := Multiset.coe_le.1 hs
    exact ⟨t, htl, by rwa [Multiset.coe_eq_coe.2 hts]⟩
  · rintro ⟨s, hs, hP⟩
    exact ⟨s, Multiset.coe_le.2 hs.subperm, hP⟩

/-- A property of sub-multisets of `l` holds for one of them exactly when it holds for the
selection of a mask of length `n`, for any `n` at least the length of `l`. -/
theorem exists_le_iff_exists_maskSelect {l : List α} {n : ℕ} (hn : l.length ≤ n)
    (P : Multiset α → Prop) :
    (∃ s ≤ (l : Multiset α), P s) ↔
      ∃ w : List Bool, w.length = n ∧ P (maskSelect l w : Multiset α) := by
  rw [exists_le_coe_iff_exists_sublist]
  constructor
  · rintro ⟨s, hs, hP⟩
    obtain ⟨w, hw, rfl⟩ := exists_maskSelect_eq hs
    exact ⟨w ++ List.replicate (n - l.length) false, by simp [hw, hn],
      by rwa [maskSelect_append_replicate_false]⟩
  · rintro ⟨w, -, hP⟩
    exact ⟨_, maskSelect_sublist l w, hP⟩

end Cslib.Complexity
