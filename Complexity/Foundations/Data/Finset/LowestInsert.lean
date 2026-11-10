/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.Lowest

/-!
# Maintaining the lowest elements of a growing set

`Finset.lowest k S` keeps the `k` smallest elements of `S`. This file shows that it can be
maintained online: inserting a new element into the current selection and selecting again gives the
selection of the enlarged set (`Finset.lowest_insert_lowest`). A one-pass algorithm can therefore
keep only `k` elements, as the k-minimum-values sketch for distinct elements does
(`Complexity.Computability.Streaming.DistinctElements`). It also characterizes when all selected
elements satisfy a property closed downwards (`Finset.forall_mem_lowest_iff`); for the property
`· < x`, this says that the `k`-th smallest element is below `x` exactly when at least `k` elements
are.

## Main results

* `Finset.lowest_eq_self`: a set of at most `k` elements is its own selection.
* `Finset.lowest_eq_lowest_of_subset`: the selection from `S` is also the selection from any
  intermediate set.
* `Finset.lowest_insert_lowest`: inserting into the selection and selecting again is selecting
  from the enlarged set.
* `Finset.forall_mem_lowest_iff`: the selected elements all satisfy a downward-closed property
  exactly when at least `k` elements do.
-/

public section

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- A set with at most `k` elements is its own selection of `k` lowest elements. -/
theorem lowest_eq_self {k : ℕ} {S : Finset α} (h : S.card ≤ k) : lowest k S = S := by
  refine (lowest_subset k S).antisymm fun x hx => mem_lowest.2 ⟨hx, ?_⟩
  exact (card_lt_card (s := S.filter (· < x)) ⟨filter_subset _ _, fun hsub => lt_irrefl x
    (mem_filter.1 (hsub hx)).2⟩).trans_le h

/-- If `T ⊆ S` contains the `k` lowest elements of `S`, then they are also the `k` lowest elements
of `T`. -/
theorem lowest_eq_lowest_of_subset {k : ℕ} {S T : Finset α} (hTS : T ⊆ S)
    (hT : lowest k S ⊆ T) : lowest k T = lowest k S := by
  ext x
  simp only [mem_lowest]
  constructor
  · rintro ⟨hxT, hx⟩
    refine ⟨hTS hxT, ?_⟩
    by_contra hge
    rw [not_lt] at hge
    -- Every selected element of `S` is then below `x`, so `T` has `k` elements below `x`.
    have hxS : x ∉ lowest k S := fun h => by
      rw [mem_lowest] at h
      omega
    have hcard := card_le_card fun y hy =>
      mem_filter.2 ⟨hT hy, lowest_lt hy (mem_sdiff.2 ⟨hTS hxT, hxS⟩)⟩
    rw [card_lowest] at hcard
    rcases le_total S.card k with hle | hle
    · exact hxS (by rw [lowest_eq_self hle]; exact hTS hxT)
    · omega
  · rintro ⟨hxS, hx⟩
    exact ⟨hT (mem_lowest.2 ⟨hxS, hx⟩),
      lt_of_le_of_lt (card_le_card (filter_subset_filter _ hTS)) hx⟩

/-- **Online selection**: inserting `x` into the `k` lowest elements of `S` and selecting the `k`
lowest again gives the `k` lowest elements of `insert x S`. -/
theorem lowest_insert_lowest [DecidableEq α] (k : ℕ) (x : α) (S : Finset α) :
    lowest k (insert x (lowest k S)) = lowest k (insert x S) :=
  lowest_eq_lowest_of_subset (insert_subset_insert _ (lowest_subset _ _)) fun y hy => by
    rcases mem_insert.1 (lowest_subset _ _ hy) with rfl | hyS
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_lowest.2 ⟨hyS, lt_of_le_of_lt
        (card_le_card (filter_subset_filter _ (subset_insert _ _))) (mem_lowest.1 hy).2⟩)

/-- **Order statistics of a downward-closed property**: when `k ≤ #S`, the `k` lowest elements of
`S` all satisfy a property `P` closed downwards exactly when at least `k` elements of `S` do. -/
theorem forall_mem_lowest_iff {k : ℕ} {S : Finset α} (hk : k ≤ S.card) (P : α → Prop)
    [DecidablePred P] (hP : ∀ x y, x ≤ y → P y → P x) :
    (∀ x ∈ lowest k S, P x) ↔ k ≤ (S.filter P).card := by
  constructor
  · intro h
    have := card_le_card fun x hx => mem_filter.2 ⟨lowest_subset k S hx, h x hx⟩
    rwa [card_lowest, min_eq_left hk] at this
  · intro h x hx
    by_contra hPx
    have hsub : S.filter P ⊆ S.filter (· < x) := fun y hy => by
      obtain ⟨hyS, hPy⟩ := mem_filter.1 hy
      exact mem_filter.2 ⟨hyS, lt_of_not_ge fun hxy => hPx (hP x y hxy hPy)⟩
    exact absurd ((card_le_card hsub).trans_lt (mem_lowest.1 hx).2) (not_lt.2 h)

end Finset
