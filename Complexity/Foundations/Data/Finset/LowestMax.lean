/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.Lowest
public import Mathlib.Data.Finset.Max

/-!
# The last element of a finite initial subset

These initial-subset facts identify the highest starred coordinate of a canonical
tensor box and the remaining star set after replacing it. They use the existing
rank-filter initial subset rather than adding a second ordering or rank convention.
-/

public section

namespace Finset

variable {α : Type*} [LinearOrder α]

/-- Membership of a finite initial subset is downward closed inside the original set. -/
theorem mem_lowest_of_le {S : Finset α} {k : ℕ} {x y : α}
    (hy : y ∈ lowest k S) (hx : x ∈ S) (hxy : x ≤ y) : x ∈ lowest k S := by
  refine mem_lowest.mpr ⟨hx, ?_⟩
  apply lt_of_le_of_lt (card_le_card ?_) (mem_lowest.mp hy).2
  intro z hz
  exact mem_filter.mpr ⟨(mem_filter.mp hz).1, (mem_filter.mp hz).2.trans_le hxy⟩

/-- The last of the first `k` elements has precisely `k - 1` predecessors in the original set. -/
theorem card_filter_lt_max_lowest {S : Finset α} {k : ℕ} (hk : k ≤ S.card)
    (hne : (lowest k S).Nonempty) :
    (S.filter fun x => x < (lowest k S).max' hne).card + 1 = k := by
  have hc : (lowest k S).card = k := by rw [card_lowest, min_eq_left hk]
  have hf : (S.filter fun x => x < (lowest k S).max' hne) =
      (lowest k S).erase ((lowest k S).max' hne) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxs, hlt⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨hlt.ne,
        mem_lowest_of_le (max'_mem _ hne) hxs hlt.le⟩
    · intro hx
      obtain ⟨hne', hx⟩ := mem_erase.mp hx
      exact mem_filter.mpr ⟨lowest_subset _ _ hx,
        lt_of_le_of_ne (le_max' _ x hx) hne'⟩
  rw [hf, card_erase_of_mem (max'_mem _ hne), hc]
  have hpos : 0 < k := by simpa only [hc] using hne.card_pos
  omega

/-- Removing the last selected element leaves the shorter initial subset. -/
theorem erase_max_lowest {S : Finset α} {k : ℕ} (hk : k ≤ S.card)
    (hne : (lowest k S).Nonempty) :
    (lowest k S).erase ((lowest k S).max' hne) = lowest (k - 1) S := by
  have hsub : (lowest k S).erase ((lowest k S).max' hne) ⊆ S :=
    (erase_subset _ _).trans (lowest_subset _ _)
  have hinit := eq_lowest_of_lt hsub (fun x hx y hy => by
    obtain ⟨hxn, hx⟩ := mem_erase.mp hx
    by_cases hyq : y ∈ lowest k S
    · have hymax : y = (lowest k S).max' hne := by
        by_contra hn
        exact (mem_sdiff.mp hy).2 (mem_erase.mpr ⟨hn, hyq⟩)
      rw [hymax]
      exact lt_of_le_of_ne (le_max' _ x hx) hxn
    · exact lowest_lt hx (mem_sdiff.mpr ⟨(mem_sdiff.mp hy).1, hyq⟩))
  simpa only [card_erase_of_mem (max'_mem _ hne), card_lowest, min_eq_left hk] using hinit

/-- Removing that coordinate from the ambient set leaves the same shorter initial subset. -/
theorem erase_max_lowest_erase {S : Finset α} {k : ℕ} (hk : k ≤ S.card)
    (hne : (lowest k S).Nonempty) :
    (lowest k S).erase ((lowest k S).max' hne) =
      lowest (k - 1) (S.erase ((lowest k S).max' hne)) := by
  have hsub : (lowest k S).erase ((lowest k S).max' hne) ⊆
      S.erase ((lowest k S).max' hne) := erase_subset_erase _ (lowest_subset _ _)
  have hinit := eq_lowest_of_lt hsub (fun x hx y hy => by
    have hxs := (mem_erase.mp hx).2
    have hyS := (mem_erase.mp (mem_sdiff.mp hy).1).2
    have hnot : y ∉ lowest k S := by
      intro hyq
      exact (mem_sdiff.mp hy).2
        (mem_erase.mpr ⟨(mem_erase.mp (mem_sdiff.mp hy).1).1, hyq⟩)
    exact lowest_lt hxs (mem_sdiff.mpr ⟨hyS, hnot⟩))
  simpa only [card_erase_of_mem (max'_mem _ hne), card_lowest, min_eq_left hk] using hinit

end Finset
