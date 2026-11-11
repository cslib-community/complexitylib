/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

/-!
# Selecting distinct list entries by a mask

`Cslib.Complexity.selectDistinct l w` keeps the entry at position `i` of `l` when bit `i` of `w`
is `true` and `i` is the first occurrence of that entry in `l`. Missing bits are `false`, and bits
beyond the length of `l` are ignored. Unlike `Cslib.Complexity.maskSelect`, which keeps every
selected position and so selects sub-multisets, a repeated entry is selected at most once, so the
selection is duplicate-free (`nodup_selectDistinct`) and describes a set. Selecting with a full mask
of `true` bits lists the distinct entries of `l` in the order of their first occurrences
(`mem_selectDistinct_replicate`, `length_selectDistinct_replicate`).

## Main definitions

* `Cslib.Complexity.selectDistinct`: the distinct entries of a list selected by a mask.

## Main results

* `Cslib.Complexity.mem_selectDistinct`, `Cslib.Complexity.nodup_selectDistinct`: membership and
  duplicate-freeness of the selected entries.
* `Cslib.Complexity.mem_selectDistinct_replicate`,
  `Cslib.Complexity.length_selectDistinct_replicate`: the full mask selects every distinct entry of
  `l` once.
-/

@[expose] public section

namespace Cslib.Complexity

variable {γ : Type*} [DecidableEq γ]

/-- The distinct entries of `l` selected by the mask `w`: position `i` of `l` is kept when bit `i`
of `w` is `true` and `i` is the first occurrence of its entry in `l`. Missing bits are `false`, and
bits beyond the length of `l` are ignored. Unlike `Cslib.Complexity.maskSelect`, which keeps every
selected position and so selects sub-multisets, a repeated entry is selected at most once, so the
selection describes a set. -/
def selectDistinct (l : List γ) (w : List Bool) : List γ :=
  (l.zipIdx.filter fun e => w.getD e.2 false && decide (l.idxOf e.1 = e.2)).map Prod.fst

/-- An entry `v` belongs to `selectDistinct l w` iff `v ∈ l` and the mask bit at the first
occurrence `l.idxOf v` is `true`. -/
theorem mem_selectDistinct {l : List γ} {w : List Bool} {v : γ} :
    v ∈ selectDistinct l w ↔ v ∈ l ∧ w.getD (l.idxOf v) false = true := by
  simp only [selectDistinct, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?,
    Bool.and_eq_true, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨u, i, ⟨hi, hw, hidx⟩, rfl⟩
    exact ⟨List.mem_of_getElem? hi, hidx ▸ hw⟩
  · rintro ⟨hv, hw⟩
    have hlt : l.idxOf v < l.length := List.idxOf_lt_length_iff.2 hv
    exact ⟨v, l.idxOf v, ⟨by simp [hlt], hw, rfl⟩, rfl⟩

/-- `selectDistinct l w` contains no duplicate entries. -/
theorem nodup_selectDistinct (l : List γ) (w : List Bool) : (selectDistinct l w).Nodup := by
  have hzip : l.zipIdx.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij h
    have := congrArg Prod.snd h
    simp only [List.getElem_zipIdx, Nat.zero_add] at this
    omega
  refine (hzip.filter _).map_on ?_
  rintro ⟨u, i⟩ hu ⟨v, j⟩ hv (rfl : u = v)
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hu hv
  rw [← hu.2.2, ← hv.2.2]

/-- The full mask selects every entry of `l`, at its first occurrence. -/
theorem mem_selectDistinct_replicate {l : List γ} {v : γ} :
    v ∈ selectDistinct l (List.replicate l.length true) ↔ v ∈ l := by
  rw [mem_selectDistinct, and_iff_left_iff_imp]
  intro hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (List.idxOf_lt_length_iff.2 hv)]
  rfl

/-- The full mask selects as many entries as `l` has distinct entries. -/
theorem length_selectDistinct_replicate (l : List γ) :
    (selectDistinct l (List.replicate l.length true)).length = l.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (nodup_selectDistinct _ _)]
  congr 1
  ext v
  simp only [List.mem_toFinset, mem_selectDistinct_replicate]

end Cslib.Complexity
