/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Order.Interval.Finset.Nat

/-!
# First indices and cardinality bounds in natural-number ranges

Range index and duplicate-free natural-list length bounds shared across certificate modules.

## Main results

* `List.idxOf_range_of_lt`, `List.length_filter_lt_le`, `List.length_le_of_nodup_lt`.
* `List.length_filter_range_eq_one_iff`: exactly one number below `n` passes a test.
-/

@[expose] public section

namespace List

/-- An in-range natural number occurs at its own position in `range`. -/
theorem idxOf_range_of_lt {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h


/-- In a duplicate-free list of naturals, at most `u` elements are strictly below `u`. -/
theorem length_filter_lt_le {S : List ℕ} (hS : S.Nodup) (u : ℕ) :
    (S.filter (· < u)).length ≤ u :=
  (List.toFinset_card_of_nodup (hS.filter _)).symm.trans_le <|
    (Finset.card_le_card fun _ hs => Finset.mem_range.mpr
      (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hs)).2)).trans_eq
      (Finset.card_range u)

/-- A duplicate-free list of naturals all strictly below `n` has length at most `n`. -/
theorem length_le_of_nodup_lt {n : ℕ} {S : List ℕ} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) :
    S.length ≤ n := by
  have h := length_filter_lt_le hS n
  rwa [List.filter_eq_self.mpr fun s hs => decide_eq_true (hSn s hs)] at h

/-- Filtering `range n` leaves one entry exactly when one number below `n` passes the test. -/
theorem length_filter_range_eq_one_iff {n : ℕ} {p : ℕ → Bool} :
    ((List.range n).filter p).length = 1 ↔ ∃! j, j < n ∧ p j = true := by
  have hmem : ∀ j, j ∈ (List.range n).filter p ↔ j < n ∧ p j = true := fun j => by
    simp only [List.mem_filter, List.mem_range]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
    refine ⟨a, (hmem a).mp (by simp [ha]), fun j hj => ?_⟩
    simpa [ha] using (hmem j).mpr hj
  · rintro ⟨a, ha, huniq⟩
    have hperm : ((List.range n).filter p).Perm [a] :=
      (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) (List.nodup_singleton a)).mpr
        fun j => by
          rw [hmem, List.mem_singleton]
          exact ⟨fun hj => huniq j hj, fun h => h ▸ ha⟩
    simpa using hperm.length_eq

end List
