/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.OfFn

/-!
# Ordered finite-set enumeration and filtering

## Main results

* `Finset.sort_eq_filter_finRange`: a level set in increasing order is the filtered level list.
* `Finset.ofFn_orderEmbOfFin`: values at its ordered positions form its sorted mapped list.
-/

@[expose] public section

namespace Finset

/-- Increasing level-set enumeration is ordinary filtering of all levels. -/
theorem sort_eq_filter_finRange {L : ℕ} (s : Finset (Fin L)) :
    s.sort = (List.finRange L).filter fun i => decide (i ∈ s) := by
  apply s.sortedLT_sort.eq_of_mem_iff
    ((List.sortedLT_finRange L).pairwise.filter _ |>.sortedLT)
  intro a
  simp

/-- Applying a function to the ordered finite-set positions agrees with its sorted list. -/
theorem ofFn_orderEmbOfFin {α β : Type*} [LinearOrder α] (s : Finset α)
    {k : ℕ} (h : s.card = k) (f : α → β) :
    List.ofFn (fun i => f (s.orderEmbOfFin h i)) = s.sort.map f := by
  rw [← s.listMap_orderEmbOfFin_finRange h, List.map_map, List.ofFn_eq_map]
  rfl

end Finset
