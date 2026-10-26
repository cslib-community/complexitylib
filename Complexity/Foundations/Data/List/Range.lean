/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# First indices in natural-number ranges

This index identity is shared by source endpoint and path geometry certificates.

## Main results

* `List.idxOf_range_of_lt`.
-/

@[expose] public section

namespace List

/-- An in-range natural number occurs at its own position in `range`. -/
theorem idxOf_range_of_lt {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h


end List
