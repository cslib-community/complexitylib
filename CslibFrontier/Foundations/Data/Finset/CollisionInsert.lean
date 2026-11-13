/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-!
# Insertion with a reserved replacement for collisions

`Finset.collisionInsert s p r` inserts the candidate `r` into `s`, replacing it by the
reserved element `p` when `r` already belongs to `s`. When `p ∉ s`, the cardinality increases
by exactly one. The candidate remains in the result, and the original set can be recovered
from the result and candidate. This is the descending collision-replacement step in fixed-weight
sampling.

## Main definitions

* `Finset.collisionInsert`: insert a candidate, replacing a collision by a reserved element.

## Main results

* `Finset.card_collisionInsert`: inserting with a fresh replacement increases cardinality by one.
* `Finset.erase_collisionInsert`: recover the input from the result and the candidate.
-/

public section

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Insert `r`, or insert the reserved element `p` if `r` already belongs to `s`. -/
@[expose] def collisionInsert (s : Finset α) (p r : α) : Finset α :=
  insert (if r ∈ s then p else r) s

/-- Every old element remains after insertion with collision replacement. -/
theorem subset_collisionInsert (s : Finset α) (p r : α) : s ⊆ s.collisionInsert p r :=
  subset_insert _ _

/-- The candidate belongs to the result even when it caused a collision. -/
theorem mem_collisionInsert (s : Finset α) (p r : α) : r ∈ s.collisionInsert p r := by
  by_cases hr : r ∈ s <;> simp [collisionInsert, hr]

/-- A reserved element outside the old set makes each step add exactly one element. -/
theorem card_collisionInsert {s : Finset α} {p : α} (hp : p ∉ s) (r : α) :
    (s.collisionInsert p r).card = s.card + 1 := by
  by_cases hr : r ∈ s <;> simp [collisionInsert, hr, hp]

/-- If the old set and candidate lie in `S`, the result lies in `insert p S`. -/
theorem collisionInsert_subset {s S : Finset α} (hs : s ⊆ S) (p : α) {r : α}
    (hr : r ∈ insert p S) : s.collisionInsert p r ⊆ insert p S := by
  apply insert_subset
  · split_ifs
    · exact mem_insert_self _ _
    · exact hr
  · exact hs.trans (subset_insert _ _)

/-- Recover the old set by erasing the reserved element if it appears, and the candidate
otherwise. The assumption that the replacement is fresh is essential. -/
theorem erase_collisionInsert {s : Finset α} {p : α} (hp : p ∉ s) (r : α) :
    (if p ∈ s.collisionInsert p r then (s.collisionInsert p r).erase p
      else (s.collisionInsert p r).erase r) = s := by
  by_cases hr : r ∈ s
  · simp [collisionInsert, hr, hp, erase_insert hp]
  · by_cases hpr : p = r
    · subst r
      simp [collisionInsert, hp, erase_insert hp]
    · simp [collisionInsert, hr, hp, hpr, erase_insert hr]

/-- Every element of a target set supplies a predecessor: erase the reserved element when it
belongs to the target, and otherwise erase the chosen candidate. -/
theorem collisionInsert_erase {s : Finset α} {r : α} (hr : r ∈ s) (p : α) :
    (if p ∈ s then s.erase p else s.erase r).collisionInsert p r = s := by
  by_cases hp : p ∈ s
  · by_cases hpr : p = r
    · subst r
      simp [collisionInsert, hp, insert_erase hp]
    · have hrp : r ≠ p := Ne.symm hpr
      simp [collisionInsert, hp, hr, hrp, insert_erase hp]
  · simp [collisionInsert, hp, hr, insert_erase hr]

end Finset
