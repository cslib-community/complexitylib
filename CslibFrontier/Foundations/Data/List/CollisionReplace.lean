/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic

/-!
# Scanning for a collision

## Main results

* `List.foldl_replaceOnCollision`: repeatedly replacing a candidate by one fixed value when
  it equals a list entry is a single membership test. No freshness premise is needed.
-/

public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- A scan returns `p` when the original candidate collides, and retains the candidate
otherwise. Once replaced, the value stays `p`. -/
theorem foldl_replaceOnCollision (xs : List α) (p r : α) :
    xs.foldl (fun current x => if current = x then p else current) r =
      if r ∈ xs then p else r := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hr : r = x
    · subst x
      simp
    · simp [hr]

end List
