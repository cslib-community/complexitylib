/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Insert

/-!
# One step of a filtering scan into a `Finset`

A scan over a list `v :: l` that inserts each element passing a test `p` into an accumulator `s`
has the invariant "`x` is in the result iff `x ∈ s ∨ (x ∈ v :: l ∧ p x)`". The induction step that
consumes `v` either inserts it (when `p v`) or skips it (when `¬p v`). The two lemmas here state
that step, so that each scan's membership proof is its induction skeleton plus one lemma per
branch.

Use them as `apply Finset.mem_or_and_iff_cons` followed by the proof of the test. Elaborating the
test hypothesis first can make Lean guess the predicate `p` from it, not from the goal.

## Main results

* `Finset.mem_insert_or_and_iff_cons`: inserting `v` when `p v` holds preserves the invariant.
* `Finset.mem_or_and_iff_cons`: skipping `v` when `p v` fails preserves the invariant.
-/

public section

namespace Finset

variable {α : Type*} {p : α → Prop} {s : Finset α} {v x : α} {l : List α}

/-- The step of a filtering scan that inserts `v`, which passes the test. -/
theorem mem_insert_or_and_iff_cons [DecidableEq α] (hv : p v) :
    x ∈ insert v s ∨ (x ∈ l ∧ p x) ↔ x ∈ s ∨ (x ∈ v :: l ∧ p x) := by
  grind

/-- The step of a filtering scan that skips `v`, which fails the test. -/
theorem mem_or_and_iff_cons (hv : ¬p v) :
    x ∈ s ∨ (x ∈ l ∧ p x) ↔ x ∈ s ∨ (x ∈ v :: l ∧ p x) := by
  grind

end Finset
