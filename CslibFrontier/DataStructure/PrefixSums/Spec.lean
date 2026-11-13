/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Dynamic prefix sums

The abstract state is a list over an additive commutative monoid. `add pos δ` increments one
entry; out-of-range positions leave the list unchanged. `sum len` returns the sum of the first
`len` entries; a length beyond the end sums the whole list. Every operation is admissible, and
the length of the list never changes. The module chooses no representation and charges no cost;
an implementation with machine bounds, such as a word-fit condition, restricts `spec.valid`.

## Main definitions

* `Cslib.DataStructure.PrefixSums.addAt`: point increment on a list.
* `Cslib.DataStructure.PrefixSums.Op`, `Cslib.DataStructure.PrefixSums.step`,
  `Cslib.DataStructure.PrefixSums.spec`: typed operations and their list semantics.

## Main results

* `Cslib.DataStructure.PrefixSums.length_addAt`, `Cslib.DataStructure.PrefixSums.getD_addAt`,
  `Cslib.DataStructure.PrefixSums.addAt_of_length_le`: the point increment changes one entry.
* `Cslib.DataStructure.PrefixSums.addAt_append`: a point increment of a concatenation updates
  the part containing the position.
* `Cslib.DataStructure.PrefixSums.length_stepFn`: every operation preserves the length.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*][Fenwick1994]
-/

@[expose] public section

namespace Cslib.DataStructure.PrefixSums

open Cslib.DataStructure

section AddAt

variable {α : Type*} [AddZeroClass α]

/-- Point increment on a list at `0`-based index `pos` (no-op when `s.length ≤ pos`). -/
def addAt (s : List α) (pos : ℕ) (δ : α) : List α :=
  s.set pos (s.getD pos 0 + δ)

@[simp]
theorem length_addAt (s : List α) (pos : ℕ) (δ : α) : (addAt s pos δ).length = s.length :=
  List.length_set

theorem addAt_of_length_le {s : List α} {pos : ℕ} (δ : α) (h : s.length ≤ pos) :
    addAt s pos δ = s :=
  List.set_eq_of_length_le h

theorem getD_addAt (s : List α) {pos : ℕ} (δ : α) (hpos : pos < s.length) (i : ℕ) :
    (addAt s pos δ).getD i 0 = if i = pos then s.getD i 0 + δ else s.getD i 0 := by
  unfold addAt
  split_ifs with heq
  · subst heq
    exact List.getD_set_self hpos
  · exact List.getD_set_ne (Ne.symm heq)

/-- A point increment of a concatenation updates the part containing the position. -/
theorem addAt_append (s t : List α) (pos : ℕ) (δ : α) :
    addAt (s ++ t) pos δ =
      if pos < s.length then addAt s pos δ ++ t else s ++ addAt t (pos - s.length) δ := by
  unfold addAt
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h, List.set_append_left _ _ h]
  · have h' := Nat.le_of_not_gt h
    rw [List.getD_append_right _ _ _ _ h', List.set_append_right _ _ h']

end AddAt

/-- Dynamic prefix-sum operations over `α`, independent of storage representation. -/
inductive Op (α : Type) where
  /-- Increment the entry at `0`-based index `pos` by `delta` (no-op when out of bounds). -/
  | add (pos : ℕ) (delta : α)
  /-- Return the sum `(s.take len).sum` of the first `len` entries. -/
  | sum (len : ℕ)
  deriving DecidableEq, Repr

/-- Return types for `Op α`. -/
abbrev Op.Result (α : Type) : Op α → Type
  | .add _ _ => Unit
  | .sum _ => α

variable {α : Type} [AddCommMonoid α]

/-- Pure transition function of dynamic prefix sums on `List α`. -/
def step (s : List α) : (o : Op α) → List α × o.Result α
  | .add pos δ => (addAt s pos δ, ())
  | .sum len => (s, (s.take len).sum)

variable (α) in
/-- Mathematical specification of dynamic prefix sums on `List α`. All operations are
admissible: out-of-bounds `add` is a no-op and `sum len` sums `s.take len`. -/
abbrev spec : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := List α) (Op := Op α) (Result := Op.Result α) step

/-- Every operation preserves the length of the list. -/
@[simp]
theorem length_stepFn (s : List α) (o : Op α) : ((spec α).stepFn s o).1.length = s.length := by
  cases o with
  | add pos δ => exact length_addAt s pos δ
  | sum len => rfl

end Cslib.DataStructure.PrefixSums
