/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Max

/-!
# Optional minima, maxima and strict predecessors of finite ordered sets

The least- and greatest-result contracts include absence: `none` means the eligible set is empty.
They are independent of any tree, storage representation or cost model. The strict predecessor
of a query is the greatest key strictly below it; the strict successor used by
`Cslib.DataStructure.OrderedSet.spec` is `least (s.filter (x < ·))`.

## Main definitions

* `Cslib.DataStructure.OrderedSet.LeastResult`: a complete optional-minimum contract.
* `Cslib.DataStructure.OrderedSet.least`: the mathematical minimum of a finite set.
* `Cslib.DataStructure.OrderedSet.GreatestResult`: a complete optional-maximum contract.
* `Cslib.DataStructure.OrderedSet.greatest`: the mathematical maximum of a finite set.
* `Cslib.DataStructure.OrderedSet.predecessor`: the greatest key strictly below a query.

## Main results

* `Cslib.DataStructure.OrderedSet.least_spec`: the mathematical minimum satisfies the contract.
* `Cslib.DataStructure.OrderedSet.LeastResult.eq_least`: any satisfying result equals that minimum.
* `Cslib.DataStructure.OrderedSet.least_eq_min`: `least` agrees with `Finset.min`.
* `Cslib.DataStructure.OrderedSet.greatest_spec`,
  `Cslib.DataStructure.OrderedSet.GreatestResult.eq_greatest`,
  `Cslib.DataStructure.OrderedSet.greatest_eq_iff`,
  `Cslib.DataStructure.OrderedSet.greatest_eq_max`: the corresponding maximum facts.
* `Cslib.DataStructure.OrderedSet.predecessor_eq_none_iff`,
  `Cslib.DataStructure.OrderedSet.predecessor_eq_some_iff`: the strict predecessor contract.

## References

Uses Mathlib's finite-set minimum, maximum and linear-order API.
-/
@[expose] public section

namespace Cslib.DataStructure.OrderedSet

variable {α : Type*} [LinearOrder α]

/-- A complete optional-minimum contract: `none` means no eligible key exists. -/
def LeastResult (s : Finset α) : Option α → Prop
  | none => s = ∅
  | some a => a ∈ s ∧ ∀ b ∈ s, a ≤ b

/-- The mathematical minimum, independent of any representation. -/
def least (s : Finset α) : Option α :=
  if h : s.Nonempty then some (s.min' h) else none

/-- `least s` satisfies the optional-minimum contract for `s`. -/
theorem least_spec (s : Finset α) : LeastResult s (least s) := by
  unfold least
  split <;> rename_i h
  · exact ⟨Finset.min'_mem s h, fun b hb => Finset.min'_le s b hb⟩
  · exact Finset.not_nonempty_iff_eq_empty.mp h

/-- Every result satisfying the optional-minimum contract for `s` is `least s`. -/
theorem LeastResult.eq_least {s : Finset α} {a : Option α} (h : LeastResult s a) :
    a = least s := by
  cases a with
  | none =>
    have hs : s = ∅ := h
    subst hs
    rfl
  | some a =>
    obtain ⟨ha, hle⟩ := h
    have hs : s.Nonempty := ⟨a, ha⟩
    rw [least, dite_eq_left hs]
    exact congrArg some (le_antisymm (hle _ (Finset.min'_mem s hs)) (Finset.min'_le s a ha))

/-- `least` agrees with `Finset.min` (`WithTop α` is `Option α`). -/
@[simp] theorem least_eq_min (s : Finset α) : (least s : WithTop α) = s.min := by
  unfold least
  split_ifs with h
  · exact Finset.coe_min' h
  · exact (Finset.min_eq_top.mpr (Finset.not_nonempty_iff_eq_empty.mp h)).symm

/-- A complete optional-maximum contract: `none` means no eligible key exists. -/
def GreatestResult (s : Finset α) : Option α → Prop
  | none => s = ∅
  | some a => a ∈ s ∧ ∀ b ∈ s, b ≤ a

/-- The mathematical maximum, independent of any representation. -/
def greatest (s : Finset α) : Option α :=
  if h : s.Nonempty then some (s.max' h) else none

/-- `greatest s` satisfies the optional-maximum contract for `s`. -/
theorem greatest_spec (s : Finset α) : GreatestResult s (greatest s) := by
  unfold greatest
  split <;> rename_i h
  · exact ⟨Finset.max'_mem s h, fun b hb => Finset.le_max' s b hb⟩
  · exact Finset.not_nonempty_iff_eq_empty.mp h

/-- Every result satisfying the optional-maximum contract for `s` is `greatest s`. -/
theorem GreatestResult.eq_greatest {s : Finset α} {a : Option α} (h : GreatestResult s a) :
    a = greatest s := by
  cases a with
  | none =>
    have hs : s = ∅ := h
    subst hs
    rfl
  | some a =>
    obtain ⟨ha, hle⟩ := h
    have hs : s.Nonempty := ⟨a, ha⟩
    rw [greatest, dite_eq_left hs]
    exact congrArg some (le_antisymm (Finset.le_max' s a ha) (hle _ (Finset.max'_mem s hs)))

/-- The optional-maximum contract characterizes `greatest`. -/
theorem greatest_eq_iff {s : Finset α} {a : Option α} : greatest s = a ↔ GreatestResult s a :=
  ⟨fun h => h ▸ greatest_spec s, fun h => h.eq_greatest.symm⟩

/-- `greatest` agrees with `Finset.max` (`WithBot α` is `Option α`). -/
@[simp] theorem greatest_eq_max (s : Finset α) : (greatest s : WithBot α) = s.max := by
  unfold greatest
  split_ifs with h
  · exact Finset.coe_max' h
  · exact (Finset.max_eq_bot.mpr (Finset.not_nonempty_iff_eq_empty.mp h)).symm

/-- The strict predecessor: the greatest key of `s` strictly below `x`, or `none`. -/
def predecessor (s : Finset α) (x : α) : Option α :=
  greatest (s.filter (· < x))

/-- A strict predecessor is absent exactly when every key is at least the query. -/
theorem predecessor_eq_none_iff {s : Finset α} {x : α} :
    predecessor s x = none ↔ ∀ b ∈ s, x ≤ b := by
  simp only [predecessor, greatest_eq_iff, GreatestResult, Finset.filter_eq_empty_iff, not_lt]

/-- A strict predecessor is the greatest key strictly below the query. -/
theorem predecessor_eq_some_iff {s : Finset α} {x a : α} :
    predecessor s x = some a ↔ a ∈ s ∧ a < x ∧ ∀ b ∈ s, b < x → b ≤ a := by
  simp only [predecessor, greatest_eq_iff, GreatestResult, Finset.mem_filter, and_imp, and_assoc]

end Cslib.DataStructure.OrderedSet
