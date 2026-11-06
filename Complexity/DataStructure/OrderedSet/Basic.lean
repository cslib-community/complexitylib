/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Finset.Max

/-!
# Optional minima of finite ordered sets

The least-result contract includes absence: `none` means the eligible set is empty. It is
independent of any tree, storage representation or cost model.

## Main definitions

* `Cslib.DataStructure.OrderedSet.LeastResult`: a complete optional-minimum contract.
* `Cslib.DataStructure.OrderedSet.least`: the mathematical minimum of a finite set.

## Main results

* `Cslib.DataStructure.OrderedSet.least_spec`: the mathematical minimum satisfies the contract.
* `Cslib.DataStructure.OrderedSet.LeastResult.eq_least`: any satisfying result equals that minimum.
* `Cslib.DataStructure.OrderedSet.least_eq_min`: `least` agrees with `Finset.min`.

## References

Uses Mathlib's finite-set minimum and linear-order API.
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
  have hs := least_spec s
  cases a with
  | none =>
    cases he : least s with
    | none => rfl
    | some b =>
      simp only [he, LeastResult] at hs
      simp only [LeastResult] at h
      simp [h] at hs
  | some a =>
    cases he : least s with
    | none =>
      simp only [he, LeastResult] at hs
      simp only [LeastResult] at h
      simp [hs] at h
    | some b =>
      simp only [he, LeastResult] at hs
      simp only [LeastResult] at h
      exact congrArg some (le_antisymm (h.2 b hs.1) (hs.2 _ h.1))

/-- `least` agrees with `Finset.min` (`WithTop α` is `Option α`). -/
@[simp] theorem least_eq_min (s : Finset α) : (least s : WithTop α) = s.min := by
  unfold least
  split_ifs with h
  · exact Finset.coe_min' h
  · exact (Finset.min_eq_top.mpr (Finset.not_nonempty_iff_eq_empty.mp h)).symm

end Cslib.DataStructure.OrderedSet
