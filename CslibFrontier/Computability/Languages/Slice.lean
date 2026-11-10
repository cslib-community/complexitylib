/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Languages/Slice.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Languages.Slice

/-!
# Slices of Boolean combinations of languages

The slices of the empty and the full language (as `0` or `⊥`, and `⊤`), of complements, unions
and intersections.

## Main results

* `Language.slice_zero`, `Language.slice_bot`, `Language.slice_top`: slices of the empty and full
  languages.
* `Language.slice_compl`, `Language.slice_sup`, `Language.slice_inf`: slices of complements,
  unions, and intersections.
-/

public section

namespace Language

variable {α : Type*} {L M : Language α} {n : ℕ} {x : Fin n → α}

/-- The slices of the empty language `0` are `false` everywhere. -/
@[simp] theorem slice_zero : (0 : Language α).slice n x = false :=
  Bool.eq_false_iff.2 fun h => notMem_zero _ (slice_eq_true_iff.1 h)

/-- The slices of the empty language `⊥` are `false` everywhere. -/
@[simp] theorem slice_bot : (⊥ : Language α).slice n x = false :=
  slice_zero

/-- The slices of the full language `⊤` are `true` everywhere. -/
@[simp] theorem slice_top : (⊤ : Language α).slice n x = true := slice_eq_true_iff.2 trivial

/-- The slice of a complement is the negation of the slice. -/
@[simp] theorem slice_compl : Lᶜ.slice n x = !L.slice n x := by
  cases h : L.slice n x
  · exact slice_eq_true_iff.2 fun hm => by simp [slice_eq_true_iff.2 hm] at h
  · exact Bool.eq_false_iff.2 fun h' => (slice_eq_true_iff.1 h') (slice_eq_true_iff.1 h)

/-- The slice of a union is the disjunction of the slices. -/
@[simp] theorem slice_sup : (L ⊔ M).slice n x = (L.slice n x || M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

/-- The slice of an intersection is the conjunction of the slices. -/
@[simp] theorem slice_inf : (L ⊓ M).slice n x = (L.slice n x && M.slice n x) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, slice_eq_true_iff, slice_eq_true_iff, slice_eq_true_iff]
  exact Iff.rfl

end Language
