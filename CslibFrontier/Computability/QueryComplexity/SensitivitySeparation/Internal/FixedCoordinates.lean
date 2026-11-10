/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators

/-!
# Superquadratic sensitivity separation: fixed coordinates

This file counts the functions `α → β` between finite types that agree with a given function
`v` on a prescribed finset `s` of coordinates, via an explicit equivalence with the functions on
the complement of `s`. The resulting exact count is used to compute the sizes of labeling events
in which some labels are prescribed.

## Main definitions

* `fixedCoordinatesEquiv`: functions agreeing with `v` on `s` are equivalent to functions on the
  coordinates outside `s`.

## Main results

* `card_fixedCoordinates`: there are `Fintype.card β ^ (Fintype.card α - s.card)` functions
  `α → β` that agree with `v` on `s`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/FixedCoordinates.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

/-- Functions with prescribed coordinates are equivalent to functions on the remaining
coordinates. -/
def fixedCoordinatesEquiv (s : Finset α) (v : α → β) :
    {f : α → β // ∀ i ∈ s, f i = v i} ≃ ({i : α // i ∉ s} → β) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then v i else f ⟨i,h⟩, by
    intro i hi
    simp only [dite_eq_left hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dite_eq_left hi]
      exact (f.property i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.property]

/-- The number of functions `α → β` agreeing with `v` on `s` is
`Fintype.card β ^ (Fintype.card α - s.card)`. -/
theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
