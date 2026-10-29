/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Data.Finset.OrderGlue
import Mathlib.Data.Fin.VecNotation

namespace ComplexityTests.FinsetOrderGlue

open Finset

private def selected : Finset (Fin 5) := {1, 3}

private theorem card_selected : selected.card = 2 := by decide

private def values : Fin 2 → ℤ := ![-3, -7]

private def otherValues : Fin 3 → ℤ := ![11, 0, 5]

/-- Nonconsecutive positions and their complement are both enumerated in increasing order. -/
example : glue selected card_selected values otherValues = ![11, -3, 0, -7, 5] := by
  symm
  apply (eq_glue_iff selected card_selected).mpr
  have hs : (![1, 3] : Fin 2 → Fin 5) = selected.orderEmbOfFin card_selected :=
    orderEmbOfFin_unique card_selected (by decide +kernel) (by decide +kernel)
  have hc : (![0, 2, 4] : Fin 3 → Fin 5) =
      selectedᶜ.orderEmbOfFin (card_compl_of_card_eq selected card_selected) :=
    orderEmbOfFin_unique _ (by decide +kernel) (by decide +kernel)
  constructor
  · rw [← hs]
    decide +kernel
  · rw [← hc]
    decide +kernel

/-- Generic predicate recognition includes a zero value in the complement. -/
example : (univ.filter fun i => glue selected card_selected values otherValues i < 0) =
    selected := by
  apply filter_glue selected card_selected (fun z : ℤ => z < 0)
  · decide +kernel
  · decide +kernel

/-- The named evaluation rules recover values on both enumerations. -/
example : glue selected card_selected values otherValues (selected.orderEmbOfFin card_selected 1)
        = -7 ∧
    glue selected card_selected values otherValues
      (selectedᶜ.orderEmbOfFin (card_compl_of_card_eq selected card_selected) 2) = 5 := by
  simp only [glue_orderEmbOfFin, glue_orderEmbOfFin_compl]
  exact ⟨rfl, rfl⟩

private def optionalValues : Fin 5 → Option ℤ := ![none, some (-3), none, some 7, none]

/-- Reconstruction applies to a generic optional value, without tensor-alphabet vocabulary. -/
example : optionalValues = glue selected card_selected
    (fun k => some ((optionalValues (selected.orderEmbOfFin card_selected k)).getD 0))
    (fun _ => none) := by
  refine eq_glue_of_reconstruct selected card_selected (fun a : Option ℤ => a ≠ none)
    (fromSubset := some) (fromCompl := fun _ : Unit => none)
    (toSubset := fun a => a.getD 0) (toCompl := fun _ => ()) ?_ ?_ ?_
  · rintro (_ | a) ha
    · exact (ha rfl).elim
    · rfl
  · intro a ha
    exact (not_not.mp ha).symm
  · decide +kernel

end ComplexityTests.FinsetOrderGlue
