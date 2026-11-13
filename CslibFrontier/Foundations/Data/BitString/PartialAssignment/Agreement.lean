/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PartialAssignment

/-!
# Agreement after fixing another coordinate

`Agrees.update` records an input's answer while preserving agreement. If the queried coordinate
was free, `agrees_update_iff_of_eq_none` characterizes the resulting residual subcube.
-/

public section

namespace Cslib.BitString.PartialAssignment

variable {ι : Type*} [DecidableEq ι] {ρ : PartialAssignment ι} {x : ι → Bool}

/-- Recording an input's answer preserves its agreement with a partial assignment. -/
theorem Agrees.update (hx : ρ.Agrees x) {i : ι} {b : Bool} (hi : x i = b) :
    Agrees (Function.update ρ i (some b)) x := by
  apply agrees_iff_fill_eq.mpr
  rw [fill_update, agrees_iff_fill_eq.mp hx, ← hi, Function.update_eq_self]

/-- Fixing a previously free coordinate imposes precisely its answer in addition to the
existing partial assignment. -/
theorem agrees_update_iff_of_eq_none {i : ι} (hi : ρ i = none) (b : Bool) (x : ι → Bool) :
    Agrees (Function.update ρ i (some b)) x ↔ ρ.Agrees x ∧ x i = b := by
  refine ⟨fun hx => ⟨?_, hx i b (Function.update_self ..)⟩,
    fun ⟨hx, hxi⟩ => hx.update hxi⟩
  intro j c hj
  have hji : j ≠ i := by
    rintro rfl
    simp [hi] at hj
  exact hx j c (by rw [Function.update_of_ne hji]; exact hj)

end Cslib.BitString.PartialAssignment
