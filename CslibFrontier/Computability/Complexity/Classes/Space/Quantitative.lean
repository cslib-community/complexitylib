/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Deterministic space in the quantitative calculus

A problem is in `Cslib.Complexity.DSPACE enc s` exactly when a Boolean function deciding it is
computable in the quantitative calculus `Turing.MultiTapeTM.ComputableInO` within some time and
within space `O(s n)` on instances whose encoding has length `n`. The two directions
(`Cslib.Complexity.computableInO_indicator_of_mem_DSPACE`,
`Cslib.Complexity.setOf_mem_DSPACE_of_computableInO`) are the space counterparts of the `DTIME`
bridges in `CslibFrontier.Computability.Complexity.Classes.Time`. No time bound is needed: a
machine within the space bound halts within its number of configurations
(`Cslib.Complexity.mem_DSPACE_iff`). Space counts visited work cells, as in `DSPACE`.

## Main results

* `Cslib.Complexity.computableInO_indicator_of_mem_DSPACE`: the indicator of a problem in
  `DSPACE enc s` is computable within some time and space `O(s n)`.
* `Cslib.Complexity.setOf_mem_DSPACE_of_computableInO`: a Boolean function computable within space
  `O(s n)` decides a problem in `DSPACE enc s`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A problem in `DSPACE enc s` is decided by a machine computing its indicator within some time
and within space `O(s n)`, on instances whose encoding has length `n`. -/
theorem computableInO_indicator_of_mem_DSPACE {A : Set α} {s : ℕ → ℕ}
    (h : A ∈ DSPACE enc s) :
    ∃ T : α → ℕ, ComputableInO (indicator A) enc encBool T fun a => s (enc a).length := by
  obtain ⟨c₁, c₂, t, hA⟩ := h
  refine ⟨fun a => t (enc a).length, .of_bounds hA (c₁ + c₂ + 1) (fun a => ?_) (fun a => ?_)
    fun a => ?_⟩
  · nlinarith
  · nlinarith
  · simp only [encBool_apply, List.length_singleton]
    nlinarith

/-- A Boolean function, computable within a space bound of the length of the encoded instance,
decides a problem within that space. -/
theorem setOf_mem_DSPACE_of_computableInO {f : α → Bool} {T S : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInO f enc encBool T S) (hS : ∀ a, S a ≤ s (enc a).length) :
    {a | f a = true} ∈ DSPACE enc s := by
  obtain ⟨c, hc, -⟩ := h
  refine mem_DSPACE_iff.mpr ⟨c, c, fun a => c * (T a + 1),
    decidableInTimeAndSpace_iff.mpr ⟨f, hc.mono (fun _ => le_rfl) fun a => ?_, fun _ => Iff.rfl⟩⟩
  have := Nat.mul_le_mul_left c (hS a)
  rw [Nat.mul_add, Nat.mul_one]
  omega

end Cslib.Complexity
