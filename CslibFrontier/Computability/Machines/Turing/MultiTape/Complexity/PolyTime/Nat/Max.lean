/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The maximum of a list of unary naturals

A `max` fold over a framed list of unary naturals never exceeds its initial value plus the length
of the encoded list, so the polynomial-bounded fold applies.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_foldl_max`: `l.foldl max init` is
  polynomial-time, in unary.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The maximum `l.foldl max init` of a list of unary naturals is polynomial-time, in unary. -/
theorem unary_foldl_max (init : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => l.foldl max init) (encList encUnary) encUnary := by
  refine foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (list := id) (init := fun _ => init) (step := max)
    id' (const init) (of_tidy .unary_max) (B := fun l => init + (encList encUnary l).length)
    ((PolyBounded.const init).add .self) (fun l i _ => ?_)
  simp only [encUnary_apply, List.length_replicate]
  refine (List.max_le_iff (l := _ :: _) (by simp)).mpr ?_
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨Nat.le_add_right _ _, fun x hx => ?_⟩
  have hsz := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
    l x (List.mem_of_mem_take hx)
  simp only [encUnary_apply, List.length_replicate] at hsz
  omega

end Turing.MultiTapeTM.ComputableInPolyTime
