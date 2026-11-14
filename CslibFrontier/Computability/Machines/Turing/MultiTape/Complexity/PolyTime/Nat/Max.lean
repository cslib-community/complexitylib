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
# Minimum and maximum of unary naturals in polynomial time

Plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates for binary `min` and `max` on unary
naturals, their shared-input composition rules `unary_min'` and `unary_max'`, and the list fold
`unary_foldl_max` (a `max` fold over a framed list of unary naturals never exceeds its initial
value plus the length of the encoded list, so the polynomial-bounded fold applies).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_min`,
  `Turing.MultiTapeTM.ComputableInPolyTime.unary_max`: pairwise `min` and `max` on unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_min'`,
  `Turing.MultiTapeTM.ComputableInPolyTime.unary_max'`: `min` and `max` of two computed unary
  naturals with a shared input context.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_foldl_max`: `l.foldl max init` is
  polynomial-time, in unary.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Take the smaller of two unary naturals. -/
@[fun_prop]
theorem unary_min : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encUnary) encUnary :=
  .of_tidy ComputableTidilyInPolyTime.unary_min

/-- Take the larger of two unary naturals. -/
@[fun_prop]
theorem unary_max : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
    (encPair encUnary encUnary) encUnary :=
  .of_tidy ComputableTidilyInPolyTime.unary_max

/-- Take the smaller of two computed unary naturals with the same full input context. Kept explicit
so `Min.min` search on `encUnary` does not branch against `binary_min_unary'`. -/
theorem unary_min' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => min (left a) (right a)) input encUnary :=
  unary_min.comp (hleft.prod hright)

/-- Take the larger of two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_max' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => max (left a) (right a)) input encUnary :=
  unary_max.comp (hleft.prod hright)

/-- The maximum `l.foldl max init` of a list of unary naturals is polynomial-time, in unary. -/
theorem unary_foldl_max (init : ℕ) :
    ComputableInPolyTime (fun l : List ℕ => l.foldl max init) (encList encUnary) encUnary := by
  refine foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (list := id) (init := fun _ => init) (step := max)
    id' (const init) unary_max (B := fun l => init + (encList encUnary l).length)
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
