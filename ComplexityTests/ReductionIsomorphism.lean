/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction.Isomorphism
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

open Turing.MultiTapeTM Cslib.Complexity

namespace ComplexityTests.ReductionIsomorphism

/-!
### Non-vacuity test: concrete polynomial-time isomorphism

The operation `List.reverse` on `List Bool` under `encBits` is a polynomial-time equivalence
(`reverseEquiv`) because `w.reverse.reverse = w` and `List.reverse` is computable in
polynomial time. Any language `A` is polynomial-time isomorphic to `{w | w.reverse ∈ A}`.
-/

/-- Reversing words is an equivalence on `List Bool`. -/
def reverseEquiv : List Bool ≃ List Bool where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

theorem computableInPolyTime_reverse :
    ComputableInPolyTime List.reverse encBits encBits :=
  ComputableTidilyInPolyTime.bitsReverse.computableInPolyTime

theorem polyTimeIsomorphic_reverse (A : Set (List Bool)) :
    PolyTimeIsomorphic encBits encBits A {w : List Bool | w.reverse ∈ A} := by
  refine ⟨reverseEquiv, ⟨computableInPolyTime_reverse, computableInPolyTime_reverse⟩, fun a => ?_⟩
  simp [reverseEquiv]

/-!
### Non-vacuity test: concrete length-increasing and invertible one-one reduction

Prefixing `true` to a bitstring strictly increases its length and is invertible by `List.tail`.
-/

theorem computableInPolyTime_cons_true :
    ComputableInPolyTime (fun w : List Bool => true :: w) encBits encBits :=
  (ComputableTidilyInPolyTime.bitsCons (ComputableTidilyInPolyTime.const true)
    ComputableTidilyInPolyTime.id').computableInPolyTime

theorem computableInPolyTime_tail :
    ComputableInPolyTime List.tail encBits encBits :=
  ComputableTidilyInPolyTime.bitsTail.computableInPolyTime

theorem polyTimeInvertibleLengthIncreasingOneOneReducible_cons_true (A : Set (List Bool)) :
    PolyTimeInvertibleLengthIncreasingOneOneReducible encBits encBits A
      {w : List Bool | w.tail ∈ A ∧ w.headD false = true} := by
  refine ⟨fun w => true :: w,
    ⟨List.tail, computableInPolyTime_cons_true, computableInPolyTime_tail,
      fun _ => rfl, fun a => ?_⟩, fun a => ?_⟩
  · simp
  · simp

end ComplexityTests.ReductionIsomorphism
