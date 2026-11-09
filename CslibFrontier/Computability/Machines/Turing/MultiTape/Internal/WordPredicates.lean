/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool

/-! # Shared finite-state word predicates

The nonempty-word transducer and its degree certificate are shared by direct Option and unary
Degree certificates. Its machine clocks include the whole runtime input; it uses no work tapes.

## Main results

* `Turing.MultiTapeTM.Internal.WordPredicates.computableInDegree_of_nonemptyT`: a Boolean test
  that `nonemptyT` computes on the encoded input, in linear time with output degree zero.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.WordPredicates

/-- Emit a single Boolean indicating whether the input contains a symbol. -/
def nonemptyT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [] else [true])
  final q := if q then [] else [false]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- After the first input symbol, no further output is emitted. -/
lemma nonemptyT_run_true (w : List Bool) : nonemptyT.run true w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [] ++ nonemptyT.run true w = []
    simpa using ih

/-- A Boolean test that `nonemptyT` computes on the encoded input runs in linear time, with
output degree zero. -/
theorem computableInDegree_of_nonemptyT {α : Type*} {enc : α ↪ List Bool} {f : α → Bool}
    (h : ∀ a, encBool (f a) = nonemptyT.run nonemptyT.q₀ (enc a)) :
    ComputableInDegree f enc encBool 1 0 := by
  refine ⟨⟨fun a => 2 * (enc a).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, nonemptyT.toTM, fun a => ?_⟩, ⟨1, fun a => by simp⟩⟩
  simpa only [h a] using nonemptyT.computesInTimeAndSpace_toTM (enc a)

end Turing.MultiTapeTM.Internal.WordPredicates
