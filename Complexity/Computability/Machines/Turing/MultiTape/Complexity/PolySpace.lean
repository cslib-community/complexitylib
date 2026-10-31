/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Foundations.Data.BitString.Counter
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Tidy computability within polynomial space

`Turing.MultiTapeTM.ComputableTidilyInPolySpace f encIn encOut`: `f` is tidily computable
(`Turing.MultiTapeTM.ComputableTidilyInO`) within some time and within space polynomially bounded in
the length of the encoded input. Unlike `Turing.MultiTapeTM.ComputableTidilyInPolyTime`, no bound on
the time is imposed. It contains polynomial time. The closure rules (composition, pairing, case
distinction and binary-counted iteration) are stated for the plain predicate
`Turing.MultiTapeTM.ComputableInPolySpace`.

Exhaustive searches within polynomial space enumerate their candidates with the binary counter
`Cslib.BitString.increment`, which is computable in linear time
(`Turing.MultiTapeTM.ComputableTidilyInDegree.increment`).

## Main definitions

* `Turing.MultiTapeTM.ComputableTidilyInPolySpace`: computability within polynomial space.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime`: polynomial time is within
  polynomial space.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.increment`: the binary counter in linear time.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- `f` is tidily computable within some time and within space polynomially bounded in the length
of the encoded input. -/
def ComputableTidilyInPolySpace {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableTidilyInO f encIn encOut T S

namespace ComputableTidilyInPolySpace

variable {α β : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}

/-- **Polynomial time is within polynomial space.** -/
theorem of_polyTime {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    ComputableTidilyInPolySpace f encIn encMid := by
  obtain ⟨d, _, h⟩ := h.exists_degree
  exact ⟨_, _, PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ d) 1 d
    fun a => by simp, h.inO⟩

/-! ### Automation -/

attribute [fun_prop] ComputableTidilyInPolySpace of_polyTime

end ComputableTidilyInPolySpace

/-! ### The binary counter -/

/-- Increment by a two-state transducer, the state being the carry. -/
private def incrementT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrementT_run_false (w : List Bool) : incrementT.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrementT.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrementT_run (w : List Bool) :
    incrementT.run true w = Cslib.BitString.increment w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementT.run (true && b) w = Cslib.BitString.increment (b :: w)
    cases b
    · rw [Bool.true_and, incrementT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- **The binary counter in linear time.** -/
theorem ComputableTidilyInDegree.increment :
    ComputableTidilyInDegree Cslib.BitString.increment encBits encBits 1 1 :=
  .of_linear (incrementT.computableTidilyInLinearTimeAndSpace fun w => by
    rw [show incrementT.q₀ = true from rfl, incrementT_run]; rfl)

/-- The binary counter in polynomial time. -/
@[fun_prop]
theorem ComputableTidilyInPolyTime.increment :
    ComputableTidilyInPolyTime Cslib.BitString.increment encBits encBits :=
  ComputableTidilyInDegree.increment.computableTidilyInPolyTime

end Turing.MultiTapeTM
