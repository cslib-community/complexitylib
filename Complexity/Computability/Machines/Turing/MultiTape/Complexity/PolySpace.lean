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
# Binary-counter certificates

The binary counter `Cslib.BitString.increment` is realized by a two-state transducer.
Its degree and polynomial-time certificates support polynomial-space enumeration;
the plain polynomial-space calculus is in
`Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.increment`: the binary counter in linear time.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.increment`: the binary counter in polynomial time.
-/

@[expose] public section

namespace Turing.MultiTapeTM

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
