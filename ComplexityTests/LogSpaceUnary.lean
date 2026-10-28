/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
# Tests for unary arithmetic in logarithmic space

Composite arithmetic on unary numbers and list lengths, discharged by `fun_prop` alone with the
instances of
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/CounterProgram/Unary.lean`.
-/

namespace ComplexityTests.LogSpaceUnary

open Turing Turing.MultiTapeTM

/-- A polynomial with a truncated difference, in unary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.1 + (p.2 - p.1))
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- A constant factor on the left, by `unaryMul` with a constant. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => 3 * p.1 + p.2 * 2)
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- Quotient and remainder, combined with minimum and maximum. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => max (p.1 / p.2) (min (p.1 % p.2) 3))
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- A comparison of composite values, used as the condition of an `if`. -/
example : ComputableInLogSpace
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ p.1 + p.2 then p.1 else p.2 * p.2)
    (encPair encUnary encUnary) encUnary := by
  fun_prop

/-- Equality and strict comparison of products, as Booleans. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => decide (p.1 * p.2 = p.2) && decide (p.1 < p.2))
    (encPair encUnary encUnary) encBool := by
  fun_prop

/-- A unary product, in binary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.2) (encPair encUnary encUnary) encNat :=
  ComputableInLogSpace.unaryToBinary (by fun_prop)

/-- A polynomial given directly as a counter-program expression, in binary. -/
example : ComputableInLogSpace (fun p : ℕ × ℕ => p.1 * p.1 + p.2) (encPair encUnary encUnary)
    encNat :=
  CounterProgram.Unary.computableInLogSpace_binary (F := fun a b => a * a + b)
    (.add (.mul (.reg 0) (.reg 0)) (.reg 1)) 2 (fun _ _ => rfl) fun a b => by nlinarith

/-- Comparing the length of a list with its head. -/
example : ComputableInLogSpace (fun l : List ℕ => decide (l.length * l.length ≤ l.headD 0))
    (encList encUnary) encBool := by
  fun_prop

end ComplexityTests.LogSpaceUnary
