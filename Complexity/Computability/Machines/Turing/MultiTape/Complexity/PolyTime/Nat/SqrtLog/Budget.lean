/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# Computing a square-root-logarithm size budget

For a fixed natural `K`, the integer budget `n * Nat.sqrt (Nat.log 2 (n + 2)) / K` is
computable in polynomial time from unary `n`, with unary output. In particular this applies
to the circuit-size budget with `K = 12 * (A + 1)` in `FineGrained.CircuitLowerBoundBudget`.
The theorem includes all integer rounding and does not assume `K` is positive.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_mul_sqrt_log_two_div`: the size budget.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The shifted square-root-logarithm size budget, in unary from unary input, is polynomial-time
computable for every fixed divisor. -/
theorem unary_mul_sqrt_log_two_div (K : ℕ) :
    ComputableInPolyTime (fun n : ℕ => n * Nat.sqrt (Nat.log 2 (n + 2)) / K)
      encUnary encUnary := by
  have hshift : ComputableInPolyTime (fun n : ℕ => n + 2) encUnary encUnary :=
    unary_add' id' (const 2)
  have hlog : ComputableInPolyTime (fun n : ℕ => Nat.log 2 (n + 2)) encUnary encUnary :=
    binary_log_two.comp (unary_to_binary.comp hshift)
  have hsq : ComputableInPolyTime (fun n : ℕ => Nat.sqrt (Nat.log 2 (n + 2)))
      encUnary encUnary :=
    binary_to_unary_bounded (binary_sqrt.comp (unary_to_binary.comp hlog)) hshift
      (fun n => (Nat.sqrt_le_self _).trans (Nat.log_le_self 2 (n + 2)))
  exact unary_div.comp ((unary_mul' id' hsq).prod (const K))

end Turing.MultiTapeTM.ComputableInPolyTime
