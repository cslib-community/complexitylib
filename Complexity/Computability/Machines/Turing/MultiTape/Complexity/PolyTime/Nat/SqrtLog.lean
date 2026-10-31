/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# The clock `2 ^ (K n / √⌊log₂ n⌋)` in polynomial time

For a fixed `K`, the number `2 ^ (K n / √⌊log₂ n⌋)` (in the natural-number scale of
`Complexity/Foundations/Data/Nat/SqrtLog.lean`) is computable in binary in polynomial time from
`n` in unary. Its binary length is at most `K n + 1`. It serves as the fuel of clocked
subexponential algorithms, such as the depth-first recursion of the contraction theorem of
[OpenAI2026ETH] (Appendix D.4.7, p. 64), whose number of calls is `2 ^ O(n / √(log n))`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_two_pow_div_sqrt_log_two`: the clock.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- **The clock `2 ^ (K n / √⌊log₂ n⌋)`**, in binary from `n` in unary. -/
theorem unary_two_pow_div_sqrt_log_two (K : ℕ) :
    ComputableInPolyTime (fun n : ℕ => 2 ^ (K * n / Nat.sqrt (Nat.log 2 n))) encUnary encNat := by
  have hb := unary_to_binary
  have hlog : ComputableInPolyTime (fun n : ℕ => Nat.log 2 n) encUnary encUnary :=
    binary_log_two.comp hb
  have hsq : ComputableInPolyTime (fun n : ℕ => Nat.sqrt (Nat.log 2 n)) encUnary encUnary :=
    binary_to_unary_bounded (binary_sqrt.comp (hb.comp hlog)) id'
      (fun n => (Nat.sqrt_le_self _).trans (Nat.log_le_self 2 n))
  exact binary_two_pow.comp (unary_div.comp ((unary_mul' (const K) id').prod hsq))

end Turing.MultiTapeTM.ComputableInPolyTime
