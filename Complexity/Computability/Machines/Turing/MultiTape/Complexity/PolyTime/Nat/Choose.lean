/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Tactic.PolyTime.Init
public import Mathlib.Data.Nat.Choose.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time binomial coefficients in binary

`n.choose k` is computable in binary (`encNat`) from `(n, k)` in unary (`encPair encUnary encUnary`)
in polynomial time via `n.factorial / (k.factorial * (n - k).factorial)` when `k ≤ n` and `0`
otherwise.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_choose`, `.binary_choose'`: plain polynomial-time
  binomial coefficients from unary `(n, k)` to binary `encNat`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Binomial coefficients `p.1.choose p.2` in binary, from `(p.1, p.2)` in unary. -/
@[fun_prop, program_certificate]
theorem binary_choose :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1.choose p.2)
      (encPair encUnary encUnary) encNat := by
  have hformula : ComputableInPolyTime
      (fun p : ℕ × ℕ =>
        if decide (p.2 ≤ p.1) then p.1.factorial / (p.2.factorial * (p.1 - p.2).factorial) else 0)
      (encPair encUnary encUnary) encNat := by fun_prop
  refine hformula.of_enc_eq fun p => congrArg encNat ?_
  split_ifs with hle
  · exact Nat.choose_eq_factorial_div_factorial (by simpa only [decide_eq_true_eq] using hle)
  · exact Nat.choose_eq_zero_of_lt
      (Nat.lt_of_not_ge (by simpa only [decide_eq_true_eq] using hle))

/-- Binomial coefficient of two computed unary naturals, returned in binary. -/
@[fun_prop, program_certificate]
theorem binary_choose' {α : Type} {input : α ↪ List Bool} {n k : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a => (n a).choose (k a)) input encNat :=
  binary_choose.comp (hn.prod hk)

end Turing.MultiTapeTM.ComputableInPolyTime
