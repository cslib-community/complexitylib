/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The pairing function on unary naturals in polynomial time

Mathlib's pairing function `Nat.pair` is a bijection `ℕ × ℕ ≃ ℕ` of polynomial size:
`Nat.pair m n ≤ (max m n + 1) ^ 2`. On unary naturals it is therefore computable in polynomial
time, so pairs and nested tuples of unary naturals can be written as single unary naturals, in
particular as words of a tally language. This module states that fact for `fun_prop`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_pair`: the pairing function, with both arguments
  and the result in unary.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The natural-number pairing function `Nat.pair`, with both arguments and the result in unary. -/
@[fun_prop]
theorem unary_pair :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2) (encPair encUnary encUnary)
      encUnary := by
  unfold Nat.pair
  fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime
