/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Log

/-!
# Integer magnitude and binary logarithms

## Main results

* `Int.abs_lt_two_pow_log_succ`: a natural magnitude bound supplies enough binary digits.
-/

@[expose] public section

namespace Int

/-- An integer bounded in magnitude by `U` has magnitude below `2^(log₂ U+1)`, including
`U = 0`. This is the scalar consequence of `Nat.lt_pow_succ_log_self`. -/
theorem abs_lt_two_pow_log_succ {U : ℕ} (x : ℤ) (hx : |x| ≤ U) :
    |x| < 2 ^ (Nat.log 2 U + 1) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) U
  have hcast : (U : ℤ) < 2 ^ (Nat.log 2 U + 1) := by exact_mod_cast h
  exact hx.trans_lt hcast

end Int
