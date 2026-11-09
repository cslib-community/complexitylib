/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Log.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log

/-!
# The strict overshoot of a ceiling-logarithm power

The power `b ^ ⌈log_b n⌉` is at least `n` (`Nat.le_pow_clog`) and, for `n ≠ 0`, strictly less
than `b * n`: the exponent is the least one reaching `n`, so one fewer factor of `b` stays below
`n`. This is the strict sibling of `Nat.pow_clog_le_mul`; it lives in its own small module so
that its clients do not import the `Nat` logarithm hub.

## Main results

* `Nat.pow_clog_lt_mul`: `b ^ ⌈log_b n⌉ < b * n` for `1 < b` and `n ≠ 0`.
-/

@[expose] public section

namespace Nat

/-- The power `b ^ ⌈log_b n⌉` overshoots `n ≠ 0` by strictly less than a factor `b`. -/
theorem pow_clog_lt_mul {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : b ^ clog b n < b * n := by
  rcases (one_le_iff_ne_zero.2 hn).eq_or_lt with rfl | hn
  · simpa using hb
  · have h := pow_pred_clog_lt_self hb hn
    rw [← succ_pred_eq_of_pos (clog_pos hb hn), pow_succ']
    exact Nat.mul_lt_mul_of_pos_left h (by omega)

end Nat
