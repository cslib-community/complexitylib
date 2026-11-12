/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Data.List.OfFn

/-!
# Injectivity of fixed-width low-order bits

Two naturals below `2 ^ w` with the same `w` low-order bits (`lowBits`) are equal. Encodings
that write a bounded number into a fixed-width field use this to decode the field uniquely.

## Main results

* `Cslib.BitString.lowBits_injective_of_lt`: `lowBits w` is injective below `2 ^ w`.
-/

public section

namespace Cslib.BitString

/-- `lowBits w` is injective on naturals strictly below `2 ^ w`. -/
theorem lowBits_injective_of_lt {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : lowBits w a = lowBits w b) : a = b := by
  rw [lowBits_eq_ofFn, lowBits_eq_ofFn] at h
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < w
  · exact congrFun (List.ofFn_injective h) ⟨j, hj⟩
  · have hle : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right Nat.two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hle), Nat.testBit_lt_two_pow (hb.trans_le hle)]

end Cslib.BitString
