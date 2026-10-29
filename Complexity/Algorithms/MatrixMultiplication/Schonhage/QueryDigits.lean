/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.MaskTable

/-!
# Packing a wanted output's digits

The binary mask selects inner positions. At each remaining position, consume one digit
from each compressed base-three offset and emit their row-major base-ten digit.
All three numberings put the first coordinate in the least significant place.

## Main definitions

* `QueryDigits.pack`: the arithmetic recurrence computed by the native query encoder.

## Main results

* `QueryDigits.pack_lt`: the packed word occupies at most the original number of digits.

This recurrence and its elementary bounds are original implementation mathematics.
-/

@[expose] public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.QueryDigits

/-- Pack a binary level mask and two compressed base-three offsets into output digits.
Unused high bits and high offset digits are ignored after the specified depth. -/
def pack : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | L + 1, mask, row, col =>
    if mask % 2 = 0 then
      3 * (row % 3) + col % 3 + 10 * pack L (mask / 2) (row / 3) (col / 3)
    else 9 + 10 * pack L (mask / 2) row col

/-- Packing never needs a supplied bound on a partial accumulator or residual input. -/
theorem pack_lt (L mask row col : ℕ) : pack L mask row col < 10 ^ L := by
  induction L generalizing mask row col with
  | zero => simp [pack]
  | succ L ih =>
    have hr := Nat.mod_lt row (by decide : 0 < 3)
    have hc := Nat.mod_lt col (by decide : 0 < 3)
    have ho := ih (mask / 2) (row / 3) (col / 3)
    have hi := ih (mask / 2) row col
    simp only [pack, pow_succ]
    split <;> omega

end Cslib.Algorithms.MatrixMultiplication.Schonhage.QueryDigits
