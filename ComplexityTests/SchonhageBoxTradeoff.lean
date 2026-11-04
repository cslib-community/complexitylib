/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoffExponent
import Mathlib.Tactic.Linarith

/-!
Concrete threshold, sparse count, empty-depth and nonzero block-parameter clients of
the finite shared-box tradeoff. These tests assert no native execution or final exponent.
-/

set_option linter.hashCommand false

namespace ComplexityTests.SchonhageBoxTradeoff

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage.BoxTradeoff

-- The natural switch rounds upward at the first and next block boundaries.
#guard ninthThreshold 0 = 0
#guard ninthThreshold 1 = 1
#guard ninthThreshold 8 = 1
#guard ninthThreshold 9 = 1
#guard ninthThreshold 10 = 2
#guard ninthThreshold 18 = 2

-- A genuine nonzero sparse query count, rather than a vacuous upper bound.
example : (∑ d ∈ range 2, alpha 9 d) = 82 := by decide +kernel

-- The smallest finite model has a real tile and retained value, even with no coordinates.
example : (tiles 0 0 1).card = 1 ∧ (boxes 0 0 0).card = 1 ∧ alpha 0 0 = 1 := by
  decide +kernel

-- An order threshold beyond the inner depth gives an empty retained-count tail.
example : (∑ d ∈ Icc 2 1, (beta 21 1 d : ℝ)) = 0 := by simp

-- All admission premises are discharged at positive block depth. The same rational gain
-- bounds both shared encodings and one nonzero query occurrence.
example :
    (numBands 189 9 (D 9 ^ 18) : ℝ) * (10 : ℝ) ^ 189 +
      ∑ d ∈ range 2, (alpha 9 d : ℝ) ≤
        5 * (9 / 20 : ℝ) * (D 9 ^ 18 : ℕ) ^ 2 := by
  have he := encodings_ninth_blocks 1 (D 9 ^ 18) le_rfl
  have hq := queries_ninth_blocks 1 (D 9 ^ 18) 1 (by decide +kernel)
  norm_num only [Nat.mul_one, pow_one, one_mul] at he hq
  nlinarith only [he, hq]

-- The rational exponent conversion is checked at a positive block depth.
example : (9 / 20 : ℝ) ≤ (D 9 : ℝ) ^ (-(8 / 125 : ℝ)) := by
  simpa only [pow_one, Nat.mul_one] using decay_le_rpow 1

-- The complete natural-cost shape at zero depth has a real tile, table and query.
example :
    ((1 + 1 * D 0 + 1 + 2 ^ 0 +
      (numBands 0 0 1 + 1) * 10 ^ 0 +
      numBands 0 0 1 ^ 2 * ((boxes 0 0 0).card + 1) +
      1 * (∑ d ∈ range 1, alpha 0 d) : ℕ) : ℝ) ≤
        80 * ((0 : ℕ) + 1 : ℝ) * (9 / 20 : ℝ) ^ 0 * (1 : ℝ) ^ 2 := by
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.cast_one] using
    nativeShape_ninth_blocks 0 1 1 (by decide +kernel) (by decide +kernel)

end ComplexityTests.SchonhageBoxTradeoff
