/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Data.Nat.Bitwise.Projection

/-! A foundation-only client for differences, projections, and prefix boundaries. -/

open Cslib.BitString

namespace BitStringProjectionTests

/-- Empty widths, equal words, least/most significant differing bits, projections on empty,
repeated, and unsorted position lists, and prefix boundaries. -/
example :
    (differingBits 0 1 2 = ∅ ∧ highestDiff 0 1 2 = 0 ∧ highestDiff 4 9 9 = 0) ∧
    (highestDiff 4 8 9 = 0 ∧ highestDiff 4 1 8 = 3 ∧ highestDiff 4 5 13 = 3) ∧
    (projectBits [] 9 = 0 ∧ projectBits [0, 0] 1 = 3 ∧
      projectBits [3, 0] 1 = 2 ∧ projectBits [3, 0] 8 = 1) ∧
    (lowerBoundary 13 2 = 11 ∧ upperBoundary 13 2 = 12) := by
  decide

/-- Monotone sketch comparison, `highestDiff_spec` on `5 ≠ 13 < 2 ^ 4`, `projectBits_ofFn_eq_sum`
on `![3, 0]`, and `boundary_prefix` on `(13, 2)`. -/
example :
    sketch {0, 1, 3} 16 < sketch {0, 1, 3} 27 ∧
    (highestDiff 4 5 13 < 4 ∧
      (5 : ℕ).testBit (highestDiff 4 5 13) ≠ (13 : ℕ).testBit (highestDiff 4 5 13) ∧
      ∀ i, highestDiff 4 5 13 < i → (5 : ℕ).testBit i = (13 : ℕ).testBit i) ∧
    projectBits (List.ofFn (![3, 0] : Fin 2 → ℕ)) 9 =
      ∑ i : Fin 2, ((9 : ℕ).testBit (![3, 0] i)).toNat * 2 ^ i.val ∧
    (lowerBoundary 13 2 >>> (2 + 1) = 13 >>> (2 + 1) ∧
      upperBoundary 13 2 >>> (2 + 1) = 13 >>> (2 + 1)) :=
  ⟨sketch_lt_of_highestDiff_mem (w := 5) (by decide) (by decide) (by decide) (by decide),
    highestDiff_spec (w := 4) (x := 5) (y := 13) (by decide) (by decide) (by decide),
    projectBits_ofFn_eq_sum (![3, 0] : Fin 2 → ℕ) 9,
    boundary_prefix 13 2⟩

end BitStringProjectionTests
