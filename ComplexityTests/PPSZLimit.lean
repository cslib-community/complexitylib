/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.Limit
import ComplexityTests.PPSZUnique
import Mathlib.Analysis.Complex.ExponentialBounds

/-! PPSZ for unique 3-SAT in the limit: the exponent `2 log 2 - 1` lies between `0.38` and `0.39`,
the limit `R3` at sample points, and the headline applied to the uniquely satisfiable 3-CNF formula
of `ComplexityTests.PPSZUnique`. -/

namespace ComplexityTests.PPSZLimit

open Cslib.Logic.PL Cslib.Complexity.PPSZ

/-! ### The exponent -/

example : 2 * Real.log 2 - 1 < 0.39 := by
  linarith [Real.log_two_lt_d9]

example : 0.38 < 2 * Real.log 2 - 1 := by
  linarith [Real.log_two_gt_d9]

/-- The limit improves on depth two: `31 / 70 < 2 - 2 log 2`. -/
example : qbar 3 2 < 2 - 2 * Real.log 2 := by
  rw [qbar_three_two]
  linarith [Real.log_two_lt_d9]

/-! ### The limit `R3` -/

example : R3 0 = 0 := by norm_num [R3]

example : R3 (1 / 3) = 1 / 4 := by norm_num [R3]

example : R3 (3 / 4) = 1 := by norm_num [R3]

-- `1` is a fixed point of the recursion step, so it bounds `R3` from above.
example : R3 (1 / 3) ≤ 1 := R3_le_of_eq ⟨by norm_num, by norm_num⟩ (by norm_num)

/-! ### The headline on a uniquely satisfiable formula -/

/-- For `ε = 1 / 100`, some `w` makes one round succeed on the formula `φ` of
`ComplexityTests.PPSZUnique` with probability at least `2^{-(2 log 2 - 1 + 1/100) * 3}`. -/
example : ∃ w : ℕ, (2 : ℝ) ^ (-((2 * Real.log 2 - 1 + 1 / 100) * 3)) ≤
    ((round PPSZUnique.φ w) fun _ => some true).toReal := by
  obtain ⟨w, hw⟩ := round_success_unique_three_limit (1 / 100) (by norm_num)
  refine ⟨w, ?_⟩
  exact_mod_cast hw 3 PPSZUnique.φ (fun _ => true) PPSZUnique.φ_sat PPSZUnique.φ_unique
    PPSZUnique.φ_len

end ComplexityTests.PPSZLimit
