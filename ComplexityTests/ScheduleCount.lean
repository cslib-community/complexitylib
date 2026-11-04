/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.ScheduleCount

/-! # The call count of the contraction recursion

The node bound of a recursion with the schedule's branching factors is `2 ^ O(s / √⌊log₂ s⌋)`,
for every constant `C` and every depth up to `⌊log₂ s⌋`. -/

namespace ComplexityTests.ScheduleCount

open Cslib.Circuits.Frontier.ContractionSchedule

-- At `s = 16` the depth is at most `⌊log₂ 16⌋ = 4`; the constant `245760 C + 37` serves every
-- depth and size.
example (C : ℕ) : ∀ D ≤ Nat.log 2 16,
    Nat.recursionBound (fun d => 2 ^ (2 * Nat.log 2 16 + branchExponent C 16 d)) D 0 ≤
      2 ^ ((245760 * C + 37) * 16 / Nat.sqrt (Nat.log 2 16)) :=
  fun _ hD => recursionBound_le_two_pow_div_sqrt_log_two C (by norm_num) hD

-- The constant is linear in `C`: at `C = 1` it is `245797`.
example : 245760 * 1 + 37 = 245797 := by norm_num

end ComplexityTests.ScheduleCount
