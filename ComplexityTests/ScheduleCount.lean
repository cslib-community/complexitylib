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

-- At `s = 16` the depth is at most `⌊log₂ 16⌋ = 4`; one constant serves every depth and size.
example (C : ℕ) : ∃ K, ∀ D ≤ Nat.log 2 16,
    Nat.recursionBound (fun d => 2 ^ (2 * Nat.log 2 16 + branchExponent C 16 d)) D 0 ≤
      2 ^ (K * 16 / Nat.sqrt (Nat.log 2 16)) := by
  obtain ⟨K, hK⟩ := exists_recursionBound_le C
  exact ⟨K, fun D hD => hK 16 D (by norm_num) hD⟩

end ComplexityTests.ScheduleCount
