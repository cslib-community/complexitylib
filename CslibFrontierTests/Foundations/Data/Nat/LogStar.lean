/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Nat.LogStar

/-! Values of the tower of twos and the iterated logarithm at the tower boundaries. -/

namespace ComplexityTests.LogStar

open Nat

example : twoTower 4 = 65536 := by decide

-- The structural tower agrees with Mathlib's `hyperoperation 4 2`, which `decide` cannot evaluate.
example : hyperoperation 4 2 3 = 16 := by
  rw [← twoTower_eq_hyperoperation]
  decide

-- `log* n` is the least `k` with `n ≤ 2 ↑↑ k`, so it steps up just after each tower.
example : logStar 0 = 0 ∧ logStar 1 = 0 ∧ logStar 2 = 1 ∧ logStar 3 = 2 ∧ logStar 4 = 2 := by
  decide
example : logStar 5 = 3 ∧ logStar 16 = 3 ∧ logStar 17 = 4 := by decide
example : logStar 65536 = 4 ∧ logStar 65537 = 5 := by decide

-- Beyond the reach of evaluation, `log*` just above a huge tower.
example : logStar (twoTower 6 + 1) = 7 := by
  rw [logStar_twoTower_add_one]

-- The recursion through `⌈log₂ ·⌉`.
example : logStar 1000 = logStar 10 + 1 := by
  rw [logStar_of_two_le (by decide)]
  decide

-- Three exponentials from `3` stay below the tower of height `3 + log* 3 = 5`.
example : (2 ^ ·)^[3] 3 ≤ twoTower 5 := by
  have h := iterate_two_pow_le_twoTower 3 3
  rwa [show logStar 3 = 2 by decide] at h

end ComplexityTests.LogStar
