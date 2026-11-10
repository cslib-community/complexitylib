/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The squared cosine of `π / 8`

Mathlib gives `cos (π / 8) = √(2 + √2) / 2` (`Real.cos_pi_div_eight`) and the square
`cos (π / 6) ^ 2 = 3 / 4` (`Real.sq_cos_pi_div_six`). This module records the square
`cos (π / 8) ^ 2 = 1 / 2 + √2 / 4` (`Real.cos_sq_pi_div_eight`), which is the entangled value of the
CHSH game.

## Main results

* `Real.cos_sq_pi_div_eight`: `cos (π / 8) ^ 2 = 1 / 2 + √2 / 4`.
-/

public section

namespace Real

/-- The square of `cos (π / 8)`: `cos (π / 8) ^ 2 = 1 / 2 + √2 / 4`. -/
theorem cos_sq_pi_div_eight : cos (π / 8) ^ 2 = 1 / 2 + √2 / 4 := by
  rw [cos_pi_div_eight, div_pow, sq_sqrt (by positivity)]
  ring

end Real
