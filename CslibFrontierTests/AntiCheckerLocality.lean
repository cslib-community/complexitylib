/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Magnification.AntiChecker

/-!
# Tests: Gap-MCSP in a local circuit class

The class form of the Gap-MCSP `[OPS19]` bullet at the smallest gap, `s₂ = n s₁ + 2 + 2 n (n + 2)`,
and non-vacuity of its locality bound: at `s₁ = n` and `n = 100`, each oracle gate reads far fewer
than `2 ^ n` bits, so one gate reading the whole truth table does not meet it.
-/

namespace CslibFrontierTests.AntiCheckerLocality

open Cslib Cslib.MCSP Cslib.Circuits.Boolean

/-- The smallest gap above `s₁ n = n`. -/
private def s₂ (n : ℕ) : ℕ := n * n + 2 + 2 * n * (n + 2)

/-- The class form at the smallest gap above `s₁ n = n`. -/
example : LocalCircuitClass (fun m => m * (610 * s₂ (Nat.log 2 m) ^ 4) + 1)
    (fun m => 5000 * s₂ (Nat.log 2 m) ^ 5) (fun m => 610 * s₂ (Nat.log 2 m) ^ 4 + 1)
    (fun m => 5000 * m * s₂ (Nat.log 2 m) ^ 5 + 1)
    (GapMCSP.yesSet fun n => n) (GapMCSP.noSet s₂) :=
  localCircuitClass_gapMCSP fun _ => le_rfl

/-- Non-vacuity of the locality bound at `n = 100`: each oracle gate reads fewer than `2 ^ 100`
bits. -/
example : 5000 * s₂ 100 ^ 5 < 2 ^ 100 := by
  norm_num [s₂]

/-- At input length `0` the size bound is `1`, which a constant gate meets. -/
example : 5000 * 0 * s₂ (Nat.log 2 0) ^ 5 + 1 = 1 := by
  simp

end CslibFrontierTests.AntiCheckerLocality
