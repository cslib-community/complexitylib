/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.ConvolutionSizes
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.DyadicCost

/-!
# Applying the concrete ET allowance at the ordinary host's actual packed side

The original host supplies magnitude `2*(n+2)^E+1` at side `sqrt(8*mPar²)+1`. Both are
its actual argument expressions. The finite dimension bounds transfer this magnitude to a
polynomial in that side, before applying the existing uniform natural ET time theorem.

## Main results

* `exists_packed_dyadicTime_bound`: one coefficient and outer threshold control the natural
  callee allowance at all actual packed dimensions and original polynomial magnitudes.

This original quantitative bridge does not yet bound the repeated outer calls or execute
parameter/prime dispatch. It is not an unconditional subquadratic 3SUM theorem.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.Algorithms.ThreeSum.ChanHe
open Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

/-- The same original input length controls both native packed geometry and its magnitude.
The coefficient and threshold precede every outer input. No magnitude or time certificate
is supplied. -/
theorem exists_packed_dyadicTime_bound (κ E : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      let t := Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1
      (dyadicTime t (2 * (n + 2) ^ E + 1) : ℝ) ≤
        C * (t : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
  obtain ⟨C, hC, N, hN, htime⟩ := exists_dyadicTime_subcubic_bound
    (by omega : 1 ≤ 2 * E + 2)
  refine ⟨C, hC, N ^ 2, ?_⟩
  intro n hn
  exact htime _ (le_packed_side_of_sq_le hn _) _ (packed_weight_le κ E n)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
