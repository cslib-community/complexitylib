/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Upper saturation with bounded common loss

Relative error in a scalar becomes absolute error after upper saturation when the common
additive loss is bounded by the saturation scale. There is no upper bound on the true scalar.
This is the scalar estimate used by polynomial row outputs and reusable by two-signal outputs;
it does not change any row, default or compression state.

## Main results

* `Cslib.RowCompression.abs_min_add_sub_min_add_le`: the capped discrepancy is at most
  `(4 * θ + 5) * ε` for relative error `ε ≤ 1 / 2` and common loss of magnitude at most `θ`.
-/

public section

namespace Cslib.RowCompression

/-- A bounded common loss permits upper saturation to turn relative error into absolute error.
The proof is extracted unchanged from `PolynomialAtomRows.ClippedError`. -/
theorem abs_min_add_sub_min_add_le {d raw loss ε : ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 2)
    (hraw : |raw - d| ≤ (1 + d) * ε) (hloss : |loss| ≤ θ) :
    |min θ (raw + loss) - min θ (d + loss)| ≤ (4 * θ + 5) * ε := by
  have hδ : 0 ≤ (4 * θ + 5) * ε := by positivity
  by_cases hdlarge : d ≤ 4 * (θ + 1)
  · apply (abs_min_sub_min_le_max _ _ _ _).trans
    refine max_le (by simpa only [sub_self, abs_zero] using hδ) ?_
    simp only [add_sub_add_right_eq_sub]
    exact hraw.trans (mul_le_mul_of_nonneg_right (by linarith) hε)
  · have hproduct := mul_le_mul_of_nonneg_left hεsmall (by linarith [not_le.mp hdlarge] : 0 ≤ 1 + d)
    have hrawlo := (abs_le.mp hraw).1
    have hlosslo := (abs_le.mp hloss).1
    have hcapraw : θ ≤ raw + loss := by nlinarith [not_le.mp hdlarge]
    have hcaptruth : θ ≤ d + loss := by linarith [not_le.mp hdlarge]
    simpa only [min_eq_left hcapraw, min_eq_left hcaptruth, sub_self, abs_zero] using hδ

end Cslib.RowCompression
