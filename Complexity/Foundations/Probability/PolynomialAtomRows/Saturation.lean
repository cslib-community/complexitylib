/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows
import Mathlib.Tactic.Linarith

/-!
# Common saturation and gate bounds for polynomial rows

Every concrete polynomial entry factor has saturated by its support scale `θ`, and every rank
gate has closed by the same bound. These scalar facts are shared by the static clipped-error
comparison and the iterated sentinel comparison. They do not involve compression schedules.

## Main results

* `Cslib.PolynomialAtomRow.eval_eq_of_entry_ge`: any two first entries at least `θ` give the
  same output at a fixed rank.
* `Cslib.PolynomialAtomRow.gateThreshold_le_scale`: `θ` bounds every rank-gate close threshold.
-/

public section

namespace Cslib.PolynomialAtomRow

variable (kind : PolynomialAtomRow) {θ : ℝ}

/-- All three entry factors have saturated by the common sufficient bound `θ`. -/
theorem eval_eq_of_entry_ge {v v' r : ℝ} (hθ : 0 < θ) (hv : θ ≤ v) (hv' : θ ≤ v') :
    kind.eval θ v r = kind.eval θ v' r := by
  cases kind
  · simp only [eval, polynomialPrepRow4,
      polynomialPrepCutoff4_eq_one hθ (by linarith : 3 * θ / 4 ≤ v),
      polynomialPrepCutoff4_eq_one hθ (by linarith : 3 * θ / 4 ≤ v')]
  · simp only [eval, polynomialAuxCutoff4,
      polynomialSwitch4_of_ge (by linarith : θ / 8 < θ / 4) (by linarith : θ / 4 ≤ v),
      polynomialSwitch4_of_ge (by linarith : θ / 8 < θ / 4) (by linarith : θ / 4 ≤ v')]
  · simp only [eval, polynomialWitnessCutoff4,
      polynomialSwitch4_of_ge (by linarith : 82 * θ / 1000 < 90 * θ / 1000)
        (by linarith : 90 * θ / 1000 ≤ v),
      polynomialSwitch4_of_ge (by linarith : 82 * θ / 1000 < 90 * θ / 1000)
        (by linarith : 90 * θ / 1000 ≤ v')]

/-- The common support scale is above every concrete rank-gate closure threshold. -/
theorem gateThreshold_le_scale (hθ : 0 < θ) : kind.gateThreshold θ ≤ θ := by
  cases kind <;> dsimp only [gateThreshold] <;> linarith

end Cslib.PolynomialAtomRow
