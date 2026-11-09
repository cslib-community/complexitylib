/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.ENNReal.Inv

/-!
# Comparing fractions of natural numbers in `ℝ≥0∞`

A probability computed by counting is a fraction `a / b` of natural numbers in `ℝ≥0∞`. Comparing
two such fractions reduces to comparing the cross products in `ℕ`.

## Main results

* `ENNReal.natCast_div_le_natCast_div_iff`: for `b, d ≠ 0`, `a / b ≤ c / d ↔ a * d ≤ b * c`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- Two fractions of natural numbers with nonzero denominators compare in `ℝ≥0∞` as their cross
products compare in `ℕ`: `a / b ≤ c / d ↔ a * d ≤ b * c`. -/
theorem natCast_div_le_natCast_div_iff {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / b ≤ c / d ↔ a * d ≤ b * c := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast hb)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
      (Or.inl (ENNReal.natCast_ne_top _)), mul_comm (c : ℝ≥0∞)]
  exact_mod_cast Iff.rfl

end ENNReal
