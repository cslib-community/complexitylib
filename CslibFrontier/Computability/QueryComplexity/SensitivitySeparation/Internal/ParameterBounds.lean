/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: parameter bounds

Real-number estimates on the size parameter `M` under the hypotheses `1 ≤ d` and `9 ^ (d + 1) ≤ M`.
The label count `r = max (Nat.ceil (Real.sqrt M)) 16` is at most `2 * Real.sqrt M`, so the relative
label budget satisfies `r / M ≤ 2 / Real.sqrt M ≤ 2 / 3 ^ (d + 1)`; equivalently
`r / M * 3 ^ (d + 1) ≤ 2`, which is the budget condition required by the sensitivity bound of the
construction.

## Main results

* `parameter_ge_eighty_one`: `81 ≤ M`.
* `parameter_epsilon_budget`: `max (Nat.ceil (Real.sqrt M)) 16 / M * 3 ^ (d + 1) ≤ 2`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/ParameterBounds.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

namespace Internal

/-- If `1 ≤ d` and `9 ^ (d + 1) ≤ M`, then `81 ≤ M`. -/
theorem parameter_ge_eighty_one {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    81 ≤ M := by
  have hp : (9 : ℕ) ^ 2 ≤ 9 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact le_trans (by norm_num) (hp.trans hM)

/-- For `81 ≤ M`, `max (Nat.ceil (Real.sqrt M)) 16 ≤ 2 * Real.sqrt M` in `ℝ`. -/
private theorem ceil_sqrt_max_le_two_sqrt {M : ℕ} (hM : 81 ≤ M) :
    (max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) ≤ 2 * Real.sqrt (M : ℝ) := by
  have hs : (9 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact le_trans (by norm_num) (show (81 : ℝ) ≤ M by exact_mod_cast hM)
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (M : ℝ))
  rw [Nat.cast_max, Nat.cast_ofNat]
  exact max_le (by linarith) (by linarith)

/-- If `9 ^ (d + 1) ≤ M`, then `3 ^ (d + 1) ≤ Real.sqrt M`. -/
private theorem parameter_sqrt_lower {d M : ℕ} (hM : 9 ^ (d + 1) ≤ M) :
    (3 : ℝ) ^ (d + 1) ≤ Real.sqrt (M : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  calc
    ((3 : ℝ) ^ (d + 1)) ^ 2 = ((3 : ℝ) ^ 2) ^ (d + 1) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ = (9 : ℝ) ^ (d + 1) := by norm_num
    _ ≤ M := by exact_mod_cast hM

/-- If `1 ≤ d` and `9 ^ (d + 1) ≤ M`, then `max (Nat.ceil (Real.sqrt M)) 16 / M * 3 ^ (d + 1) ≤ 2`
in `ℝ`. -/
theorem parameter_epsilon_budget {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ((max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2 := by
  have h81 := parameter_ge_eighty_one hd hM
  have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm := ceil_sqrt_max_le_two_sqrt h81
  have hp := parameter_sqrt_lower hM
  calc
    _ ≤ (2 * Real.sqrt (M : ℝ)) / M * Real.sqrt (M : ℝ) :=
      mul_le_mul (div_le_div_of_nonneg_right hm hpos.le) hp (by positivity) (by positivity)
    _ = 2 := by
      field_simp
      nlinarith [Real.sq_sqrt hpos.le]

end Internal

end Cslib.QueryComplexity.SensitivitySeparation
