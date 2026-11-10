/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/MeanInequalitiesPow.lean)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A multiplicative Bernoulli inequality

For `p ≤ 1` and `n : ℕ`, `(1 - p) ^ n * (1 + n * p) ≤ 1`
(`Real.one_sub_pow_mul_one_add_mul_le_one`). By induction on `n`, each factor `1 - p ≥ 0` decreases
`(1 + (n + 1) * p)` below `(1 + n * p) / (1 - p)` because `(n + 1) * p ^ 2 ≥ 0`. For `0 ≤ p ≤ 1`
this bounds `(1 - p) ^ n` from above by `1 / (1 + n * p)`.

## Main results

* `Real.one_sub_pow_mul_one_add_mul_le_one`: `(1 - p) ^ n * (1 + n * p) ≤ 1` for `p ≤ 1`.
* `Real.one_sub_pow_le_one_div_one_add_mul`: `(1 - p) ^ n ≤ 1 / (1 + n * p)` for `0 ≤ p ≤ 1`.
-/

@[expose] public section

namespace Real

/-- A multiplicative form of Bernoulli's inequality: `(1 - p) ^ n (1 + n p) ≤ 1` for `p ≤ 1`. -/
theorem one_sub_pow_mul_one_add_mul_le_one {p : ℝ} (hp : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n * (1 + (n : ℝ) * p) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hnon := mul_nonneg (pow_nonneg (sub_nonneg.mpr hp) n)
      (mul_nonneg (show (0 : ℝ) ≤ n + 1 by positivity) (sq_nonneg p))
    nlinarith

/-- For `0 ≤ p ≤ 1`, `(1 - p) ^ n ≤ 1 / (1 + n p)`. -/
theorem one_sub_pow_le_one_div_one_add_mul {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 / (1 + (n : ℝ) * p) :=
  (le_div_iff₀ (by positivity)).mpr (one_sub_pow_mul_one_add_mul_le_one hp₁ n)

end Real
