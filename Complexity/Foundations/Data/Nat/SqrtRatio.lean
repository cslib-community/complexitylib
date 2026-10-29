/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Computing a floor involving a square root

## Main results

* `Nat.sqrt_div_eq_floor_div_sqrt`: the floor of `a / sqrt b` is the natural square root
  of `a² / b`, including the zero-denominator convention.

This elementary arithmetic bridge is original adaptation code. It lets finite algorithms use
integer arithmetic while retaining their real-valued capacity specifications.
-/

public section

namespace Nat

/-- A computable integer formula for the floor of a quotient by a square root. -/
theorem sqrt_div_eq_floor_div_sqrt (a b : ℕ) :
    Nat.sqrt (a ^ 2 / b) = ⌊(a : ℝ) / Real.sqrt b⌋₊ := by
  by_cases hb : b = 0
  · simp [hb]
  have hb0 : 0 < b := Nat.pos_of_ne_zero hb
  have hs : 0 < Real.sqrt (b : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hb0)
  apply eq_of_forall_le_iff
  intro k
  rw [Nat.le_sqrt', Nat.le_div_iff_mul_le hb0, Nat.le_floor_iff (by positivity),
    le_div_iff₀ hs]
  have hcast : k ^ 2 * b ≤ a ^ 2 ↔ (k : ℝ) ^ 2 * (b : ℝ) ≤ (a : ℝ) ^ 2 := by
    norm_cast
  rw [hcast, ← sq_le_sq₀ (show (0 : ℝ) ≤ k * Real.sqrt b by positivity) (Nat.cast_nonneg a)]
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg b)]

end Nat
