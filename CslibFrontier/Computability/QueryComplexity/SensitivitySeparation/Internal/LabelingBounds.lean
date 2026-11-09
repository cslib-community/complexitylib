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

/-!
# Superquadratic sensitivity separation: labeling bounds

Two elementary numerical facts used in the union bound for good labelings: every natural number `M`
is at most the square of `Nat.ceil (Real.sqrt M)`, so this many labels satisfy `M ≤ r ^ 2`, and for
`M ≥ 3` a tournament on `2 * M ^ 2 + 1` vertices has at least `120 = Nat.choose 16 2` ordered pairs
of vertices.

## Main results

* `le_ceil_sqrt_sq`: `M ≤ (Nat.ceil (Real.sqrt M)) ^ 2`.
* `labeling_space_large`: `120 ≤ (2 * M ^ 2 + 1) * (2 * M ^ 2 + 1)` for `3 ≤ M`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/LabelingBounds.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

namespace Internal

/-- Every natural number satisfies `M ≤ (Nat.ceil (Real.sqrt M)) ^ 2`. -/
theorem le_ceil_sqrt_sq (M : ℕ) : M ≤ (Nat.ceil (Real.sqrt M)) ^ 2 := by
  have hs := Nat.le_ceil (Real.sqrt (M : ℝ))
  have hr := Real.sqrt_nonneg (M : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh : (M : ℝ) ≤ (Nat.ceil (Real.sqrt M) : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hh

/-- For `3 ≤ M`, `120 ≤ (2 * M ^ 2 + 1) * (2 * M ^ 2 + 1)`. -/
theorem labeling_space_large {M : ℕ} (hM : 3 ≤ M) :
    120 ≤ (2 * M ^ 2 + 1) * (2 * M ^ 2 + 1) := by
  have : 19 ≤ 2 * M ^ 2 + 1 := by nlinarith
  nlinarith

end Internal

end Cslib.QueryComplexity.SensitivitySeparation
