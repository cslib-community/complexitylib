/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.DenseRowRecipes

/-!
# True-input agreement for bounded routed bins

Only the top scale needs an upper input cap. Fine bins extend negative inputs by zero
and otherwise preserve the canonical expression, even above the top cap in atom units.
The adjacent-scale range bound remains the separate `boundedRoutedBinCutoff_mem_Icc` API.
-/
public section
namespace Matrix

/-- Nonnegative matrix-unit inputs below the top cap preserve every canonical routed bin.
No cap at a fine bin's normalized input is required. -/
theorem boundedRoutedBinCutoff_div_eq {χ route : ℝ → ℝ} {b : ℕ → ℝ} {cap w : ℝ}
    (hb : ∀ i, 0 < b i) (hw : 0 ≤ w) (hcap : w ≤ cap * b 0) (i : ℕ) :
    boundedRoutedBinCutoff χ b cap i route (w / b i) =
      routedBinCutoff χ b i route (w / b i) := by
  cases i with
  | zero =>
    exact boundedRoutedBinCutoff_eq (div_nonneg hw (hb 0).le)
        ((div_le_iff₀ (hb 0)).mpr hcap) 0 route
  | succ i => simp [boundedRoutedBinCutoff, not_lt.mpr (div_nonneg hw (hb _).le)]

end Matrix
