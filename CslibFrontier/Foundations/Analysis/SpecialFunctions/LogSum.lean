/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The log-sum inequality with uniform weights

For nonnegative reals `x i` over a finite set `s` with total `T`, Jensen's inequality for the convex
function `x ↦ x log x` (Mathlib's `Real.convexOn_mul_log`) gives `T log (T / #s) ≤ ∑ x log x`.
Equivalently, the entropy of the distribution `x / T` is at most `log #s`. No nonemptiness or
positivity hypothesis is needed: an empty `s` or a zero total makes the left side `0`.

## Main results

* `Real.sum_mul_log_div_card_le`: `T log (T / #s) ≤ ∑ i ∈ s, x i log (x i)`.
-/

public section

namespace Real

open Finset

/-- **Log-sum inequality** with uniform weights, from Jensen's inequality for `x log x`: for
nonnegative `x` over `s` with total `T = ∑ i ∈ s, x i`,
`T log (T / #s) ≤ ∑ i ∈ s, x i log (x i)`. -/
theorem sum_mul_log_div_card_le {ι : Type*} (s : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, x i) * log ((∑ i ∈ s, x i) / #s) ≤ ∑ i ∈ s, x i * log (x i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hc : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have h := convexOn_mul_log.map_sum_le (t := s) (w := fun _ => (#s : ℝ)⁻¹) (p := x)
    (fun _ _ => by positivity) (by simp [hc.ne']) hx
  simp only [smul_eq_mul, ← mul_sum] at h
  rw [show (#s : ℝ)⁻¹ * ∑ i ∈ s, x i = (∑ i ∈ s, x i) / #s by ring] at h
  have h2 := mul_le_mul_of_nonneg_left h hc.le
  rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne', ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2

end Real
