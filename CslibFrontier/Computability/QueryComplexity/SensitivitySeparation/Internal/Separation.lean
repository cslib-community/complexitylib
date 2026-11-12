/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.SeedAmplification
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: separation

The final separation statements. For each depth `d ≥ 1` there is a nonconstant Boolean function
whose block sensitivity at the all-false input is at least `2 ^ d / (4 * (d + 2) ^ 2)` times the
square of its sensitivity. Consequently block sensitivity is not bounded by `C * sensitivity ^ 2`
for any constant `C`, and there is even a fixed exponent `α > 2` with
`s(f) ^ α ≤ bs(f, 0)` along a family of functions of unbounded block sensitivity. Here
`s(f)` is `sensitivity f` and `bs(f, 0)` is the block sensitivity at the all-false input.

## Main results

* `quantitative_separation`: for `d ≥ 1`, some nonconstant function has
  `bs(f, 0) / s(f) ^ 2 ≥ 2 ^ d / (4 * (d + 2) ^ 2)`.
* `unbounded_quadratic_separation`: for every `C`, some nonconstant function has
  `C * s(f) ^ 2 < bs(f, 0)`.
* `fixed_power_separation`: for a fixed `α > 2`, a family of nonconstant functions with
  `s(F m) ^ α ≤ bs(F m, 0)` and unbounded block sensitivity at the all-false input.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Separation.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- For `1 ≤ d` there is a nonconstant `f : (Fin n → Bool) → Bool` with `0 < n`,
`f (fun _ => false) = false` and
`2 ^ d / (4 * (d + 2) ^ 2) ≤ blockSensitivityAt f (fun _ => false) / sensitivity f ^ 2`. -/
theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivityAt f (fun _ => false) : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  let M : ℕ := 9 ^ (d + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, hn, hf, hnc, hs, hb⟩ := exists_constructed_seed d M hd (by rfl)
  exact ⟨_, f, hn, hf, hnc, quantitative_ratio_of_bounds f d M hM hnc hs hb⟩

/-- For every `C` there is a nonconstant `f : (Fin n → Bool) → Bool` with `0 < n`,
`f (fun _ => false) = false` and `C * sensitivity f ^ 2 < blockSensitivityAt f (fun _ => false)`. -/
theorem unbounded_quadratic_separation (C : ℝ) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivityAt f (fun _ => false) : ℝ) := by
  obtain ⟨d, hd, hlarge⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and
    (quantitative_ratio_tendsto.eventually_gt_atTop C)).exists
  obtain ⟨n, f, hn, hf, hnc, hratio⟩ := quantitative_separation d hd
  have hs : (0 : ℝ) < sensitivity f := by
    exact_mod_cast sensitivity_pos_of_nonconstant f hnc
  exact ⟨n, f, hn, hf, hnc, (lt_div_iff₀ (pow_pos hs 2)).mp (hlarge.trans_le hratio)⟩

/-- There are `α > 2` and Boolean functions `F m` on `n m` variables such that for every `m`,
`0 < n m`, `F m` is nonconstant, vanishes at the all-false input and satisfies
`sensitivity (F m) ^ α ≤ blockSensitivityAt (F m) (fun _ => false)`, while
`blockSensitivityAt (F m) (fun _ => false)` tends to infinity. -/
theorem fixed_power_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ,
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y : Fin (n m) → Bool, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤
            (blockSensitivityAt (F m) (fun _ => false) : ℝ)) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := constructed_power_family
  refine ⟨α, hα, n, F, fun m => ?_, hlim⟩
  obtain ⟨hn, hf, hnc, hpow, -⟩ := hall m
  exact ⟨hn, hf, hnc, hpow⟩

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
