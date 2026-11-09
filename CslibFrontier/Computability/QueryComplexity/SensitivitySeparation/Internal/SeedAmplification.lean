/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.ConstructedSeed
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.PowerAmplification
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.SeparationArithmetic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Superquadratic sensitivity separation: seed amplification

Combines the depth-nine seed with `M = 9 ^ 10` and power amplification. The seed has sensitivity at
most `22 * M ^ 10` and block sensitivity at least `M ^ 2 * (2 * M ^ 2 + 1) ^ 9` at the all-false
input, a strict quadratic gap, so its iterated compositions form a family with a fixed exponent
`α > 2` such that `s ^ α ≤ bs`, with ratio `bs / s ^ 2 ≥ (128 / 121) ^ m` and unbounded block
sensitivity.

## Main results

* `constructed_power_family`: a family of nonconstant functions with `s ^ α ≤ bs` for a fixed
  `α > 2`, ratio `bs / s ^ 2 ≥ (128 / 121) ^ m`, and block sensitivity tending to infinity.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/SeedAmplification.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- There are `α > 2` and Boolean functions `F m` on `n m > 0` variables, each nonconstant and
vanishing at the all-false input, such that
`sensitivity (F m) ^ α ≤ blockSensitivityAt (F m) (fun _ => false)` and
`(128 / 121) ^ m ≤ blockSensitivity (F m) / sensitivity (F m) ^ 2` for every `m`, and
`blockSensitivityAt (F m) (fun _ => false)` tends to infinity. -/
theorem constructed_power_family :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ,
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤ (blockSensitivityAt (F m) (fun _ => false) : ℝ) ∧
          ((128 : ℝ) / 121) ^ m ≤
            (blockSensitivity (F m) : ℝ) / (sensitivity (F m) : ℝ) ^ 2) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop := by
  let M : ℕ := 9 ^ 10
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, _, hf, _, hs, hb⟩ := exists_constructed_seed 9 M (by norm_num) (by rfl)
  change sensitivity f ≤ 22 * M ^ 10 at hs
  obtain ⟨hA, hB⟩ := depth_nine_seed_gap M hM
  obtain ⟨hα, hall, hlim⟩ := power_amplification f hf (22 * M ^ 10)
    (M ^ 2 * (2 * M ^ 2 + 1) ^ 9) hs hb hA hB
  refine ⟨_, hα, _, (fun m => iterateFin f m), ?_, hlim⟩
  intro m
  obtain ⟨hn, hzero, hnc, hpow, hratio⟩ := hall m
  refine ⟨hn, hzero, hnc, hpow, ?_⟩
  apply le_trans _ hratio
  apply pow_le_pow_left₀ (by norm_num)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    using depth_nine_seed_ratio hMr

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
