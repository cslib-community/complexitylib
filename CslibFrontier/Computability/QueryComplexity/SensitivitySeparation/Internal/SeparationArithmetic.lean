/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Superquadratic sensitivity separation: separation arithmetic

Real arithmetic turning the seed bounds into ratio bounds. A nonconstant function with sensitivity
at most `2 * (d + 2) * M ^ (d + 1)` and block sensitivity at least `M ^ 2 * (2 * M ^ 2 + 1) ^ d` at
the all-false input has `bs / s ^ 2` at least `2 ^ d / (4 * (d + 2) ^ 2)`, a quantity tending to
infinity with `d`. At depth nine this bound equals `128 / 121 > 1`, giving the strict quadratic gap
`(22 * M ^ 10) ^ 2 < M ^ 2 * (2 * M ^ 2 + 1) ^ 9` used for amplification.

## Main results

* `quantitative_ratio_of_bounds`: the seed bounds imply `2 ^ d / (4 * (d + 2) ^ 2) ≤ bs / s ^ 2` at
  the all-false input.
* `depth_nine_seed_ratio`: `128 / 121 ≤ M ^ 2 * (2 * M ^ 2 + 1) ^ 9 / (22 * M ^ 10) ^ 2`.
* `depth_nine_seed_gap`: `1 < 22 * M ^ 10` and `(22 * M ^ 10) ^ 2 < M ^ 2 * (2 * M ^ 2 + 1) ^ 9`.
* `quantitative_ratio_tendsto`: `2 ^ d / (4 * (d + 2) ^ 2)` tends to infinity as `d → ∞`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/SeparationArithmetic.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section
open Filter
open scoped Topology

namespace Internal

/-- For `L ≠ 0` and `M ≠ 0`,
`(M ^ 2 * k ^ d) / (2 * L * M ^ (d + 1)) ^ 2 = (k / M ^ 2) ^ d / (4 * L ^ 2)`. -/
private theorem seed_ratio_identity (d : ℕ) {L M k : ℝ} (hL : L ≠ 0) (hM : M ≠ 0) :
    (M ^ 2 * k ^ d) / (2 * L * M ^ (d + 1)) ^ 2 =
      (k / M ^ 2) ^ d / (4 * L ^ 2) := by
  have hp : (M ^ 2) ^ d = (M ^ d) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 d]
  rw [div_pow, hp, pow_succ]
  field_simp
  ring

/-- For `0 < M`,
`2 ^ d / (4 * (d + 2) ^ 2) ≤ (M ^ 2 * (2 * M ^ 2 + 1) ^ d) / (2 * (d + 2) * M ^ (d + 1)) ^ 2`. -/
private theorem seed_ratio_lower (d : ℕ) {M : ℝ} (hM : 0 < M) :
    (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
      (M ^ 2 * (2 * M ^ 2 + 1) ^ d) /
        (2 * ((d : ℝ) + 2) * M ^ (d + 1)) ^ 2 := by
  rw [seed_ratio_identity d (by positivity) (ne_of_gt hM)]
  have hk : 2 ≤ (2 * M ^ 2 + 1) / M ^ 2 := by
    apply (le_div_iff₀ (pow_pos hM 2)).mpr
    linarith
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hk d) (by positivity)

/-- If `0 < sensitivity f ≤ s` and `0 ≤ b ≤ blockSensitivityAt f (fun _ => false)`, then
`b / s ^ 2 ≤ blockSensitivityAt f (fun _ => false) / sensitivity f ^ 2`. -/
private theorem ratio_of_bounds {I : Type} [Fintype I] (f : (I → Bool) → Bool)
    (s b : ℝ) (hpos : 0 < (sensitivity f : ℝ))
    (hs : (sensitivity f : ℝ) ≤ s) (hb : b ≤ (blockSensitivityAt f (fun _ => false) : ℝ))
    (hb0 : 0 ≤ b) :
    b / s ^ 2 ≤ (blockSensitivityAt f (fun _ => false) : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  have hsp : 0 < s := lt_of_lt_of_le hpos hs
  apply (le_div_iff₀ (pow_pos hpos 2)).mpr
  calc
    _ ≤ (b / s ^ 2) * s ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hs 2) (div_nonneg hb0 (sq_nonneg s))
    _ = b := div_mul_cancel₀ _ (ne_of_gt (pow_pos hsp 2))
    _ ≤ (blockSensitivityAt f (fun _ => false) : ℝ) := hb

/-- If `f` is nonconstant, `0 < M`, `sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1)` and
`M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false)`, then
`2 ^ d / (4 * (d + 2) ^ 2) ≤ blockSensitivityAt f (fun _ => false) / sensitivity f ^ 2`. -/
theorem quantitative_ratio_of_bounds {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (d M : ℕ) (hM : 0 < M)
    (hnc : ∃ x y, f x ≠ f y)
    (hs : sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1))
    (hb : M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false)) :
    (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
      (blockSensitivityAt f (fun _ => false) : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  apply (seed_ratio_lower d hMr).trans
  apply ratio_of_bounds
  · exact_mod_cast sensitivity_pos_of_nonconstant f hnc
  · exact_mod_cast hs
  · exact_mod_cast hb
  · positivity

/-- For `0 < M`, `128 / 121 ≤ M ^ 2 * (2 * M ^ 2 + 1) ^ 9 / (22 * M ^ 10) ^ 2`. -/
theorem depth_nine_seed_ratio {M : ℝ} (hM : 0 < M) :
    (128 : ℝ) / 121 ≤ M ^ 2 * (2 * M ^ 2 + 1) ^ 9 / (22 * M ^ 10) ^ 2 := by
  convert seed_ratio_lower 9 hM using 1 <;> norm_num

/-- For `0 < M`, in `ℕ`, `1 < 22 * M ^ 10` and `(22 * M ^ 10) ^ 2 < M ^ 2 * (2 * M ^ 2 + 1) ^ 9`. -/
theorem depth_nine_seed_gap (M : ℕ) (hM : 0 < M) :
    1 < 22 * M ^ 10 ∧ (22 * M ^ 10) ^ 2 < M ^ 2 * (2 * M ^ 2 + 1) ^ 9 := by
  constructor
  · have hp := pow_pos hM 10
    omega
  · have hp := pow_pos hM 20
    have hmono : M ^ 2 * (2 * M ^ 2) ^ 9 ≤ M ^ 2 * (2 * M ^ 2 + 1) ^ 9 := by
      gcongr
      omega
    calc
      _ = 484 * M ^ 20 := by ring
      _ < 512 * M ^ 20 := by omega
      _ = M ^ 2 * (2 * M ^ 2) ^ 9 := by ring
      _ ≤ _ := hmono

/-- The ratio bound `2 ^ d / (4 * (d + 2) ^ 2)` tends to infinity as `d → ∞`. -/
theorem quantitative_ratio_tendsto :
    Tendsto (fun d : ℕ => (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2)) atTop atTop := by
  have hb := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 2)
  have hz : Tendsto (fun d : ℕ => 4 * ((d : ℝ) + 2) ^ 2 / (2 : ℝ) ^ d)
      atTop (𝓝 0) := by
    have h := hb.const_mul (16 : ℝ)
    convert h using 1
    · funext d
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, pow_add]
      ring
    · simp
  have hr : Tendsto (fun d : ℕ => 4 * ((d : ℝ) + 2) ^ 2 / (2 : ℝ) ^ d)
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, Filter.Eventually.of_forall ?_⟩
    intro d
    change 0 < 4 * ((d : ℝ) + 2) ^ 2 / (2 : ℝ) ^ d
    positivity
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hr

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
