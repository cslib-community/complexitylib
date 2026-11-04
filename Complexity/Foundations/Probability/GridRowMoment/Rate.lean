/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.GridRowMoment
import Mathlib.Tactic.Linarith

/-!
# Rounded grid mass and importance bounds

Nominal rates and exact rounded frame masses differ by at most sixteen on the finite
admissible horizon. This gives a width-independent bound for bin importance factors.

## Main results

* `gridMass_bounds`: lower and upper nominal-rate comparisons.
* `gridMass_importance_le`: the importance-weighted bin rate is at most sixteen times
  the larger nominal rate.
-/
public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Cslib Cslib.Probability
variable {P : ℕ} [Fact P.Prime]
/-- Rounded grid masses compare with their nominal rates on the admitted horizon. -/
theorem gridMass_bounds (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent) :
    rate k ≤ gridMass P k ∧ gridMass P k ≤ 16 * rate k := by
  have h := affineRetains_rates (P := P) (H := 4) (horizon_admissible H hk)
    (show ((2 : ℝ) ^ k)⁻¹ ≤ 1 from inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  rw [← side_eq_ceil] at h
  exact ⟨h.2.1, by simpa only [gridMass, rate, show (2 : ℝ) ^ 4 = 16 by norm_num] using h.2.2.1⟩

/-- A bin's literal importance factor costs at most sixteen times the larger rate. -/
theorem gridMass_importance_le (H : Horizon P) {ka i : ℕ}
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent) :
    rate i * (gridMass P ka / gridMass P (max ka i)) ≤ 16 * max (rate i) (rate ka) := by
  have hb := gridMass_bounds H (max_le ha hi)
  have hm := gridMass_bounds H ha
  have hp := (rate_pos (max ka i)).trans_le hb.1
  rw [← mul_div_assoc, div_le_iff₀ hp]
  rcases le_total ka i with h | h
  · rw [max_eq_right h, max_eq_right (rate_antitone h)] at *
    nlinarith [mul_le_mul_of_nonneg_left hm.2 (rate_pos i).le,
      mul_le_mul_of_nonneg_left hb.1 (mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) (rate_pos ka).le)]
  · rw [max_eq_left h, max_eq_left (rate_antitone h)] at *
    nlinarith [mul_le_mul_of_nonneg_left hm.2 (rate_pos i).le,
      mul_le_mul_of_nonneg_left hb.1 (mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) (rate_pos i).le)]

end Matrix.HierarchyParams.H4RankEnvironment
