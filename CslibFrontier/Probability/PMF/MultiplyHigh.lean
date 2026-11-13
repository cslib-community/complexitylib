/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.MultiplyHigh
public import CslibFrontier.Probability.PMF.Map

/-!
# Density bounds for multiply-high sampling

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_mul_div_bounds`: scaling a uniform integer below
  `M` into the range below `d` has density between `⌊M/d⌋ d/M` and `(⌊M/d⌋ + 1) d/M`
  relative to the uniform distribution on that range.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

private theorem density_factor_cancel {d M q : ℕ} (hd : 0 < d) :
    ((q * d : ℕ) : ℝ≥0∞) / M * (d : ℝ≥0∞)⁻¹ = (q : ℝ≥0∞) / M := by
  rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
  calc
    (q : ℝ≥0∞) * d * (M : ℝ≥0∞)⁻¹ * (d : ℝ≥0∞)⁻¹ =
        (q : ℝ≥0∞) * (M : ℝ≥0∞)⁻¹ * ((d : ℝ≥0∞) * (d : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne') (ENNReal.natCast_ne_top _),
        mul_one]

/-- The floor and ceiling fibre counts give multiplicative density bounds. The upper bound
deliberately permits one extra preimage even when `d` divides `M`. -/
theorem uniformOfFintype_mul_div_bounds {M d : ℕ} (hM : 0 < M) (hd : 0 < d)
    [NeZero M] [NeZero d] (k : Fin d) :
    (((M / d * d : ℕ) : ℝ≥0∞) / M) * uniformOfFintype (Fin d) k ≤
      ((uniformOfFintype (Fin M)).map
        (fun u => (⟨u.val * d / M, Nat.mul_div_lt_of_lt hM hd u.isLt⟩ : Fin d))) k ∧
    ((uniformOfFintype (Fin M)).map
        (fun u => (⟨u.val * d / M, Nat.mul_div_lt_of_lt hM hd u.isLt⟩ : Fin d))) k ≤
      ((((M / d + 1) * d : ℕ) : ℝ≥0∞) / M) * uniformOfFintype (Fin d) k := by
  rw [uniformOfFintype_map_apply]
  simp only [Fin.ext_iff, Fintype.card_fin, uniformOfFintype_apply]
  rw [density_factor_cancel hd, density_factor_cancel hd]
  obtain ⟨hl, hu⟩ := Nat.card_mul_div_fiber_bounds hM hd k
  constructor
  · exact ENNReal.div_le_div_right (by exact_mod_cast hl) _
  · exact ENNReal.div_le_div_right (by exact_mod_cast hu) _

end Cslib.Probability.PMF
