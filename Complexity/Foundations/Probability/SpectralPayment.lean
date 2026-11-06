/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite spectral payments

An explicit natural logarithmic ceiling pays a nonnegative coefficient times spectral decay
at every larger step count. Positive tolerance is required. This controls centered noise,
not mean bias or recursive resources. The proof generalizes the second-signal payment;
compression proof patterns retain Samuel Schlesinger's adapted credit.

## Main definitions

* `Cslib.Probability.spectralWalkLength`: sufficient finite logarithmic steps.

## Main results

* `Cslib.Probability.spectralWalkLength_payment`: every larger step count pays the tolerance.
-/

public section

namespace Cslib.Probability

/-- Sufficient finite steps for a positive fourth-power dyadic tolerance. The added one
handles zero coefficients without division by zero. -/
@[expose] noncomputable def spectralWalkLength (r C ε : ℝ) (slack : ℕ) : ℕ :=
  ⌈Real.logb r ((ε * (64 : ℝ)⁻¹ ^ slack) ^ 4 / (C + 1))⌉₊

/-- Every larger step count pays the tolerance. No finite exact-mixing claim at ε=0. -/
theorem spectralWalkLength_payment {r C ε : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC : 0 ≤ C) (hε : 0 < ε) (slack steps : ℕ)
    (hsteps : spectralWalkLength r C ε slack ≤ steps) :
    C * r ^ (2 * steps) ≤ (ε * (64 : ℝ)⁻¹ ^ slack) ^ 4 := by
  let b : ℝ := (ε * (64 : ℝ)⁻¹ ^ slack) ^ 4
  have hb : 0 < b := by dsimp only [b]; positivity
  have hlog : Real.logb r (b / (C + 1)) ≤ (steps : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hsteps)
  have hpow : r ^ steps ≤ b / (C + 1) := by
    have := (Real.logb_le_iff_le_rpow_of_base_lt_one hr hr1
      (div_pos hb (by positivity))).mp hlog
    rwa [Real.rpow_natCast] at this
  have hp : r ^ (2 * steps) ≤ b / (C + 1) :=
    (pow_le_pow_of_le_one hr.le hr1.le (by omega : steps ≤ 2 * steps)).trans hpow
  calc
    _ ≤ C * (b / (C + 1)) := mul_le_mul_of_nonneg_left hp hC
    _ ≤ b := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
      nlinarith [hb.le]

/-- Calibrate a fourth-moment tolerance by any explicit nonnegative payment. -/
theorem calibrated_fourth_moment {payment ε : ℝ} (hp : 0 ≤ payment) (hε : 0 < ε) :
    payment * (ε / (1 + payment)) ^ 4 ≤ ε ^ 4 := by
  have hden : 0 < 1 + payment := by linarith
  have ht : 0 < ε / (1 + payment) := div_pos hε hden
  have hte : ε / (1 + payment) ≤ ε := (div_le_iff₀ hden).mpr (by nlinarith)
  have hce : payment * (ε / (1 + payment)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  calc
    payment * (ε / (1 + payment)) ^ 4 =
      (payment * (ε / (1 + payment))) * (ε / (1 + payment)) ^ 3 := by ring
    _ ≤ ε * ε ^ 3 := mul_le_mul hce (pow_le_pow_left₀ ht.le hte 3) (by positivity) hε.le
    _ = ε ^ 4 := by ring

end Cslib.Probability
