/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.SpectralPayment

/-!
# Spare spectral decay from the same logarithmic allocation

Retaining both powers of the allocated walk decay provides a squared payment without
increasing its step count. This is the scalar estimate used by sparse preparation noise.

## Main results

* `Cslib.Probability.spectralWalkLength_squared_payment`: both powers of logarithmic decay.
-/

public section
namespace Cslib.Probability

/-- Retain the spare half of the logarithmic walk allocation. This bound uses the
same length as `spectralWalkLength_payment`, without increasing the computed walk. -/
theorem spectralWalkLength_squared_payment {r C ε : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC : 0 ≤ C) (hε : 0 < ε) (d t : ℕ)
    (ht : spectralWalkLength r C ε d ≤ t) :
    r ^ (2 * t) ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 8 / (C + 1) ^ 2 := by
  have hb : 0 < (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 := by positivity
  have hlog := (Nat.le_ceil (Real.logb r
    ((ε * (64 : ℝ)⁻¹ ^ d) ^ 4 / (C + 1)))).trans
      (show (spectralWalkLength r C ε d : ℝ) ≤ t by exact_mod_cast ht)
  have hp : r ^ t ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 / (C + 1) := by
    have h := (Real.logb_le_iff_le_rpow_of_base_lt_one hr hr1
      (div_pos hb (by positivity))).mp hlog
    rwa [Real.rpow_natCast] at h
  have hsq := pow_le_pow_left₀ (pow_nonneg hr.le t) hp 2
  simpa only [← pow_mul, mul_comm t 2, div_pow, ← pow_mul] using hsq

end Cslib.Probability
