/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Small real powers of polynomial bounds

A polynomially bounded natural-valued function has a positive real power that is little-o of
the input. This converts a polynomial increase in input length into a stretched-exponential
size bound in formula hardness magnification.

## Main results

* `Cslib.PolynomiallyBounded.exists_pos_rpow_isLittleO`: some positive power of a polynomially
  bounded function grows sublinearly.
-/

public section

open Filter Asymptotics

namespace Cslib.PolynomiallyBounded

/-- A polynomially bounded function has a positive real power that is little-o of the input.
The exponent depends only on the polynomial bound, not on any later multiplicative constant. -/
theorem exists_pos_rpow_isLittleO {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    ∃ δ : ℝ, 0 < δ ∧
      (fun n => (p n : ℝ) ^ δ) =o[atTop] (fun n => (n : ℝ)) := by
  obtain ⟨d, hd⟩ := polynomiallyBounded_iff_isBigO.mp hp
  have hpow : (fun n : ℕ => (n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (d + 1)) :=
    (isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self d)).comp_tendsto tendsto_natCast_atTop_atTop
  have hpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hsmall := (hd.trans_isLittleO hpow).rpow (inv_pos.mpr hpos)
    (Eventually.of_forall fun n => pow_nonneg (Nat.cast_nonneg n) (d + 1))
  refine ⟨((d + 1 : ℕ) : ℝ)⁻¹, inv_pos.mpr hpos, ?_⟩
  convert hsmall using 1
  ext n
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n), mul_inv_cancel₀ hpos.ne', Real.rpow_one]

end Cslib.PolynomiallyBounded
