/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/Padics/RingHoms.lean`)

public import Complexity.Init
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Reducing `p`-integral rationals modulo `p ^ n`

The rationals whose denominator is prime to `p` form the valuation ring `ℤ_(p)` of
`Rat.padicValuation p`. It embeds in the `p`-adic integers (`Rat.padicIntegerToPadicInt`), so
it has reductions modulo every power of `p` (`Rat.padicIntegerToZModPow`). On `a / b` with `b`
prime to `p`, the reduction is `a * b⁻¹`: it is characterized by
`Rat.padicIntegerToZModPow_mul_den`.

This reduces the integral local coordinates of the Cauchy kernel of [OpenAI2026ETH] (Lemma D.4,
pp. 59–60), whose coefficients lie in `ℤ_(2)`, modulo the working precision `2 ^ p`.

## Main definitions

* `Rat.padicIntegerToPadicInt`: the inclusion `ℤ_(p) → ℤ_[p]`.
* `Rat.padicIntegerToZModPow`: reduction `ℤ_(p) → ZMod (p ^ n)`.

## Main results

* `Rat.padicIntegerToZModPow_mul_den`: the reduction of `x` times the denominator of `x` is the
  numerator of `x`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.3, pp. 59–60.
-/

public section

namespace Rat

variable (p : ℕ) [Fact p.Prime]

/-- The inclusion of the `p`-integral rationals `ℤ_(p)` in the `p`-adic integers. -/
noncomputable def padicIntegerToPadicInt : (Rat.padicValuation p).integer →+* ℤ_[p] where
  toFun x := ⟨(x : ℚ), Padic.norm_rat_le_one (Rat.padicValuation_le_one_iff.mp x.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by push_cast; rfl)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by push_cast; rfl)

@[simp]
theorem coe_padicIntegerToPadicInt (x : (Rat.padicValuation p).integer) :
    ((padicIntegerToPadicInt p x : ℤ_[p]) : ℚ_[p]) = ((x : ℚ) : ℚ_[p]) := by
  simp only [padicIntegerToPadicInt]
  rfl

/-- Reduction of the `p`-integral rationals modulo `p ^ n`. -/
noncomputable def padicIntegerToZModPow (n : ℕ) : (Rat.padicValuation p).integer →+* ZMod (p ^ n) :=
  (PadicInt.toZModPow n).comp (padicIntegerToPadicInt p)

/-- **The reduction of `a / b` is `a * b⁻¹`**: multiplied by the denominator it gives the
numerator. -/
theorem padicIntegerToZModPow_mul_den (n : ℕ) (x : (Rat.padicValuation p).integer) :
    padicIntegerToZModPow p n x * ((x : ℚ).den : ZMod (p ^ n)) = ((x : ℚ).num : ZMod (p ^ n)) := by
  have h : x * ((x : ℚ).den : (Rat.padicValuation p).integer) =
      ((x : ℚ).num : (Rat.padicValuation p).integer) :=
    Subtype.ext (by push_cast; exact Rat.mul_den_eq_num _)
  simpa only [map_mul, map_natCast, map_intCast] using congrArg (padicIntegerToZModPow p n) h

end Rat
