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
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The `p`-adic valuation of rationals: integers and reduction modulo `p ^ n`

Two facts about `Rat.padicValuation p`. First, valuations of integers below `p ^ (a + 1)`: such
a nonzero integer has at most `a` factors of `p` (`Rat.padicValuation_pow_le_of_abs_lt`), so adding
`p ^ (a + 1)` does not change its valuation (`Rat.padicValuation_add_pow_of_abs_lt`).

Second, reduction modulo `p ^ n`. The rationals whose denominator is prime to `p` form the
valuation ring `ℤ_(p)` of `Rat.padicValuation p`. It embeds in the `p`-adic integers
(`Rat.padicIntegerToPadicInt`), so it has reductions modulo every power of `p`
(`Rat.padicIntegerToZModPow`). On `a / b` with `b` prime to `p`, the reduction is `a * b⁻¹`: it
is characterized by `Rat.padicIntegerToZModPow_mul_den`.

Both serve the integral local coordinates of the Cauchy kernel of [OpenAI2026ETH] (Lemma D.4,
pp. 59–60): the first shows that its grid is a complete residue system for valuations, and the
second reduces its `ℤ_(2)` coefficients modulo the working precision `2 ^ p`.

## Main definitions

* `Rat.padicIntegerToPadicInt`: the inclusion `ℤ_(p) → ℤ_[p]`.
* `Rat.padicIntegerToZModPow`: reduction `ℤ_(p) → ZMod (p ^ n)`.

## Main results

* `Rat.padicValuation_pow_self`: `v (p ^ k) = exp (-k)`.
* `Rat.padicValuation_pow_le_of_abs_lt`: a nonzero integer below `p ^ (a + 1)` in absolute value
  has valuation at least `v (p ^ a)`.
* `Rat.padicValuation_add_pow_of_abs_lt`: adding `p ^ (a + 1)` to it keeps its valuation.
* `Rat.castHom_comp_padicIntegerToZModPow`: the reductions are compatible.
* `Rat.padicIntegerToZModPow_mul_den`: the reduction of `x` times the denominator of `x` is the
  numerator of `x`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.3, pp. 59–60.
-/

public section

open scoped WithZero

namespace Rat

variable (p : ℕ) [Fact p.Prime]

/-! ### Valuations of integers -/

/-- The `p`-adic valuation of a nonzero integer. -/
theorem padicValuation_intCast_of_ne_zero {x : ℤ} (hx : x ≠ 0) :
    Rat.padicValuation p (x : ℚ) = WithZero.exp (-(padicValInt p x : ℤ)) := by
  simp [Rat.padicValuation, hx, padicValRat.of_int]

/-- The `p`-adic valuation of a power of `p`. -/
theorem padicValuation_pow_self (k : ℕ) :
    Rat.padicValuation p ((p : ℚ) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, Rat.padicValuation_self, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]

variable {p}

/-- **A nonzero integer below `p ^ (a + 1)` in absolute value has at most `a` factors of `p`.** -/
theorem padicValuation_pow_le_of_abs_lt {a : ℕ} {x : ℤ} (hx : x ≠ 0)
    (hlt : |x| < (p : ℤ) ^ (a + 1)) :
    Rat.padicValuation p ((p : ℚ) ^ a) ≤ Rat.padicValuation p (x : ℚ) := by
  rw [padicValuation_pow_self, padicValuation_intCast_of_ne_zero p hx, WithZero.exp_le_exp,
    neg_le_neg_iff]
  by_contra h
  have hdvd : (p : ℤ) ^ (a + 1) ∣ x := (padicValInt_dvd_iff (a + 1) x).mpr (Or.inr (by omega))
  exact absurd (Int.le_of_dvd (abs_pos.mpr hx) ((dvd_abs _ _).mpr hdvd)) (not_le.mpr hlt)

/-- **Adding `p ^ (a + 1)` to a nonzero integer below it in absolute value keeps its valuation.** -/
theorem padicValuation_add_pow_of_abs_lt {a : ℕ} {x : ℤ} (hx : x ≠ 0)
    (hlt : |x| < (p : ℤ) ^ (a + 1)) :
    Rat.padicValuation p ((x : ℚ) + (p : ℚ) ^ (a + 1)) = Rat.padicValuation p (x : ℚ) := by
  refine (Rat.padicValuation p).map_add_eq_of_lt_left (lt_of_lt_of_le ?_
    (padicValuation_pow_le_of_abs_lt hx hlt))
  rw [padicValuation_pow_self, padicValuation_pow_self, WithZero.exp_lt_exp]
  omega

variable (p)

/-! ### Reduction modulo `p ^ n` -/

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

/-- **The reductions are compatible**: reducing modulo `p ^ n` and then modulo `p ^ m`, `m ≤ n`,
is reducing modulo `p ^ m`. -/
theorem castHom_comp_padicIntegerToZModPow {m n : ℕ} (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (padicIntegerToZModPow p n) =
      padicIntegerToZModPow p m := by
  rw [padicIntegerToZModPow, padicIntegerToZModPow, ← RingHom.comp_assoc,
    PadicInt.zmod_cast_comp_toZModPow m n h]

/-- **The reduction of `a / b` is `a * b⁻¹`**: multiplied by the denominator it gives the
numerator. -/
theorem padicIntegerToZModPow_mul_den (n : ℕ) (x : (Rat.padicValuation p).integer) :
    padicIntegerToZModPow p n x * ((x : ℚ).den : ZMod (p ^ n)) = ((x : ℚ).num : ZMod (p ^ n)) := by
  have h : x * ((x : ℚ).den : (Rat.padicValuation p).integer) =
      ((x : ℚ).num : (Rat.padicValuation p).integer) :=
    Subtype.ext (by push_cast; exact Rat.mul_den_eq_num _)
  simpa only [map_mul, map_natCast, map_intCast] using congrArg (padicIntegerToZModPow p n) h

end Rat
