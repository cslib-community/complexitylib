/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
import Cslib.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Polynomial bounds are eventually below exponentials

A polynomially bounded function is eventually smaller than `2 ^ n`
(`PolynomiallyBounded.eventually_lt_two_pow`): exponential lower bounds rule out polynomial upper
bounds. It is therefore bounded everywhere by a constant multiple of `2 ^ n`, the constant
absorbing the finitely many exceptions (`PolynomiallyBounded.exists_le_mul_two_pow`).

## Main results

* `Cslib.PolynomiallyBounded.eventually_lt_two_pow`.
* `Cslib.PolynomiallyBounded.exists_le_mul_two_pow`.
-/

public section

namespace Cslib.PolynomiallyBounded

open Filter

/-- **A polynomially bounded function is eventually below `2 ^ n`.** -/
theorem eventually_lt_two_pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∀ᶠ n in atTop, f n < 2 ^ n := by
  obtain ⟨d, hd⟩ := hf
  filter_upwards [hd, Nat.eventually_mul_pow_le_pow 2 d one_lt_two, eventually_ge_atTop 1]
    with n hn hpow hn1
  have := Nat.pow_pos (n := d) hn1
  omega

/-- A polynomially bounded function is bounded by a constant multiple of `2 ^ n`. -/
theorem exists_le_mul_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    ∃ C, ∀ n, p n ≤ C * 2 ^ n := by
  obtain ⟨C, hC⟩ :=
    Nat.exists_le_add_of_eventually_le (hp.eventually_lt_two_pow.mono fun _ => le_of_lt)
  refine ⟨C + 1, fun n => ?_⟩
  have := hC n
  have := Nat.le_mul_of_pos_right C (Nat.two_pow_pos n)
  rw [Nat.add_one_mul]
  omega

end Cslib.PolynomiallyBounded
