/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Polynomial bounds are eventually below exponentials

A polynomially bounded function is eventually smaller than `2 ^ n`
(`PolynomiallyBounded.eventually_lt_two_pow`): exponential lower bounds rule out polynomial upper
bounds. Summing the finitely many exceptions, it is bounded everywhere by a constant multiple of
`2 ^ n` (`PolynomiallyBounded.exists_le_mul_two_pow`).

## Main results

* `Cslib.PolynomiallyBounded.eventually_lt_two_pow`.
* `Cslib.PolynomiallyBounded.exists_le_mul_two_pow`.
-/

@[expose] public section

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
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp.eventually_lt_two_pow
  refine ⟨∑ m ∈ Finset.range N, p m + 1, fun n => ?_⟩
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases le_or_gt N n with hn | hn
  · exact (hN n hn).le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
    exact this.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpow))

end Cslib.PolynomiallyBounded
