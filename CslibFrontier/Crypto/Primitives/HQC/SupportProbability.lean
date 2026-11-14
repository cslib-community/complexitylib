/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Negligible.Dyadic
public import CslibFrontier.Crypto.Primitives.HQC.SupportDensity
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Statistical error of finite-width HQC support sampling

The existing product lower-density bound gives an additive statistical error for the actual
bounded sampler. The error is `1 - supportLowerDensity.toReal`; it is not an abort probability.
Under `count ≤ n`, the sampler always returns a support of the requested size. Mapping supports
to vectors or continuing an experiment uses the existing `CloseTo.map` and `CloseTo.bind_left`.

## Main results

* `Cslib.Crypto.HQC.supportLowerDensity_le_one`: the lower product is at most one.
* `Cslib.Crypto.HQC.sampleSupport2_closeTo`: the implemented and ideal support laws are close.
* `Cslib.Crypto.HQC.one_sub_supportLowerDensity_le`: an explicit dyadic upper bound on the error.
* `Cslib.Crypto.HQC.negligible_one_sub_supportLowerDensity`: growing width gives negligible error.

## References

These are original consequences of the density estimate already formalized from
[HQC version 5.1][HQC2026], §6.2.3, Proposition 6.2.1, p. 65. The model uses independent fair
words; replacing those words with XOF output is a separate cryptographic obligation.
-/

public section

namespace Cslib.Crypto.HQC

open Finset Probability
open scoped ENNReal

/-- The minimum fibre-count product is a finite number in `[0, 1]`, including empty products. -/
theorem supportLowerDensity_le_one (width n offset count : ℕ) :
    supportLowerDensity width n offset count ≤ 1 := by
  unfold supportLowerDensity
  apply Finset.prod_le_one
  intro j _
  apply ENNReal.div_le_of_le_mul
  simpa only [one_mul] using
    (show ((2 ^ width / (n - (offset + j.val)) * (n - (offset + j.val)) : ℕ) : ℝ≥0∞) ≤
      (2 ^ width : ℕ) from by exact_mod_cast Nat.div_mul_le_self (2 ^ width) _)

/-- Exact finite-width sampling differs from the ideal support law by at most the complement
of its lower density. This is statistical error with no abort term. -/
theorem sampleSupport2_closeTo {width n count : ℕ} (h : count ≤ n) :
    CloseTo (ProbComp.eval (sampleSupport2 width n count))
      (PMF.uniformOfFinset ((range n).powersetCard count)
        (powersetCard_nonempty.mpr (by simpa only [card_range] using h)))
      (ENNReal.ofReal (1 - (supportLowerDensity width n 0 count).toReal)) := by
  have hle := supportLowerDensity_le_one width n 0 count
  have hreal : (supportLowerDensity width n 0 count).toReal ≤ 1 :=
    (ENNReal.toReal_mono (by simp) hle).trans_eq (by simp)
  apply CloseTo.of_le_apply (sub_nonneg.mpr hreal)
  intro S
  rw [sub_sub_cancel, ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) hle)]
  exact (sampleSupport2_density_bounds h S).1

/-- A convenient finite upper bound on the same product error. The product expression in
`sampleSupport2_closeTo` remains available when this coarser estimate is unnecessary. -/
theorem one_sub_supportLowerDensity_le {width n count : ℕ} (h : count ≤ n) :
    1 - (supportLowerDensity width n 0 count).toReal ≤
      (count : ℝ) * n / 2 ^ width := by
  by_cases hc : count = 0
  · subst count
    simp [supportLowerDensity]
  have hM : (0 : ℝ) < 2 ^ width := by positivity
  by_cases hn : n ≤ 2 ^ width
  · have hn' : (n : ℝ) / 2 ^ width ≤ 1 :=
      (div_le_one hM).mpr (by exact_mod_cast hn)
    have hbase : 0 ≤ 1 - (n : ℝ) / 2 ^ width := sub_nonneg.mpr hn'
    have hprod : (1 - (n : ℝ) / 2 ^ width) ^ count ≤
        (supportLowerDensity width n 0 count).toReal := by
      rw [supportLowerDensity_toReal]
      have hfactor (j : Fin count) :
          1 - (n : ℝ) / 2 ^ width ≤
            1 - (2 ^ width % (n - (0 + j.val)) : ℕ) / (2 ^ width : ℝ) := by
        apply sub_le_sub_left
        apply div_le_div_of_nonneg_right _ hM.le
        exact_mod_cast (Nat.mod_lt (2 ^ width) (by have := j.isLt; omega)).le.trans
          (Nat.sub_le n _)
      simpa using Finset.prod_le_prod₀ (s := Finset.univ)
        (fun _ _ => hbase) (fun j _ => hfactor j)
    have hpow := one_add_mul_sub_le_pow (a := 1 - (n : ℝ) / 2 ^ width)
      (by linarith : -1 ≤ 1 - (n : ℝ) / 2 ^ width) count
    rw [mul_div_assoc]
    nlinarith
  · have hn' : (1 : ℝ) ≤ n / 2 ^ width :=
      (le_div_iff₀ hM).mpr (by
        simpa only [one_mul] using
          (show (2 : ℝ) ^ width ≤ n from by exact_mod_cast (Nat.lt_of_not_ge hn).le))
    have hc' : (1 : ℝ) ≤ count := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
    have hbig : (1 : ℝ) ≤ count * (n / 2 ^ width) :=
      one_mul (1 : ℝ) ▸ mul_le_mul hc' hn' (by positivity) (by positivity)
    have hnonneg := ENNReal.toReal_nonneg (a := supportLowerDensity width n 0 count)
    rw [mul_div_assoc]
    linarith

/-- Polynomially bounded support parameters and at least one word bit per security-parameter
unit suffice for negligible sampling error. This does not apply to a fixed 32-bit schedule. -/
theorem negligible_one_sub_supportLowerDensity {width n count : ℕ → ℕ}
    (h : ∀ s, count s ≤ n s) (hn : PolynomiallyBounded n) (hc : PolynomiallyBounded count)
    (hwidth : ∀ s, s ≤ width s) :
    Negligible (fun s => Real.toNNReal (1 - (supportLowerDensity (width s) (n s) 0
      (count s)).toReal)) := by
  apply negligible_of_le
    ((negligible_inv_two_pow_comp_of_le hwidth).polynomiallyBounded_mul (hc.mul hn))
  intro s
  apply (Real.toNNReal_le_iff_le_coe).mpr
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_mul, div_eq_mul_inv] using
    one_sub_supportLowerDensity_le (width := width s) (h s)

end Cslib.Crypto.HQC
