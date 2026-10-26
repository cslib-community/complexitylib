/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Noise
public import Complexity.Foundations.BooleanAnalysis.Hypercontractivity.LpNorm
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hypercontractivity of a single bit

A real function of a single uniformly random bit `x = ±1` is `a + b x`, and the noise operator
`T_ρ` turns it into `a + ρ b x`. For `1 ≤ p ≤ 2` and `0 ≤ ρ ≤ √(p - 1)`, the **two-point
inequality** `‖a + ρ b x‖_2 ≤ ‖a + b x‖_p` holds: raised to the power `p`, it reads
`(a ^ 2 + ρ ^ 2 b ^ 2) ^ (p / 2) ≤ (|a + b| ^ p + |a - b| ^ p) / 2`
(`BitString.sq_add_sq_mul_sq_rpow_le`), and it says that a single bit is
`(p, 2, √(p - 1))`-hypercontractive (`BitString.lpNorm_two_noiseOp_le_of_unit`)
[O'Donnell, Theorem 9.18][ODonnell2014].

O'Donnell proves the inequality with the generalized binomial series. Here the two sides are
compared through `1 + p (p - 1) / 2 t ^ 2`, with `t = |b| / |a| ≤ 1`: Bernoulli's inequality bounds
the left side by it, and two monotonicity arguments for derivatives show
`2 + p (p - 1) t ^ 2 ≤ (1 + t) ^ p + (1 - t) ^ p`, using that
`(1 + t) ^ (p - 2) + (1 - t) ^ (p - 2)` is at least `2` when `p ≤ 2`.

## Main results

* `Cslib.BitString.sq_add_sq_mul_sq_rpow_le`: the two-point inequality.
* `Cslib.BitString.lpNorm_two_noiseOp_le_of_unit`: `(p, 2)`-hypercontractivity of a single bit.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Set
open scoped BigOperators

/-! ### The two-point inequality -/

/-- For `p ≤ 2` and `0 < t < 1`, `(1 + t) ^ (p - 2) + (1 - t) ^ (p - 2)` is at least `2`: the
product of the two terms is `(1 - t ^ 2) ^ (p - 2) ≥ 1`. -/
private theorem two_le_one_add_rpow_add_one_sub_rpow {p t : ℝ} (hp : p ≤ 2) (ht : 0 < t)
    (ht' : t < 1) : 2 ≤ (1 + t) ^ (p - 2) + (1 - t) ^ (p - 2) := by
  have hu : 0 < 1 + t := by linarith
  have hv : 0 < 1 - t := by linarith
  have hprod : 1 ≤ (1 + t) ^ (p - 2) * (1 - t) ^ (p - 2) := by
    rw [← Real.mul_rpow hu.le hv.le]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hu hv) (by nlinarith)
      (by linarith)
  have ha := Real.rpow_nonneg hu.le (p - 2)
  have hb := Real.rpow_nonneg hv.le (p - 2)
  nlinarith [sq_nonneg ((1 + t) ^ (p - 2) - (1 - t) ^ (p - 2))]

private theorem hasDerivAt_one_add_rpow (p : ℝ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun t : ℝ => (1 + t) ^ p) (p * (1 + t) ^ (p - 1)) t := by
  simpa using ((hasDerivAt_id t).const_add 1).rpow_const (p := p) (Or.inl (by
    simp only [id_eq]
    linarith))

private theorem hasDerivAt_one_sub_rpow (p : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ p) (-(p * (1 - t) ^ (p - 1))) t := by
  simpa using ((hasDerivAt_id t).const_sub 1).rpow_const (p := p) (Or.inl (by
    simp only [id_eq]
    linarith))

/-- For `1 ≤ p ≤ 2`, `(1 + t) ^ (p - 1) - (1 - t) ^ (p - 1) - 2 (p - 1) t` is monotone on
`[0, 1]`. -/
private theorem monotoneOn_one_add_rpow_sub_one_sub_rpow_sub {p : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) :
    MonotoneOn (fun t : ℝ => (1 + t) ^ (p - 1) - (1 - t) ^ (p - 1) - 2 * (p - 1) * t)
      (Icc 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (f' := fun t => (p - 1) * ((1 + t) ^ (p - 2) + (1 - t) ^ (p - 2) - 2))
    (((((Real.continuous_rpow_const (by linarith)).comp
      (continuous_const.add continuous_id)).sub
      ((Real.continuous_rpow_const (by linarith)).comp
        (continuous_const.sub continuous_id))).sub
      (continuous_const.mul continuous_id)).continuousOn) (fun t ht => ?_) fun t ht => ?_
  · rw [interior_Icc] at ht
    have h := ((hasDerivAt_one_add_rpow (p - 1) (by linarith [ht.1] : -1 < t)).sub
      (hasDerivAt_one_sub_rpow (p - 1) ht.2)).sub ((hasDerivAt_id t).const_mul (2 * (p - 1)))
    convert h.hasDerivWithinAt using 1
    · rfl
    · rw [show p - 1 - 1 = p - 2 by ring]
      ring
  · rw [interior_Icc] at ht
    exact mul_nonneg (by linarith)
      (by linarith [two_le_one_add_rpow_add_one_sub_rpow hp' ht.1 ht.2])

/-- For `1 ≤ p ≤ 2` and `0 ≤ t ≤ 1`, `2 + p (p - 1) t ^ 2 ≤ (1 + t) ^ p + (1 - t) ^ p`: the
right side minus `p (p - 1) t ^ 2` increases from `2`, since its derivative is `p` times
`(1 + t) ^ (p - 1) - (1 - t) ^ (p - 1) - 2 (p - 1) t`, which increases from `0`. -/
private theorem two_add_mul_sq_le_one_add_rpow_add_one_sub_rpow {p t : ℝ} (hp : 1 ≤ p)
    (hp' : p ≤ 2) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    2 + p * (p - 1) * t ^ 2 ≤ (1 + t) ^ p + (1 - t) ^ p := by
  have hψ := monotoneOn_one_add_rpow_sub_one_sub_rpow_sub hp hp'
  -- `φ t = (1 + t) ^ p + (1 - t) ^ p - p (p - 1) t ^ 2` increases from `φ 0 = 2`
  have hφ : MonotoneOn (fun t : ℝ => (1 + t) ^ p + (1 - t) ^ p - p * (p - 1) * t ^ 2)
      (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun t => p * ((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1) - 2 * (p - 1) * t))
      (((((Real.continuous_rpow_const (by linarith)).comp
        (continuous_const.add continuous_id)).add
        ((Real.continuous_rpow_const (by linarith)).comp
          (continuous_const.sub continuous_id))).sub
        (continuous_const.mul (continuous_pow 2))).continuousOn) (fun t ht => ?_) fun t ht => ?_
    · rw [interior_Icc] at ht
      have h := ((hasDerivAt_one_add_rpow p (by linarith [ht.1] : -1 < t)).add
        (hasDerivAt_one_sub_rpow p ht.2)).sub ((hasDerivAt_pow 2 t).const_mul (p * (p - 1)))
      convert h.hasDerivWithinAt using 1
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
      ring
    · rw [interior_Icc] at ht
      have h0 := hψ ⟨le_rfl, zero_le_one⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le
      simp only [add_zero, sub_zero, Real.one_rpow, sub_self, mul_zero] at h0
      exact mul_nonneg (by linarith) h0
  have h := hφ ⟨le_rfl, zero_le_one⟩ ⟨ht, ht'⟩ ht
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at h
  linarith

/-- The two-point inequality for `0 ≤ B ≤ A`. -/
private theorem sq_add_sq_mul_sq_rpow_le_of_le {p ρ A B : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) (hB : 0 ≤ B) (hBA : B ≤ A) :
    (A ^ 2 + ρ ^ 2 * B ^ 2) ^ (p / 2) ≤ ((A + B) ^ p + (A - B) ^ p) / 2 := by
  have hp0 : 0 < p := by linarith
  rcases (hB.trans hBA).eq_or_lt with rfl | hA0
  · obtain rfl : B = 0 := le_antisymm hBA hB
    norm_num [Real.zero_rpow hp0.ne', Real.zero_rpow (half_pos hp0).ne']
  · set t := B / A with ht
    have ht0 : 0 ≤ t := div_nonneg hB hA0.le
    have ht1 : t ≤ 1 := (div_le_one hA0).2 hBA
    have hBt : B = A * t := by rw [ht, mul_div_cancel₀ _ hA0.ne']
    have hs : 0 ≤ (p - 1) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg t)
    calc (A ^ 2 + ρ ^ 2 * B ^ 2) ^ (p / 2)
        ≤ (A ^ 2 * (1 + (p - 1) * t ^ 2)) ^ (p / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [hBt]
          nlinarith [sq_nonneg (A * t)]
      _ = A ^ p * (1 + (p - 1) * t ^ 2) ^ (p / 2) := by
          rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_natCast,
            ← Real.rpow_mul hA0.le, Nat.cast_ofNat, show (2 : ℝ) * (p / 2) = p by ring]
      _ ≤ A ^ p * (((1 + t) ^ p + (1 - t) ^ p) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hA0.le _)
          have hb := rpow_one_add_le_one_add_mul_self (s := (p - 1) * t ^ 2) (by linarith)
            (p := p / 2) (by positivity) (by linarith)
          have h2 := two_add_mul_sq_le_one_add_rpow_add_one_sub_rpow hp hp' ht0 ht1
          nlinarith
      _ = ((A + B) ^ p + (A - B) ^ p) / 2 := by
          rw [hBt, show A + A * t = A * (1 + t) by ring, show A - A * t = A * (1 - t) by ring,
            Real.mul_rpow hA0.le (by linarith), Real.mul_rpow hA0.le (by linarith)]
          ring

/-- The absolute values of `a + b` and `a - b` are `|a| + |b|` and `|a| - |b|`, in some order,
when `|b| ≤ |a|`. -/
private theorem abs_add_rpow_add_abs_sub_rpow {a b : ℝ} (h : |b| ≤ |a|) (p : ℝ) :
    |a + b| ^ p + |a - b| ^ p = (|a| + |b|) ^ p + (|a| - |b|) ^ p := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at h ⊢
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb] at h ⊢
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), add_comm]
    ring_nf
  · rw [abs_of_nonpos ha, abs_of_nonneg hb] at h ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), add_comm]
    ring_nf
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring_nf

/-- **The two-point inequality**: for `1 ≤ p ≤ 2` and `ρ ^ 2 ≤ p - 1`,
`(a ^ 2 + ρ ^ 2 b ^ 2) ^ (p / 2) ≤ (|a + b| ^ p + |a - b| ^ p) / 2`. For a uniformly random bit
`x = ±1` it says `‖a + ρ b x‖_2 ^ p ≤ ‖a + b x‖_p ^ p`, so `x` is
`(p, 2, √(p - 1))`-hypercontractive [O'Donnell, Theorem 9.18][ODonnell2014]. -/
theorem sq_add_sq_mul_sq_rpow_le {p ρ a b : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) (hρ : ρ ^ 2 ≤ p - 1) :
    (a ^ 2 + ρ ^ 2 * b ^ 2) ^ (p / 2) ≤ (|a + b| ^ p + |a - b| ^ p) / 2 := by
  rcases le_total |b| |a| with h | h
  · rw [abs_add_rpow_add_abs_sub_rpow h, ← sq_abs a, ← sq_abs b]
    exact sq_add_sq_mul_sq_rpow_le_of_le hp hp' hρ (abs_nonneg b) h
  · rw [← abs_neg (a - b), neg_sub, add_comm a b, abs_add_rpow_add_abs_sub_rpow h]
    calc (a ^ 2 + ρ ^ 2 * b ^ 2) ^ (p / 2)
        ≤ (|b| ^ 2 + ρ ^ 2 * |a| ^ 2) ^ (p / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [sq_abs, sq_abs]
          have hab : a ^ 2 ≤ b ^ 2 := sq_le_sq.2 h
          nlinarith
      _ ≤ ((|b| + |a|) ^ p + (|b| - |a|) ^ p) / 2 :=
          sq_add_sq_mul_sq_rpow_le_of_le hp hp' hρ (abs_nonneg a) h

/-! ### A single bit -/

/-- The noise operator on a single bit keeps it with probability `(1 + ρ) / 2` and flips it with
probability `(1 - ρ) / 2`. -/
private theorem noiseOp_unit (ρ : ℝ) (g : (Unit → Bool) → ℝ) (b : Bool) :
    noiseOp ρ g (fun _ => b) =
      (1 + ρ) / 2 * g (fun _ => b) + (1 - ρ) / 2 * g (fun _ => !b) := by
  have h : (fun P : Unit → Bool => g ((fun _ => b) + P)) =
      fun P => ∏ i : Unit, (fun (_ : Unit) (c : Bool) => g fun _ => b ^^ c) i (P i) :=
    funext fun P => by
      rw [Fintype.prod_unique]
      exact congrArg g (funext fun _ => Bool.add_eq_xor _ _)
  rw [noiseOp, h]
  refine (bernoulliAverage_prod _ fun (_ : Unit) (c : Bool) => g fun _ => b ^^ c).trans ?_
  rw [Fintype.prod_unique, Bool.xor_false, Bool.xor_true]
  ring

/-- **`(p, 2)`-hypercontractivity of a single bit**: for `1 ≤ p ≤ 2` and `0 ≤ ρ ≤ √(p - 1)`,
`‖T_ρ f‖_2 ≤ ‖f‖_p` for every function `f` of one bit [O'Donnell, Theorem 9.18][ODonnell2014]. -/
theorem lpNorm_two_noiseOp_le_of_unit {p ρ : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ √(p - 1)) (f : (Unit → Bool) → ℝ) : lpNorm 2 (noiseOp ρ f) ≤ lpNorm p f := by
  have hρ2 : ρ ^ 2 ≤ p - 1 :=
    (pow_le_pow_left₀ hρ hρ' 2).trans (Real.sq_sqrt (by linarith)).le
  set A := f fun _ => false
  set B := f fun _ => true
  have key := sq_add_sq_mul_sq_rpow_le (a := (A + B) / 2) (b := (A - B) / 2) hp hp' hρ2
  rw [show (A + B) / 2 + (A - B) / 2 = A by ring, show (A + B) / 2 - (A - B) / 2 = B by ring]
    at key
  have hX : ((noiseOp ρ f fun _ => false) ^ 2 + (noiseOp ρ f fun _ => true) ^ 2) / 2 =
      ((A + B) / 2) ^ 2 + ρ ^ 2 * ((A - B) / 2) ^ 2 := by
    rw [noiseOp_unit, noiseOp_unit, Bool.not_false, Bool.not_true]
    ring
  have hX0 : 0 ≤ ((A + B) / 2) ^ 2 + ρ ^ 2 * ((A - B) / 2) ^ 2 := by positivity
  rw [lpNorm_two, Fintype.expect_unique_bool, hX, lpNorm, Fintype.expect_unique_bool,
    Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = p / 2 * p⁻¹ by field_simp, Real.rpow_mul hX0]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) key (inv_nonneg.2 (by linarith))

end Cslib.BitString
