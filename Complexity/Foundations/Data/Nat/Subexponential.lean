/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Cslib.Foundations.Data.Nat.Asymptotics

/-!
# Subexponential bounds on natural-valued functions

`SubexponentiallyBounded f` expresses `f(n) = 2^{o(n)}` using the upper binary logarithm of
`f n + 1`. Equivalently, this logarithm is little-o of `n` after casting to the reals. The shift
by one handles zero values without side conditions. This is a growth condition and makes no
computability assertion.

The closure rules show that polynomial expressions in subexponentially bounded functions remain
subexponentially bounded. The concrete bound `f n ≤ 2 ^ (n / d)` for each positive integer `d`
allows purely natural-number estimates in formula hardness magnification.

## Main definitions

* `Cslib.SubexponentiallyBounded`: subexponential growth of a natural-valued function.

## Main results

* `Cslib.subexponentiallyBounded_iff_isLittleO`: the logarithmic little-o characterization.
* `Cslib.SubexponentiallyBounded.add`, `Cslib.SubexponentiallyBounded.mul`,
  `Cslib.SubexponentiallyBounded.pow`: closure under sums, products and fixed powers.
* `Cslib.PolynomiallyBounded.subexponentiallyBounded`: polynomial growth is subexponential.
* `Cslib.SubexponentiallyBounded.eventually_le_two_pow_div`: an eventual bound by every positive
  reciprocal exponential rate.
-/

public section

namespace Cslib

open Filter Asymptotics

/-- A function is subexponentially bounded when every fixed multiple of its upper binary
logarithm is eventually at most the input. -/
@[expose] def SubexponentiallyBounded (f : ℕ → ℕ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in atTop, c * Nat.clog 2 (f n + 1) ≤ n

/-- Subexponential growth is equivalent to the upper binary logarithm being little-o of the
input after casting to the reals. -/
theorem subexponentiallyBounded_iff_isLittleO {f : ℕ → ℕ} :
    SubexponentiallyBounded f ↔
      (fun n => (Nat.clog 2 (f n + 1) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
  rw [Asymptotics.isLittleO_iff_nat_mul_le]
  constructor
  · intro hf c
    filter_upwards [hf c] with n hn
    simpa only [Real.norm_natCast] using
      (show (c : ℝ) * Nat.clog 2 (f n + 1) ≤ (n : ℝ) by exact_mod_cast hn)
  · intro hf c
    filter_upwards [hf c] with n hn
    simp only [Real.norm_natCast] at hn
    exact_mod_cast hn

namespace SubexponentiallyBounded

variable {f g h : ℕ → ℕ}

/-- Eventual domination preserves a subexponential bound. -/
theorem mono (hg : SubexponentiallyBounded g) (hfg : f ≤ᶠ[atTop] g) :
    SubexponentiallyBounded f := by
  intro c
  filter_upwards [hg c, hfg] with n hn hfg
  exact (Nat.mul_le_mul_left c
    (Nat.clog_mono_right 2 (Nat.add_le_add_right hfg 1))).trans hn

/-- Pointwise domination preserves a subexponential bound. -/
theorem mono_of_le (hg : SubexponentiallyBounded g) (hfg : f ≤ g) :
    SubexponentiallyBounded f :=
  hg.mono (Eventually.of_forall hfg)

/-- Constants are subexponentially bounded. -/
protected theorem const (a : ℕ) : SubexponentiallyBounded (fun _ => a) :=
  fun c => eventually_ge_atTop (c * Nat.clog 2 (a + 1))

/-- The identity function is subexponentially bounded. -/
protected theorem id : SubexponentiallyBounded (fun n => n) := by
  intro c
  filter_upwards [Nat.eventually_mul_log_le (2 * c) one_lt_two,
    eventually_ge_atTop (2 * c)] with n hlog hn
  have hclog : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr (Nat.lt_pow_succ_log_self one_lt_two n)
  have hmul := Nat.mul_le_mul_left c hclog
  nlinarith

private theorem of_le_mul_add_one (hf : SubexponentiallyBounded f)
    (hg : SubexponentiallyBounded g)
    (hh : ∀ n, h n + 1 ≤ (f n + 1) * (g n + 1)) : SubexponentiallyBounded h := by
  intro c
  filter_upwards [hf (2 * c), hg (2 * c)] with n hfn hgn
  have hlog : Nat.clog 2 (h n + 1) ≤
      Nat.clog 2 (f n + 1) + Nat.clog 2 (g n + 1) := by
    apply (Nat.clog_le_iff_le_pow one_lt_two).mpr
    rw [pow_add]
    exact (hh n).trans
      (Nat.mul_le_mul (Nat.le_pow_clog one_lt_two _) (Nat.le_pow_clog one_lt_two _))
  have hmul := Nat.mul_le_mul_left c hlog
  nlinarith

/-- Sums of subexponentially bounded functions are subexponentially bounded. -/
protected theorem add (hf : SubexponentiallyBounded f) (hg : SubexponentiallyBounded g) :
    SubexponentiallyBounded (fun n => f n + g n) :=
  of_le_mul_add_one hf hg fun n => by nlinarith

/-- Products of subexponentially bounded functions are subexponentially bounded. -/
protected theorem mul (hf : SubexponentiallyBounded f) (hg : SubexponentiallyBounded g) :
    SubexponentiallyBounded (fun n => f n * g n) :=
  of_le_mul_add_one hf hg fun n => by nlinarith

/-- Fixed powers of a subexponentially bounded function are subexponentially bounded. -/
protected theorem pow (hf : SubexponentiallyBounded f) (a : ℕ) :
    SubexponentiallyBounded (fun n => f n ^ a) := by
  induction a with
  | zero => simpa only [pow_zero] using SubexponentiallyBounded.const 1
  | succ a ih => simpa only [pow_succ] using ih.mul hf

/-- A subexponentially bounded function is eventually at most `2 ^ (n / d)` for every positive
integer `d`. Natural division only rounds the exponent down. -/
theorem eventually_le_two_pow_div (hf : SubexponentiallyBounded f) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, f n ≤ 2 ^ (n / d) := by
  filter_upwards [hf d] with n hn
  have hlog : Nat.clog 2 (f n + 1) ≤ n / d :=
    (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm] using hn)
  exact (Nat.le_succ _).trans ((Nat.clog_le_iff_le_pow one_lt_two).mp hlog)

end SubexponentiallyBounded

/-- Every polynomially bounded function is subexponentially bounded. -/
theorem PolynomiallyBounded.subexponentiallyBounded {f : ℕ → ℕ}
    (hf : PolynomiallyBounded f) : SubexponentiallyBounded f := by
  obtain ⟨d, hd⟩ := hf
  exact (SubexponentiallyBounded.id.pow d).mono hd

end Cslib
