/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.OddCircuitFourier
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import CslibFrontier.Foundations.Data.Code.BallVolume
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fourier estimates for the punctured Hamming ball

Let `B = {x ∈ 𝔽₂ⁿ | 0 < |x| ≤ w}` have `V` elements and let `μ̂(y) = charSum B y / V` be the
normalized Fourier transform of its indicator. Lemma 3.1 of [Saglam2027] bounds the third moment
`𝔼_y |μ̂(y)| ^ 3 = O(1 / (V n ^ 3))` and the tail
`Pr_y[|μ̂(y)| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))` for
`log n ≪ w ≤ (1 / 2 - ε) n`. `Cslib.Code.PuncturedBallFourierBounds n w C` states the two bounds
for one `n` and `w` with moment constant `C`; it is the input of the asymptotic code
construction in `CslibFrontier.Foundations.Data.Code.OddCircuitAsymptotic`.

Saglam derives Lemma 3.1 from two results of Kirshner and Samorodnitsky [KirshnerSamorodnitsky2021,
Corollary 1.4 and Theorem 1.5] about polynomials `f` of degree at most `w` on the cube, in the
specializations quoted in [Saglam2027, Appendix A]. Those results are **not proved here**; they are
stated as the hypotheses `Cslib.Code.KSThirdMomentBound` and `Cslib.Code.KSTailBound`, in nats:

* third moment: `𝔼|f| ^ 3 ≤ (𝔼 f ^ 2) ^ (3 / 2) exp (n (h(ρ) / 2 - γ(ρ)))` with `ρ = w / n` and
  `γ = Cslib.Code.ksGamma`;
* tail: `Pr[|f| > √(𝔼 f ^ 2) exp (n (T(ρ, k / n) - h(ρ) / 2))] ≤ exp (n (h(k / n) - log 2))` for
  integers `k` with `k / n ≤ 1 / 2 - √(ρ (1 - ρ))`, where `T = Cslib.Code.ksTailExponent`.

Here `h = Real.binEntropy` is the binary entropy in nats. Saglam writes both in bits with base-`2`
logarithms (`2 ^ (n (H₂(ρ)/2 - γ₂(ρ)))`, `2 ^ (n (H₂(y) - 1))`); multiplying the exponents by
`log 2` gives the forms above. A polynomial of degree at most `w` is written by its Fourier
coefficients `a x`, which vanish for `|x| > w`. The hypotheses are only required for `0 < w` and
`2 w < n`, the range in which they are used.

These forms agree with arXiv:1909.11929v1, which states both bounds for every `n` with no error
term. An independent review of #4735 checked the specializations there. Saglam's `γ` is
`H₂(ρ) / 2 - ψ(3, ρ)`, by Kirshner–Samorodnitsky Proposition 2.6 at `p = 3` with `t = 1 - 2 δ`,
which gives Saglam's `1 - 2 u = √(ρ / (2 - 3 ρ))`. Saglam's integral is their tail exponent `τ`
on `y ≤ 1 / 2 - √(ρ (1 - ρ))` (their §2.1.1–2.1.2).

Everything else in Saglam's Appendix A is proved: `μ̂` has degree at most `w` and
`𝔼 μ̂ ^ 2 = 1 / V` (`Cslib.Code.sum_charSum_sq`); `γ(ρ) ≥ c ρ` for `0 < ρ ≤ 1 / 2 - ε`
(`Cslib.Code.exists_mul_le_ksGamma`); `T(ρ, y) ≤ h(ρ) - 2 ρ y` (`Cslib.Code.ksTailExponent_le`);
`exp (n h(w / n)) ≤ (n + 1) V` (`Cslib.exp_mul_binEntropy_le_succ_mul_choose`); and
`h(y) ≤ y log (e / y)`. Together they give
`Cslib.Code.exists_puncturedBallFourierBounds_of_ks`: Lemma 3.1 with explicit constants, the
moment constant being `C = 2`.

Saglam proves `γ(ρ) = (ρ / 2) log₂ (1 / ρ) + O(ρ)`. The weaker `γ(ρ) ≥ c_ε ρ` suffices because
`w ≥ K log₂ n` is assumed with `K` at our disposal. Here it follows from
`(1 - ρ) ^ 4 < ρ (2 - 3 ρ) ^ 3` on `(3 / 20, 1 / 2)`, which makes `γ` strictly decreasing there to
`γ(1 / 2) = 0`, and from elementary logarithm bounds on `(0, 3 / 20]`.

## Main definitions

* `Cslib.Code.PuncturedBallFourierBounds`: the moment and tail bounds of Lemma 3.1 of
  [Saglam2027] for one `n` and `w`.
* `Cslib.Code.ksGamma`, `Cslib.Code.ksTailExponent`: the exponents of the Kirshner–Samorodnitsky
  bounds, in nats.
* `Cslib.Code.KSThirdMomentBound`, `Cslib.Code.KSTailBound`: the imported Kirshner–Samorodnitsky
  bounds, as hypotheses.

## Main results

* `Cslib.Code.sum_charSum_sq`: Parseval, `∑_y charSum B y ^ 2 = 2 ^ n |B|`.
* `Cslib.Code.exists_mul_le_ksGamma`: `γ(ρ) ≥ c ρ` on `(0, 1 / 2 - ε]`.
* `Cslib.Code.ksTailExponent_le`: `T(ρ, y) ≤ h(ρ) - 2 ρ y`.
* `Cslib.Code.exists_puncturedBallFourierBounds_of_ks`: Lemma 3.1 of [Saglam2027] from the
  Kirshner–Samorodnitsky bounds.

## References

* [M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*][Saglam2027], STOC 2027
  submission 1516, Lemma 3.1 and Appendix A.
* [N. Kirshner and A. Samorodnitsky, *A moment ratio bound for polynomials and some extremal
  properties of Krawtchouk polynomials and Hamming spheres*][KirshnerSamorodnitsky2021],
  Corollary 1.4 and Theorem 1.5, as quoted in [Saglam2027, Appendix A].
-/

public section

namespace Cslib.Code

open Finset Matrix Real Set

section Parseval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parseval for `charSum`**: `∑_y charSum B y ^ 2 = 2 ^ n |B|`, so `𝔼_y μ̂(y) ^ 2 = 1 / |B|` for
`μ̂ = charSum B / |B|`. -/
theorem sum_charSum_sq (B : Finset (ι → ZMod 2)) :
    ∑ y, charSum B y ^ 2 = 2 ^ Fintype.card ι * #B := by
  have hsq : ∀ y, charSum B y ^ 2 = ∑ x ∈ B, ∑ x' ∈ B, (-1 : ℝ) ^ (y ⬝ᵥ (x + x')).val := by
    intro y
    rw [sq, charSum, sum_mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
    rw [dotProduct_add, ZMod.neg_one_pow_val_add]
  simp_rw [hsq]
  rw [sum_comm]
  refine (sum_congr rfl fun x _ => ?_).trans (by rw [sum_const, nsmul_eq_mul, mul_comm])
  rw [sum_comm]
  simp_rw [sum_neg_one_pow_val_dotProduct]
  have : ∀ x' : ι → ZMod 2, (x + x' = 0 ↔ x = x') := fun x' => by
    rw [← sub_eq_zero (a := x), sub_eq_add_neg,
      show -x' = x' from funext fun i => ZMod.neg_eq_self_mod_two _]
  simp_rw [this]
  rw [sum_ite_eq]
  simp_all

/-- `μ̂ = charSum B / |B|` is the Fourier expansion with coefficients `1 / |B|` on `B`. -/
theorem charSum_div_card_eq (B : Finset (ι → ZMod 2)) (y : ι → ZMod 2) :
    charSum B y / #B = ∑ x, (if x ∈ B then (#B : ℝ)⁻¹ else 0) * (-1 : ℝ) ^ (y ⬝ᵥ x).val := by
  simp only [ite_mul, zero_mul]
  rw [sum_ite_mem, Finset.univ_inter, charSum, sum_div]
  exact sum_congr rfl fun x _ => by ring

end Parseval

/-- **Lemma 3.1 of [Saglam2027]** for one `n` and `w`, with moment constant `C`. Let
`B = {x ∈ 𝔽₂ⁿ | x ≠ 0, |x| < w + 1}` and `μ̂ = charSum B / |B|`. Then
`𝔼_y |μ̂(y)| ^ 3 ≤ C / (|B| n ^ 3)` and
`Pr_y[|μ̂(y)| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))`, with expectations and
probabilities over uniform `y ∈ 𝔽₂ⁿ`. Saglam states the moment bound as `O(1 / (V n ^ 3))`. -/
@[expose] def PuncturedBallFourierBounds (n w : ℕ) (C : ℝ) : Prop :=
  let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
  (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n ≤ C / (#B * n ^ 3) ∧
    (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n ≤
      (2 : ℝ) ^ (-(n : ℝ) + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n))

section Exponents

/-- The exponent `γ` of the Kirshner–Samorodnitsky third-moment bound as specialized in
[Saglam2027, Appendix A], in nats:
`γ(ρ) = -(ρ / 2) log ρ - 2 (1 - ρ) log (1 - ρ) - log 2 + (1 - 3 ρ / 2) log (2 - 3 ρ)`. Saglam's
`γ` uses base-`2` logarithms and equals this value divided by `log 2`. -/
noncomputable def ksGamma (ρ : ℝ) : ℝ :=
  -(ρ / 2 * log ρ) - 2 * (1 - ρ) * log (1 - ρ) - log 2 + (1 - 3 * ρ / 2) * log (2 - 3 * ρ)

/-- The exponent vanishes at the end of the range: `γ(1 / 2) = 0`. -/
theorem ksGamma_half : ksGamma (1 / 2) = 0 := by
  have h : (2 : ℝ) - 3 * (1 / 2) = 1 / 2 := by norm_num
  rw [ksGamma, h, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, log_inv]
  ring

/-- The derivative `γ'(ρ) = (4 log (1 - ρ) - log ρ - 3 log (2 - 3 ρ)) / 2`. -/
private theorem hasDerivAt_ksGamma {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1 / 2) :
    HasDerivAt ksGamma ((4 * log (1 - ρ) - log ρ - 3 * log (2 - 3 * ρ)) / 2) ρ := by
  have ha : (1 - ρ) ≠ 0 := by linarith
  have hb : (2 - 3 * ρ) ≠ 0 := by linarith
  have e1 := ((hasDerivAt_id ρ).div_const 2).mul (hasDerivAt_log h0.ne')
  have e2 := (((hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)).const_mul 2).mul
    (((hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)).log ha)
  have e3 := ((hasDerivAt_const ρ (1 : ℝ)).sub ((hasDerivAt_id ρ).const_mul 3 |>.div_const 2)).mul
    (((hasDerivAt_const ρ (2 : ℝ)).sub ((hasDerivAt_id ρ).const_mul 3)).log hb)
  have := ((e1.neg.sub e2).sub (hasDerivAt_const ρ (log 2))).add e3
  convert this using 1
  · ext x; simp [ksGamma]
  · simp only [id, Pi.sub_apply]
    have k1 : (1 - 3 * ρ / 2) * ((0 - 3 * 1) / (2 - 3 * ρ)) = -3 / 2 := by field_simp; ring
    have k2 : 2 * (1 - ρ) * ((0 - 1) / (1 - ρ)) = -2 := by field_simp; ring
    have k3 : ρ / 2 * ρ⁻¹ = 1 / 2 := by field_simp
    linear_combination k3 + k2 - k1

/-- `(1 - ρ) ^ 4 < ρ (2 - 3 ρ) ^ 3` on `(3 / 20, 1 / 2)`: the difference is
`(2 ρ - 1) (14 ρ ^ 3 - 22 ρ ^ 2 + 10 ρ - 1)` and the cubic is positive there. -/
private theorem pow_four_lt {ρ : ℝ} (h0 : 3 / 20 < ρ) (h1 : ρ < 1 / 2) :
    (1 - ρ) ^ 4 < ρ * (2 - 3 * ρ) ^ 3 := by
  have hg : 0 < 14 * ρ ^ 3 - 22 * ρ ^ 2 + 10 * ρ - 1 := by
    nlinarith [mul_pos (sub_pos.2 h0) (sub_pos.2 h1), sq_nonneg (ρ - 1 / 3),
      mul_pos (mul_pos (sub_pos.2 h0) (sub_pos.2 h1)) (sub_pos.2 h1)]
  nlinarith [mul_pos (sub_pos.2 h1) hg]

/-- `γ` is strictly decreasing on `[3 / 20, 1 / 2]`, because
`γ'(ρ) = log ((1 - ρ) ^ 4 / (ρ (2 - 3 ρ) ^ 3)) / 2` is negative there. -/
theorem strictAntiOn_ksGamma : StrictAntiOn ksGamma (Icc (3 / 20) (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · intro x hx
    have h0 : 0 < x := by linarith [hx.1]
    have hlt : x < 2 / 3 := by linarith [hx.2]
    unfold ksGamma
    refine ContinuousAt.continuousWithinAt ?_
    have : (1 - x) ≠ 0 := by linarith
    have : (2 - 3 * x) ≠ 0 := by linarith
    have : x ≠ 0 := h0.ne'
    have : (2 : ℝ) ≠ 0 := two_ne_zero
    fun_prop (disch := assumption)
  · intro x hx
    rw [interior_Icc] at hx
    have h0 : 0 < x := by linarith [hx.1]
    rw [(hasDerivAt_ksGamma h0 hx.2).deriv]
    have hl := pow_four_lt hx.1 hx.2
    have hp1 : 0 < 1 - x := by linarith [hx.2]
    have hp2 : 0 < 2 - 3 * x := by linarith [hx.2]
    have := log_lt_log (by positivity) hl
    rw [log_pow, log_mul h0.ne' (by positivity), log_pow] at this
    push_cast at this
    linarith

/-- For `0 < ρ ≤ 3 / 20`, `ρ / 20 ≤ γ(ρ)`. -/
private theorem div_le_ksGamma_of_le {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 3 / 20) :
    ρ / 20 ≤ ksGamma ρ := by
  have hρ1 : 0 < 1 - ρ := by linarith
  have ha : 0 < 1 - 3 * ρ / 2 := by linarith
  -- `log (1 - ρ) ≤ -ρ`
  have l1 : log (1 - ρ) ≤ -ρ := by linarith [log_le_sub_one_of_pos hρ1]
  -- `(1 - a) log (1 - a) ≥ -a`
  have l2 : -(3 * ρ / 2) ≤ (1 - 3 * ρ / 2) * log (1 - 3 * ρ / 2) := by
    have := one_sub_inv_le_log_of_pos ha
    have e : (1 - 3 * ρ / 2) * (1 - (1 - 3 * ρ / 2)⁻¹) = -(3 * ρ / 2) := by
      rw [mul_sub, mul_inv_cancel₀ ha.ne']; ring
    nlinarith [mul_le_mul_of_nonneg_left this ha.le]
  have hsplit : log (2 - 3 * ρ) = log 2 + log (1 - 3 * ρ / 2) := by
    rw [← log_mul two_ne_zero ha.ne']; ring_nf
  -- `-log ρ ≥ log (20 / 3) ≥ 3 log 2 - 1 / 5`
  have l3 : 3 * log 2 - 1 / 5 ≤ -log ρ := by
    have hl : log (20 / 3) ≤ -log ρ := by
      rw [← log_inv]
      exact log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) h0]; linarith)
    have h56 : log (5 / 6) ≥ 1 - (5 / 6 : ℝ)⁻¹ := one_sub_inv_le_log_of_pos (by norm_num)
    have : log (20 / 3) = 3 * log 2 + log (5 / 6) := by
      rw [show (20 / 3 : ℝ) = 2 ^ 3 * (5 / 6) by norm_num, log_mul (by norm_num) (by norm_num),
        log_pow]; norm_num
    norm_num at h56
    linarith
  have hl2 := log_two_gt_d9
  have hl2' := log_two_lt_d9
  rw [ksGamma, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left l1 (by linarith : (0 : ℝ) ≤ 2 * (1 - ρ)),
    mul_le_mul_of_nonneg_left l3 h0.le]

/-- **Positivity of the exponent** [Saglam2027, Appendix A]: for every `ε > 0` there is `c > 0` with
`c ρ ≤ γ(ρ)` for `0 < ρ ≤ 1 / 2 - ε`. -/
theorem exists_mul_le_ksGamma {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ ρ, 0 < ρ → ρ ≤ 1 / 2 - ε → c * ρ ≤ ksGamma ρ := by
  set ρ₀ := max (1 / 2 - ε) (3 / 20) with hρ₀
  have hρ₀m : ρ₀ ∈ Icc (3 / 20 : ℝ) (1 / 2) :=
    ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩
  have hρ₀lt : ρ₀ < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hpos : 0 < ksGamma ρ₀ := by
    have := strictAntiOn_ksGamma hρ₀m ⟨by norm_num, le_rfl⟩ hρ₀lt
    rwa [ksGamma_half] at this
  refine ⟨min (1 / 20) (2 * ksGamma ρ₀), lt_min (by norm_num) (by positivity), fun ρ h0 h1 => ?_⟩
  rcases le_total ρ (3 / 20) with hs | hl
  · calc min (1 / 20) (2 * ksGamma ρ₀) * ρ ≤ 1 / 20 * ρ := by gcongr; exact min_le_left _ _
      _ = ρ / 20 := by ring
      _ ≤ ksGamma ρ := div_le_ksGamma_of_le h0 hs
  · have hle : ksGamma ρ₀ ≤ ksGamma ρ :=
      strictAntiOn_ksGamma.antitoneOn ⟨hl, by linarith⟩ hρ₀m (h1.trans (le_max_left _ _))
    calc min (1 / 20) (2 * ksGamma ρ₀) * ρ ≤ 2 * ksGamma ρ₀ * ρ := by
          gcongr; exact min_le_right _ _
      _ ≤ 2 * ksGamma ρ₀ * (1 / 2) := by gcongr; linarith
      _ ≤ ksGamma ρ := by linarith

/-- The integrand `log ((1 - 2 ρ + √((1 - 2 ρ) ^ 2 - 4 z (1 - z))) / (2 (1 - z)))` of the
Kirshner–Samorodnitsky tail exponent [Saglam2027, Appendix A], in nats. -/
noncomputable def ksTailIntegrand (ρ z : ℝ) : ℝ :=
  log ((1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)))

/-- The Kirshner–Samorodnitsky tail exponent `T(ρ, y) = h(ρ) + ∫_0^y ksTailIntegrand ρ z dz`
[Saglam2027, Appendix A], in nats; Saglam's `T` is this value divided by `log 2`. -/
noncomputable def ksTailExponent (ρ y : ℝ) : ℝ :=
  binEntropy ρ + ∫ z in (0 : ℝ)..y, ksTailIntegrand ρ z

/-- The argument of the logarithm in the tail integrand lies in `(0, 1 - 2 ρ]` for
`0 ≤ z ≤ 1 / 2`. -/
private theorem ksTailIntegrand_arg {ρ z : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    0 < (1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)) ∧
      (1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)) ≤ 1 - 2 * ρ := by
  have hd : 0 < 2 * (1 - z) := by linarith
  constructor
  · exact div_pos (by linarith [sqrt_nonneg ((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))]) hd
  · rw [div_le_iff₀ hd]
    have hs : √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z)) ≤ (1 - 2 * ρ) * (1 - 2 * z) := by
      rw [sqrt_le_left (by nlinarith)]
      have h1 : (1 - 2 * ρ) ^ 2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ z * (1 - z) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    nlinarith

/-- **The tail exponent bound** [Saglam2027, Appendix A]: the integrand is at most
`log (1 - 2 ρ) ≤ -2 ρ`, so `T(ρ, y) ≤ h(ρ) - 2 ρ y` for `0 ≤ y ≤ 1 / 2`. -/
theorem ksTailExponent_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    ksTailExponent ρ y ≤ binEntropy ρ - 2 * ρ * y := by
  have hcont : ContinuousOn (ksTailIntegrand ρ) (Icc 0 y) := by
    refine ContinuousOn.log ?_ fun z hz => (ksTailIntegrand_arg hρ0 hρ hz.1 (hz.2.trans hy)).1.ne'
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    have := hz.2; linarith
  have hint : IntervalIntegrable (ksTailIntegrand ρ) MeasureTheory.volume 0 y :=
    (hcont.mono (by rw [uIcc_of_le hy0])).intervalIntegrable
  have hle : ∫ z in (0 : ℝ)..y, ksTailIntegrand ρ z ≤ ∫ _ in (0 : ℝ)..y, (-2 * ρ) := by
    refine intervalIntegral.integral_mono_on hy0 hint intervalIntegrable_const fun z hz => ?_
    obtain ⟨hpos, hle⟩ := ksTailIntegrand_arg hρ0 hρ hz.1 (hz.2.trans hy)
    calc ksTailIntegrand ρ z ≤ log (1 - 2 * ρ) := log_le_log hpos hle
      _ ≤ 1 - 2 * ρ - 1 := log_le_sub_one_of_pos (by linarith)
      _ = -2 * ρ := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  rw [ksTailExponent]
  linarith

/-- `ε ^ 2 ≤ 1 / 2 - √(ρ (1 - ρ))` for `0 ≤ ρ ≤ 1 / 2 - ε`. -/
theorem sq_le_half_sub_sqrt {ε ρ : ℝ} (hε : 0 ≤ ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2 - ε) :
    ε ^ 2 ≤ 1 / 2 - √(ρ * (1 - ρ)) := by
  have hε2 : ε ≤ 1 / 2 := by linarith
  have : √(ρ * (1 - ρ)) ≤ 1 / 2 - ε ^ 2 := by
    rw [sqrt_le_left (by nlinarith)]
    nlinarith [mul_le_mul hρ hρ hρ0 (by linarith)]
  linarith

end Exponents

section KirshnerSamorodnitsky

/-- **The Kirshner–Samorodnitsky third-moment bound** [KirshnerSamorodnitsky2021, Corollary 1.4],
in the specialization quoted in [Saglam2027, Appendix A], **imported as a hypothesis**: for
`0 < w`, `2 w < n` and `ρ = w / n`, every `f(y) = ∑_x a x (-1) ^ (y ⬝ᵥ x)` with `a x = 0` for
`|x| > w` (a polynomial of degree at most `w` in the signs `(-1) ^ y_i`) satisfies
`𝔼|f| ^ 3 ≤ (𝔼 f ^ 2) ^ (3 / 2) exp (n (h(ρ) / 2 - γ(ρ)))`. -/
def KSThirdMomentBound (n w : ℕ) : Prop :=
  0 < w → 2 * w < n → ∀ a : (Fin n → ZMod 2) → ℝ, (∀ x, w < hammingNorm x → a x = 0) →
    let f : (Fin n → ZMod 2) → ℝ := fun y => ∑ x, a x * (-1 : ℝ) ^ (y ⬝ᵥ x).val
    (∑ y, |f y| ^ 3) / 2 ^ n ≤
      ((∑ y, f y ^ 2) / 2 ^ n) ^ (3 / 2 : ℝ) * exp (n * (binEntropy (w / n) / 2 - ksGamma (w / n)))

/-- **The Kirshner–Samorodnitsky tail bound** [KirshnerSamorodnitsky2021, Theorem 1.5], in the
specialization quoted in [Saglam2027, Appendix A], **imported as a hypothesis**: for `0 < w`,
`2 w < n`, `ρ = w / n` and every `f` of degree at most `w` as in `KSThirdMomentBound`, every
integer `k` with `k / n ≤ 1 / 2 - √(ρ (1 - ρ))` satisfies
`Pr[|f| > √(𝔼 f ^ 2) exp (n (T(ρ, k / n) - h(ρ) / 2))] ≤ exp (n (h(k / n) - log 2))`.
Saglam and Kirshner–Samorodnitsky state the event with `≥`. The strict event used here is
smaller, so this hypothesis is weaker. The weakening, like the restriction `0 < w`, is needed:
as printed, Theorem 1.5 fails at degree `0`. For `f ≡ 1` and `k = 0` the threshold is
`‖f‖₂ = 1`, so the `≥` event has probability `1 > 2 ^ (-n)`. -/
def KSTailBound (n w : ℕ) : Prop :=
  0 < w → 2 * w < n → ∀ a : (Fin n → ZMod 2) → ℝ, (∀ x, w < hammingNorm x → a x = 0) →
    ∀ k : ℕ, (k : ℝ) / n ≤ 1 / 2 - √(w / n * (1 - w / n)) →
    let f : (Fin n → ZMod 2) → ℝ := fun y => ∑ x, a x * (-1 : ℝ) ^ (y ⬝ᵥ x).val
    (#{y | √((∑ y, f y ^ 2) / 2 ^ n) *
        exp (n * (ksTailExponent (w / n) (k / n) - binEntropy (w / n) / 2)) < |f y|} : ℝ) /
      2 ^ n ≤ exp (n * (binEntropy (k / n) - log 2))

variable {n w : ℕ}

/-- Facts about the punctured ball used by both estimates: the Fourier coefficients of `μ̂` vanish
above weight `w`, `𝔼 μ̂ ^ 2 = 1 / V`, and `√(exp (n h(w / n)) / V) ≤ √(n + 1)`. -/
private theorem puncturedBall_facts (hw0 : 0 < w) (hwn : w ≤ n) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (0 : ℝ) < #B ∧
    (∀ x, w < hammingNorm x → (if x ∈ B then (#B : ℝ)⁻¹ else 0) = 0) ∧
    (∑ y, (charSum B y / #B) ^ 2) / 2 ^ n = (#B : ℝ)⁻¹ ∧
    √((#B : ℝ)⁻¹) * √(exp (n * binEntropy (w / n))) ≤ √(n + 1) := by
  intro B
  have hcard : (#B : ℝ) = ∑ i ∈ Ico 1 (w + 1), (n.choose i : ℝ) := by
    simp only [B]; rw [card_filter_ne_zero_hammingNorm_lt]; push_cast; rfl
  have hchoose : (n.choose w : ℝ) ≤ #B := by
    rw [hcard]
    exact single_le_sum (f := fun i => (n.choose i : ℝ)) (fun i _ => by positivity)
      (mem_Ico.2 ⟨hw0, by omega⟩)
  have hpos : (0 : ℝ) < #B :=
    lt_of_lt_of_le (by exact_mod_cast Nat.choose_pos hwn) hchoose
  refine ⟨hpos, fun x hx => ?_, ?_, ?_⟩
  · rw [ite_eq_right_iff]
    intro hB
    simp only [B, mem_filter] at hB
    omega
  · have h := sum_charSum_sq B
    simp only [Fintype.card_fin] at h
    simp_rw [div_pow, ← sum_div, h]
    field_simp
  · rw [← sqrt_mul (inv_nonneg.2 hpos.le)]
    refine sqrt_le_sqrt ?_
    rw [inv_mul_le_iff₀ hpos]
    calc exp (n * binEntropy (w / n)) ≤ (n + 1) * n.choose w :=
          exp_mul_binEntropy_le_succ_mul_choose hwn
      _ ≤ #B * (n + 1) := by rw [mul_comm]; gcongr

/-- `exp (-(t log n)) = n ^ (-t)` as an inverse power for natural `t`. -/
private theorem exp_neg_mul_log (t : ℕ) {x : ℝ} (hx : 0 < x) :
    exp (-(t * log x)) = (x ^ t)⁻¹ := by
  rw [exp_neg, ← log_pow, exp_log (by positivity)]

/-- `log n ≤ log₂ n` for `n ≥ 1`. -/
private theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) : log x ≤ logb 2 x := by
  rw [logb, le_div_iff₀ (log_pos one_lt_two)]
  have := log_two_lt_d9
  have h0 := log_nonneg hx
  norm_num at this
  nlinarith

/-- **The moment estimate of Lemma 3.1** [Saglam2027, Appendix A] from the Kirshner–Samorodnitsky
third-moment bound: if `γ(ρ) ≥ c ρ` at `ρ = w / n` and `w ≥ K log₂ n` with `c K ≥ 4`, then
`𝔼|μ̂| ^ 3 ≤ 2 / (V n ^ 3)`. -/
theorem moment_le_of_ksThirdMomentBound (hKS : KSThirdMomentBound n w) (hw0 : 0 < w)
    (hwn : 2 * w < n) {c K : ℝ} (hc0 : 0 < c) (hc : c * (w / n) ≤ ksGamma (w / n))
    (hcK : 4 ≤ c * K)
    (hK : K * logb 2 n ≤ w) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n ≤ 2 / (#B * n ^ 3) := by
  intro B
  obtain ⟨hV, hsupp, hpar, hsq⟩ := puncturedBall_facts (n := n) hw0 (by omega)
  have h := hKS hw0 hwn _ hsupp
  dsimp only at h
  simp_rw [← charSum_div_card_eq] at h
  rw [hpar] at h
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  -- `(1 / V) ^ (3 / 2) = (1 / V) √(1 / V)`
  have hr : ((#B : ℝ)⁻¹) ^ (3 / 2 : ℝ) = (#B : ℝ)⁻¹ * √((#B : ℝ)⁻¹) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (inv_pos.2 hV), rpow_one,
      sqrt_eq_rpow]
  -- `n γ(ρ) ≥ 4 log n`
  have hγ : 4 * log n ≤ n * ksGamma (w / n) := by
    have h1 : c * w ≤ n * ksGamma (w / n) := by
      have := mul_le_mul_of_nonneg_left hc hnpos.le
      rwa [show (n : ℝ) * (c * (w / n)) = c * w by field_simp] at this
    have hlog := log_le_logb_two hn
    have hlog0 := log_nonneg hn
    nlinarith [mul_le_mul_of_nonneg_left hK hc0.le]
  have hexp : exp (-(n * ksGamma (w / n))) ≤ ((n : ℝ) ^ 4)⁻¹ := by
    rw [← exp_neg_mul_log 4 hnpos]
    push_cast
    exact exp_le_exp.2 (by linarith)
  have hsplit : exp (n * (binEntropy (w / n) / 2 - ksGamma (w / n))) =
      √(exp (n * binEntropy (w / n))) * exp (-(n * ksGamma (w / n))) := by
    rw [← exp_half, ← exp_add]; ring_nf
  rw [hr, hsplit] at h
  have hsqn : √((n : ℝ) + 1) ≤ 2 * n := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  calc (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n
      ≤ (#B : ℝ)⁻¹ * (√((#B : ℝ)⁻¹) * √(exp (n * binEntropy (w / n)))) *
          exp (-(n * ksGamma (w / n))) := by linarith
    _ ≤ (#B : ℝ)⁻¹ * (2 * n) * ((n : ℝ) ^ 4)⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hsq.trans hsqn) (by positivity)) hexp
          (by positivity) (by positivity)
    _ = 2 / (#B * n ^ 3) := by field_simp

/-- The tail bound of Lemma 3.1 in nats: with `u = log₂ n / w`,
`2 ^ (-n + 2 n u log₂ (e w / log₂ n)) = exp (n (2 u log (e / u) - log 2))`. -/
theorem two_rpow_tail_eq (n w : ℝ) :
    (2 : ℝ) ^ (-n + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) =
      exp (n * (2 * (logb 2 n / w) * log (exp 1 / (logb 2 n / w)) - log 2)) := by
  have hl : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  rw [← div_div_eq_mul_div, rpow_def_of_pos two_pos]
  congr 1
  generalize logb 2 n / w = u
  rw [logb]
  field_simp
  ring

/-- The threshold of the tail bound is at most `1 / n`: with `T(ρ, y) ≤ h(ρ) - 2 ρ y`,
`√(1 / V) exp (n (T(ρ, y) - h(ρ) / 2)) ≤ √(1 / V) √(exp (n h(ρ))) exp (-2 w y)`, and
`w y ≥ log n`. -/
private theorem threshold_le {n w y V : ℝ} (hn : 2 ≤ n) (hρ0 : 0 ≤ w / n)
    (hρ : w / n < 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (hwy : log n ≤ w * y)
    (hsq : √V⁻¹ * √(exp (n * binEntropy (w / n))) ≤ √(n + 1)) :
    √V⁻¹ * exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2)) ≤ 1 / n := by
  have hnpos : 0 < n := by linarith
  have hT := ksTailExponent_le hρ0 hρ hy0 hy
  have hexp : exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2)) ≤
      √(exp (n * binEntropy (w / n))) * exp (-(2 * log n)) := by
    rw [← exp_half, ← exp_add]
    refine exp_le_exp.2 ?_
    have hwy' : n * (2 * (w / n) * y) = 2 * (w * y) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hT hnpos.le]
  have hn2 : exp (-(2 * log n)) = (n ^ 2)⁻¹ := by
    rw [exp_neg, show (2 : ℝ) * log n = ((2 : ℕ) : ℝ) * log n by norm_num, ← log_pow,
      exp_log (by positivity)]
  have hsqn : √(n + 1) ≤ n := by
    rw [sqrt_le_left (by positivity)]; nlinarith
  calc √V⁻¹ * exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2))
      ≤ √V⁻¹ * (√(exp (n * binEntropy (w / n))) * (n ^ 2)⁻¹) := by
        rw [← hn2]; exact mul_le_mul_of_nonneg_left hexp (sqrt_nonneg _)
    _ = √V⁻¹ * √(exp (n * binEntropy (w / n))) * (n ^ 2)⁻¹ := by ring
    _ ≤ n * (n ^ 2)⁻¹ := by gcongr; exact hsq.trans hsqn
    _ = 1 / n := by field_simp

/-- The tail probability of Lemma 3.1: with `u = log₂ n / w ≤ 1` and `u ≤ y ≤ 2 u < 1`,
`exp (n (h(y) - log 2)) ≤ 2 ^ (-n + 2 n u log₂ (e w / log₂ n))`, since
`h(y) ≤ y log (e / y) ≤ 2 u log (e / u)`. -/
private theorem exp_binEntropy_le_rpow {n w y : ℝ} (hw : 0 < w) (hlg : 0 < logb 2 n)
    (hu1 : logb 2 n / w ≤ 1) (hy1 : logb 2 n / w ≤ y) (hy2 : y ≤ 2 * (logb 2 n / w))
    (hy : y < 1) (hn : 0 ≤ n) :
    exp (n * (binEntropy y - log 2)) ≤
      (2 : ℝ) ^ (-n + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) := by
  set u := logb 2 n / w with hu
  have hu0 : 0 < u := by positivity
  have hy0 : 0 < y := hu0.trans_le hy1
  have hlog0 : 0 ≤ log (exp 1 / u) := by
    refine log_nonneg ?_
    rw [le_div_iff₀ hu0, one_mul]
    exact hu1.trans (by linarith [add_one_le_exp (1 : ℝ)])
  have hent : binEntropy y ≤ 2 * u * log (exp 1 / u) := by
    calc binEntropy y ≤ y * log (exp 1 / y) := binEntropy_le_mul_log_exp_one_div hy0 hy
      _ ≤ y * log (exp 1 / u) := by gcongr
      _ ≤ 2 * u * log (exp 1 / u) := by gcongr
  rw [two_rpow_tail_eq, ← hu]
  refine exp_le_exp.2 ?_
  gcongr

/-- **The tail estimate of Lemma 3.1** [Saglam2027, Appendix A] from the Kirshner–Samorodnitsky
tail bound, with `k = ⌈n log₂ n / w⌉` and `y = k / n`: if `ρ = w / n ≤ 1 / 2 - ε`,
`w ≥ K log₂ n` with `K ≥ 2 / ε ^ 2`, and `n ≥ 2 / ε ^ 2`, then
`Pr[|μ̂| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))`. -/
theorem tail_le_of_ksTailBound (hKS : KSTailBound n w) (hw0 : 0 < w) {ε K : ℝ} (hε : 0 < ε)
    (hρ : (w : ℝ) ≤ (1 / 2 - ε) * n) (hK : 2 / ε ^ 2 ≤ K) (hnε : 2 / ε ^ 2 ≤ n)
    (hKw : K * logb 2 n ≤ w) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n ≤
      (2 : ℝ) ^ (-(n : ℝ) + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) := by
  intro B
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw0
  have hε2pos : 0 < 2 / ε ^ 2 := by positivity
  have hnpos : (0 : ℝ) < n := hε2pos.trans_le hnε
  have hwn' : (2 * w : ℝ) < n := by nlinarith
  have hwn : 2 * w < n := by exact_mod_cast hwn'
  obtain ⟨hV, hsupp, hpar, hsq⟩ := puncturedBall_facts (n := n) hw0 (by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hlg : 1 ≤ logb 2 n := by rw [le_logb_iff_rpow_le one_lt_two hnpos, rpow_one]; exact hn2
  have hKpos : 0 < K := hε2pos.trans_le hK
  have hu0 : 0 < logb 2 n / w := by positivity
  have huK : logb 2 n / w ≤ ε ^ 2 / 2 := by
    have h1 : logb 2 n / w ≤ 1 / K := by
      rw [div_le_div_iff₀ (by linarith) hKpos]; linarith
    have h2 : 1 / K ≤ 1 / (2 / ε ^ 2) := one_div_le_one_div_of_le hε2pos hK
    rw [one_div_div] at h2
    linarith
  have hnu : 1 / (n : ℝ) ≤ logb 2 n / w := by
    rw [div_le_div_iff₀ hnpos (by linarith)]
    nlinarith
  have hn1 : 1 / (n : ℝ) ≤ ε ^ 2 / 2 := by
    rw [div_le_iff₀ hnpos]; rw [div_le_iff₀ (by positivity)] at hnε; linarith
  have hε1 : ε ^ 2 < 1 := by nlinarith
  -- the parameter `y = ⌈n u⌉ / n`
  have hky1 : logb 2 n / w ≤ (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n := by
    rw [le_div_iff₀ hnpos, mul_comm]; exact Nat.le_ceil _
  have hky2 : (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n ≤ 2 * (logb 2 n / w) := by
    rw [div_le_iff₀ hnpos]
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ n * (logb 2 n / w))
    rw [div_le_iff₀ hnpos] at hnu
    linarith
  have hy0 : 0 < (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n := hu0.trans_le hky1
  have hyε : (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n ≤ ε ^ 2 := by linarith
  have hρ0 : 0 ≤ (w : ℝ) / n := by positivity
  have hρε : (w : ℝ) / n ≤ 1 / 2 - ε := by rw [div_le_iff₀ hnpos]; exact hρ
  have h := hKS hw0 hwn _ hsupp _ (hyε.trans (sq_le_half_sub_sqrt hε.le hρ0 hρε))
  dsimp only at h
  simp_rw [← charSum_div_card_eq] at h
  rw [hpar] at h
  have hwy : log n ≤ w * ((⌈n * (logb 2 n / w)⌉₊ : ℝ) / n) := by
    have hl := log_le_logb_two (by linarith : (1 : ℝ) ≤ n)
    have : (w : ℝ) * (logb 2 n / w) = logb 2 n := by field_simp
    nlinarith
  have hthr := threshold_le hn2 hρ0 (by linarith) hy0.le (by nlinarith) hwy hsq
  refine le_trans ?_ (exp_binEntropy_le_rpow (by linarith) (by linarith) (by nlinarith) hky1 hky2
    (by linarith) hnpos.le)
  refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) h
  refine Nat.cast_le.2 (card_le_card fun y hy => ?_)
  rw [mem_filter] at hy ⊢
  exact ⟨hy.1, hthr.trans_lt hy.2⟩

/-- **Lemma 3.1 of [Saglam2027] from the Kirshner–Samorodnitsky bounds.** For every `ε > 0` there
are `K` and `N` such that for all `n ≥ N` and `K log₂ n ≤ w ≤ (1 / 2 - ε) n`, the
Kirshner–Samorodnitsky bounds at `n` and `w` imply the moment and tail estimates of Lemma 3.1 with
moment constant `C = 2`. -/
theorem exists_puncturedBallFourierBounds_of_ks {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, K * logb 2 n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      KSThirdMomentBound n w → KSTailBound n w → PuncturedBallFourierBounds n w 2 := by
  obtain ⟨c, hc, hγ⟩ := exists_mul_le_ksGamma hε
  refine ⟨max (4 / c) (2 / ε ^ 2), max 2 ⌈2 / ε ^ 2⌉₊, fun n hn w hKw hρ hM hT => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hnε : 2 / ε ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlg : 1 ≤ logb 2 n := by
    rw [le_logb_iff_rpow_le one_lt_two hnpos, rpow_one]; exact_mod_cast hn2
  have hK4 : 4 / c ≤ max (4 / c) (2 / ε ^ 2) := le_max_left _ _
  have hKε : 2 / ε ^ 2 ≤ max (4 / c) (2 / ε ^ 2) := le_max_right _ _
  have hw0 : 0 < w := by
    have : (0 : ℝ) < w := lt_of_lt_of_le (by positivity) hKw
    exact_mod_cast this
  have hwn : 2 * w < n := by
    have : (0 : ℝ) < w := by exact_mod_cast hw0
    have : (2 * w : ℝ) < n := by nlinarith
    exact_mod_cast this
  refine ⟨moment_le_of_ksThirdMomentBound hM hw0 hwn
    hc (hγ _ (by positivity) (by rw [div_le_iff₀ hnpos]; exact hρ))
    (by rw [div_le_iff₀ hc] at hK4; linarith) hKw,
    tail_le_of_ksTailBound hT hw0 hε hρ hKε hnε hKw⟩

end KirshnerSamorodnitsky

end Cslib.Code
