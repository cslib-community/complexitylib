/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Complexity.Foundations.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Moments of the privacy loss

For mass functions `p`, `q` on a countable type, `lossMoment t p q = ∑ a, p a · (p a / q a) ^ t`
is the moment generating function of the privacy loss `ln (p a / q a)` [DworkRoth2014, §2.3].
Markov's inequality turns a moment bound into an event bound
(`tsum_indicator_le_lossMoment`). When the likelihood ratio lies in `[e^{-ε}, e^ε]`, convexity
of `x ↦ x ^ (1 + t)` bounds the moment by `cosh (ε t) + tanh (ε / 2) · sinh (ε t)` per unit of
mass (`lossMoment_le_of_le_mul`), hence by `exp (tanh (ε / 2) · ε t + (ε t)² / 2)`
(`lossMoment_le_exp`). The last step is Hoeffding's lemma for the two-point law on `±ε t`
(`Real.cosh_add_mul_sinh_le_exp`; compare `Cslib.one_sub_mul_exp_add_mul_exp_le`). This is the
per-round step of the proof of advanced composition.

For approximate differential privacy, `exists_le_of_tsum_tsub_le` splits an `(ε, δ)`-close pair
of distributions into sub-probability parts that are `ε`-close in both directions and keep all but
`δ` of the mass.

## Main definitions

* `Cslib.Privacy.lossMoment`: the moment generating function of the privacy loss.

## Main results

* `Cslib.Privacy.tsum_indicator_le_lossMoment`: Markov's inequality for the privacy loss.
* `Cslib.Privacy.lossMoment_le_of_le_mul`, `Cslib.Privacy.lossMoment_le_exp`: the moment bound
  for an `ε`-close pair.
* `Cslib.Privacy.exists_le_of_tsum_tsub_le`: `ε`-close sub-probability parts of an
  `(ε, δ)`-close pair.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe u

variable {α : Type u}

section Moment

/-- The privacy-loss moment `∑ a, p a · (p a / q a) ^ t`: for probability mass functions `p`
and `q`, the moment generating function `E_{a ∼ p}[exp (t · L(a))]` of the privacy loss
`L(a) = ln (p a / q a)` [DworkRoth2014, §2.3]. The masses may be sub-probabilities. -/
noncomputable def lossMoment (t : ℝ) (p q : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * (p a / q a) ^ t

theorem lossMoment_def (t : ℝ) (p q : α → ℝ≥0∞) :
    lossMoment t p q = ∑' a, p a * (p a / q a) ^ t := by
  rw [lossMoment]

/-- Pointwise Markov bound: either `p ≤ e^{ε'} q`, or the loss exceeds `ε'` and
`p ≤ e^{-t ε'} · p · (p / q) ^ t`. -/
private theorem le_mul_add_mul_rpow {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : ℝ≥0∞) :
    p ≤ ENNReal.ofReal (Real.exp ε') * q +
      ENNReal.ofReal (Real.exp (-(t * ε'))) * (p * (p / q) ^ t) := by
  set E := ENNReal.ofReal (Real.exp ε')
  rcases le_or_gt p (E * q) with h | h
  · exact h.trans le_self_add
  refine le_add_left ?_
  have hE0 : E ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hEt : E ^ t = ENNReal.ofReal (Real.exp (t * ε')) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht, ← Real.exp_mul, mul_comm]
  have hq : q ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.mul_top hE0] at h
    exact not_top_lt h
  have hdiv : E ≤ p / q := by
    rw [ENNReal.le_div_iff_mul_le (Or.inr (ne_bot_of_gt h)) (Or.inl hq)]
    exact h.le
  calc p = ENNReal.ofReal (Real.exp (-(t * ε'))) * E ^ t * p := by
        rw [hEt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(t * ε'))) * (p / q) ^ t * p := by
        gcongr
    _ = _ := by ring

/-- Markov's inequality for the privacy loss: for every event `S` and every `ε'`, `t ≥ 0`,
`p(S) ≤ e^{ε'} · q(S) + e^{-t ε'} · lossMoment t p q`. -/
theorem tsum_indicator_le_lossMoment {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : α → ℝ≥0∞)
    (S : Set α) :
    ∑' a, S.indicator p a ≤ ENNReal.ofReal (Real.exp ε') * ∑' a, S.indicator q a +
      ENNReal.ofReal (Real.exp (-(t * ε'))) * lossMoment t p q := by
  rw [lossMoment, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ S
  · simp only [Set.indicator_of_mem ha]
    exact le_mul_add_mul_rpow ht ε' (p a) (q a)
  · simp only [Set.indicator_of_notMem ha]
    exact zero_le

end Moment

section Chord

/-- The chord bound for `x ↦ x ^ (1 + t)` on `[E⁻¹, E]`, in real numbers. -/
private theorem mul_div_rpow_add_le {E t P Q : ℝ} (hE : 1 < E) (ht : 0 ≤ t) (hP : 0 < P)
    (hQ : 0 < Q) (hPQ : P ≤ E * Q) (hQP : Q ≤ E * P) :
    P * (P / Q) ^ t + (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q ≤
      (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) * P := by
  have hE0 : 0 < E := by linarith
  have hEinv : E⁻¹ < E := (inv_lt_one_of_one_lt₀ hE).trans hE
  have hD : 0 < E - E⁻¹ := sub_pos.mpr hEinv
  have hF : 0 < E ^ t := Real.rpow_pos_of_pos hE0 t
  have hw0 : 0 < P / Q := div_pos hP hQ
  have hwle : P / Q ≤ E := by rw [div_le_iff₀ hQ]; exact hPQ
  have hwge : E⁻¹ ≤ P / Q := by
    rw [le_div_iff₀ hQ, inv_mul_le_iff₀ hE0]
    exact hQP
  -- convexity of `x ↦ x ^ (1 + t)` between `E⁻¹` and `E`
  have ha : 0 ≤ (E - P / Q) / (E - E⁻¹) := div_nonneg (by linarith) hD.le
  have hb : 0 ≤ (P / Q - E⁻¹) / (E - E⁻¹) := div_nonneg (by linarith) hD.le
  have hab : (E - P / Q) / (E - E⁻¹) + (P / Q - E⁻¹) / (E - E⁻¹) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hD.ne']
    ring
  have hconv := (convexOn_rpow (p := 1 + t) (by linarith)).2 (Set.mem_Ici.mpr (inv_pos.mpr hE0).le)
    (Set.mem_Ici.mpr hE0.le) ha hb hab
  have hcomb : (E - P / Q) / (E - E⁻¹) * E⁻¹ + (P / Q - E⁻¹) / (E - E⁻¹) * E = P / Q := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD.ne']
    ring
  simp only [smul_eq_mul] at hconv
  rw [hcomb] at hconv
  rw [Real.rpow_add hw0, Real.rpow_one, Real.rpow_add (inv_pos.mpr hE0), Real.rpow_one,
    Real.rpow_add hE0, Real.rpow_one, Real.inv_rpow hE0.le] at hconv
  have hkey : P * (P / Q) ^ t = Q * (P / Q * (P / Q) ^ t) := by
    field_simp
  rw [hkey]
  calc Q * (P / Q * (P / Q) ^ t) + (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q
      ≤ Q * ((E - P / Q) / (E - E⁻¹) * (E⁻¹ * (E ^ t)⁻¹) +
          (P / Q - E⁻¹) / (E - E⁻¹) * (E * E ^ t)) +
          (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) * Q := by gcongr
    _ = (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) * P := by
        generalize hDdef : E - E⁻¹ = D at *
        have hD0 : D ≠ 0 := hD.ne'
        field_simp
        ring

end Chord

section SingleRound

/-- The moment bound for one round: if the likelihood ratio of `p` and `q` lies in
`[e^{-ε}, e^ε]` and `p` has at most the mass of `q`, then
`lossMoment t p q ≤ (cosh (ε t) + tanh (ε / 2) · sinh (ε t)) · ∑ p`. The bound comes from the
chord of the convex function `x ↦ x ^ (1 + t)` between `e^{-ε}` and `e^ε`, and is attained by
two-point distributions whose likelihood ratio takes only the values `e^{±ε}`. -/
theorem lossMoment_le_of_le_mul {p q : α → ℝ≥0∞} {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpq : ∀ a, p a ≤ ENNReal.ofReal (Real.exp ε) * q a)
    (hqp : ∀ a, q a ≤ ENNReal.ofReal (Real.exp ε) * p a)
    (hsum : ∑' a, p a ≤ ∑' a, q a) (hfin : ∑' a, q a ≠ ⊤) :
    lossMoment t p q ≤ ENNReal.ofReal (Real.cosh (ε * t) +
      Real.tanh (ε / 2) * Real.sinh (ε * t)) * ∑' a, p a := by
  rw [Real.tanh_half_eq_exp_sub_one_div]
  have hq : ∀ a, q a ≠ ⊤ := ne_top_of_tsum_ne_top hfin
  have hp : ∀ a, p a ≠ ⊤ := fun a => ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq a)) (hpq a)
  rcases hε.eq_or_lt with rfl | hε
  · have heq : ∀ a, p a = q a := fun a => le_antisymm
      (by simpa using hpq a) (by simpa using hqp a)
    simp only [zero_mul, Real.cosh_zero, Real.sinh_zero, mul_zero, add_zero, ENNReal.ofReal_one,
      one_mul, lossMoment]
    refine tsum_le_tsum fun a => ?_
    rw [heq a]
    rcases eq_or_ne (q a) 0 with h0 | h0
    · simp [h0]
    · rw [ENNReal.div_self h0 (hq a), ENNReal.one_rpow, mul_one]
  set E := Real.exp ε with hEdef
  have hE : 1 < E := Real.one_lt_exp_iff.mpr hε
  have hE0 : 0 < E := Real.exp_pos ε
  have hF : 0 < E ^ t := Real.rpow_pos_of_pos hE0 t
  have hEinv : E⁻¹ < E := (inv_lt_one_of_one_lt₀ hE).trans hE
  have hD : 0 < E - E⁻¹ := sub_pos.mpr hEinv
  set Y := (E ^ t - (E ^ t)⁻¹) / (E - E⁻¹) with hYdef
  set A := (E * E ^ t - (E * E ^ t)⁻¹) / (E - E⁻¹) with hAdef
  have hF1 : 1 ≤ E ^ t := Real.one_le_rpow hE.le ht
  have hY : 0 ≤ Y := div_nonneg (sub_nonneg.mpr ((inv_le_one_of_one_le₀ hF1).trans hF1)) hD.le
  have hEF1 : 1 ≤ E * E ^ t := one_le_mul_of_one_le_of_one_le hE.le hF1
  have hA : 0 ≤ A := div_nonneg (sub_nonneg.mpr ((inv_le_one_of_one_le₀ hEF1).trans hEF1)) hD.le
  -- pointwise chord bound in `ℝ≥0∞`
  have hpt : ∀ a, p a * (p a / q a) ^ t + ENNReal.ofReal Y * q a ≤ ENNReal.ofReal A * p a := by
    intro a
    rcases eq_or_ne (q a) 0 with hq0 | hq0
    · have hp0 : p a = 0 := by simpa [hq0] using hpq a
      simp [hp0, hq0]
    rcases eq_or_ne (p a) 0 with hp0 | hp0
    · have : q a = 0 := by simpa [hp0] using hqp a
      exact absurd this hq0
    have hP : 0 < (p a).toReal := ENNReal.toReal_pos hp0 (hp a)
    have hQ : 0 < (q a).toReal := ENNReal.toReal_pos hq0 (hq a)
    have hPQ : (p a).toReal ≤ E * (q a).toReal := by
      have := (ENNReal.toReal_le_toReal (hp a) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hq a))).mpr (hpq a)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0.le] at this
    have hQP : (q a).toReal ≤ E * (p a).toReal := by
      have := (ENNReal.toReal_le_toReal (hq a) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hp a))).mpr (hqp a)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE0.le] at this
    have hreal := mul_div_rpow_add_le hE ht hP hQ hPQ hQP
    rw [← ENNReal.ofReal_toReal (hp a), ← ENNReal.ofReal_toReal (hq a),
      ← ENNReal.ofReal_div_of_pos hQ, ENNReal.ofReal_rpow_of_nonneg (div_pos hP hQ).le ht,
      ← ENNReal.ofReal_mul hP.le, ← ENNReal.ofReal_mul hY,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [hYdef, hAdef] using hreal)
  have hsum' : lossMoment t p q + ENNReal.ofReal Y * ∑' a, p a ≤ ENNReal.ofReal A * ∑' a, p a :=
    calc lossMoment t p q + ENNReal.ofReal Y * ∑' a, p a
        ≤ lossMoment t p q + ENNReal.ofReal Y * ∑' a, q a := by gcongr
      _ = ∑' a, (p a * (p a / q a) ^ t + ENNReal.ofReal Y * q a) := by
          rw [lossMoment, ← ENNReal.tsum_mul_left, ← tsum_add]
      _ ≤ ∑' a, ENNReal.ofReal A * p a := tsum_le_tsum hpt
      _ = ENNReal.ofReal A * ∑' a, p a := ENNReal.tsum_mul_left
  have hfinp : ∑' a, p a ≠ ⊤ := ne_top_of_le_ne_top hfin hsum
  calc lossMoment t p q ≤ ENNReal.ofReal A * ∑' a, p a - ENNReal.ofReal Y * ∑' a, p a :=
        ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinp) hsum'
    _ = ENNReal.ofReal (A - Y) * ∑' a, p a := by
        rw [ENNReal.ofReal_sub _ hY, ENNReal.sub_mul fun _ _ => hfinp]
    _ = _ := by
        congr 2
        rw [hAdef, hYdef, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, Real.exp_mul]
        rw [← sub_div, div_eq_iff hD.ne']
        have hE1 : E + 1 ≠ 0 := by positivity
        field_simp
        ring

/-- The moment bound in exponential form: with `s = ε t`,
`lossMoment t p q ≤ exp (tanh (ε / 2) · s + s² / 2) · ∑ p`. -/
theorem lossMoment_le_exp {p q : α → ℝ≥0∞} {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpq : ∀ a, p a ≤ ENNReal.ofReal (Real.exp ε) * q a)
    (hqp : ∀ a, q a ≤ ENNReal.ofReal (Real.exp ε) * p a)
    (hsum : ∑' a, p a ≤ ∑' a, q a) (hfin : ∑' a, q a ≠ ⊤) :
    lossMoment t p q ≤
      ENNReal.ofReal (Real.exp (Real.tanh (ε / 2) * (ε * t) + (ε * t) ^ 2 / 2)) * ∑' a, p a := by
  refine (lossMoment_le_of_le_mul hε ht hpq hqp hsum hfin).trans (mul_le_mul' ?_ le_rfl)
  refine ENNReal.ofReal_le_ofReal (Real.cosh_add_mul_sinh_le_exp ?_ (mul_nonneg hε ht))
  exact Real.tanh_nonneg_iff.mpr (by linarith)

end SingleRound

section SubKernel

private theorem min_le_mul_min {c : ℝ≥0∞} (hc : 1 ≤ c) (x y : ℝ≥0∞) :
    min y (c * x) ≤ c * min x (c * y) := by
  rcases le_total x (c * y) with h | h
  · rw [min_eq_left h]
    exact min_le_right _ _
  · rw [min_eq_right h]
    calc min y (c * x) ≤ y := min_le_left _ _
      _ = 1 * (1 * y) := by rw [one_mul, one_mul]
      _ ≤ c * (c * y) := by gcongr

private theorem exists_mix {P : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : 1 ≤ c) (p₀ q₀ : α → ℝ≥0∞)
    (hp₀ : ∀ a, p₀ a ≤ P a) (hpq : ∀ a, p₀ a ≤ c * q₀ a) (hqp : ∀ a, q₀ a ≤ c * p₀ a)
    (hfin : ∑' a, p₀ a ≠ ⊤) (hlt : ∑' a, q₀ a < ∑' a, p₀ a) :
    ∃ p : α → ℝ≥0∞, (∀ a, p a ≤ P a) ∧ (∀ a, p a ≤ c * q₀ a) ∧ (∀ a, q₀ a ≤ c * p a) ∧
      ∑' a, p a = ∑' a, q₀ a := by
  set u : α → ℝ≥0∞ := fun a => min (p₀ a) (q₀ a) with hu
  have hup : ∀ a, u a ≤ p₀ a := fun a => min_le_left _ _
  have huq : ∀ a, u a ≤ q₀ a := fun a => min_le_right _ _
  have hfq : ∑' a, q₀ a ≠ ⊤ := ne_top_of_lt hlt
  have hfu : ∑' a, u a ≠ ⊤ := ne_top_of_le_ne_top hfin (tsum_le_tsum hup)
  set mp := ∑' a, p₀ a with hmp
  set mq := ∑' a, q₀ a with hmq
  set mu := ∑' a, u a with hmu
  have hmuq : mu.toReal ≤ mq.toReal := (ENNReal.toReal_le_toReal hfu hfq).mpr (tsum_le_tsum huq)
  have hmqp : mq.toReal < mp.toReal := (ENNReal.toReal_lt_toReal hfq hfin).mpr hlt
  have hden : 0 < mp.toReal - mu.toReal := by linarith
  set s := (mp.toReal - mq.toReal) / (mp.toReal - mu.toReal) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hsden : s * (mp.toReal - mu.toReal) = mp.toReal - mq.toReal := div_mul_cancel₀ _ hden.ne'
  have hθ : ENNReal.ofReal (1 - s) + ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hs0, sub_add_cancel, ENNReal.ofReal_one]
  have hcu : ∀ a, q₀ a ≤ c * u a := fun a => by
    rcases le_total (p₀ a) (q₀ a) with h | h
    · change q₀ a ≤ c * min (p₀ a) (q₀ a)
      rw [min_eq_left h]
      exact hqp a
    · change q₀ a ≤ c * min (p₀ a) (q₀ a)
      rw [min_eq_right h]
      calc q₀ a = 1 * q₀ a := (one_mul _).symm
        _ ≤ c * q₀ a := by gcongr
  refine ⟨fun a => ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a, fun a => ?_,
    fun a => ?_, fun a => ?_, ?_⟩
  · calc ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a
        ≤ ENNReal.ofReal (1 - s) * P a + ENNReal.ofReal s * P a := by
          gcongr
          · exact hp₀ a
          · exact (hup a).trans (hp₀ a)
      _ = P a := by rw [← add_mul, hθ, one_mul]
  · calc ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a
        ≤ ENNReal.ofReal (1 - s) * (c * q₀ a) + ENNReal.ofReal s * (c * q₀ a) := by
          gcongr
          · exact hpq a
          · calc u a ≤ q₀ a := huq a
              _ = 1 * q₀ a := (one_mul _).symm
              _ ≤ c * q₀ a := by gcongr
      _ = c * q₀ a := by rw [← add_mul, hθ, one_mul]
  · calc q₀ a = ENNReal.ofReal (1 - s) * q₀ a + ENNReal.ofReal s * q₀ a := by
          rw [← add_mul, hθ, one_mul]
      _ ≤ ENNReal.ofReal (1 - s) * (c * p₀ a) + ENNReal.ofReal s * (c * u a) := by
          gcongr
          · exact hqp a
          · exact hcu a
      _ = c * (ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a) := by ring
  · rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← hmp, ← hmu,
      ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hfu, ← ENNReal.ofReal_toReal hfq,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hs0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
        (mul_nonneg hs0 ENNReal.toReal_nonneg)]
    congr 1
    linear_combination -hsden

/-- Sub-probability parts of an `(ε, δ)`-close pair. If both hockey-stick divergences of `P` and
`Q` at factor `c ≥ 1` are at most `δ`, there are `p ≤ P` and `q ≤ Q` whose likelihood ratio is
bounded by `c` in both directions, with `∑ p ≤ ∑ q` and `∑ p ≥ 1 - δ`. The construction takes
`min P (c Q)` and `min Q (c P)`, mixing the former with `min (min P (c Q)) (min Q (c P))` when it
carries more mass. -/
theorem exists_le_of_tsum_tsub_le (P Q : PMF α) {c : ℝ≥0∞} (hc : 1 ≤ c) {δ : ℝ≥0∞}
    (hPQ : ∑' a, (P a - c * Q a) ≤ δ) (hQP : ∑' a, (Q a - c * P a) ≤ δ) :
    ∃ p q : α → ℝ≥0∞, (∀ a, p a ≤ P a) ∧ (∀ a, q a ≤ Q a) ∧ (∀ a, p a ≤ c * q a) ∧
      (∀ a, q a ≤ c * p a) ∧ ∑' a, p a ≤ ∑' a, q a ∧ 1 ≤ ∑' a, p a + δ := by
  have hmass : ∀ P Q : PMF α, ∑' a, (P a - c * Q a) ≤ δ →
      1 ≤ ∑' a, min (P a) (c * Q a) + δ := fun P Q h => by
    calc (1 : ℝ≥0∞) = ∑' a, P a := P.tsum_coe.symm
      _ = ∑' a, (P a - c * Q a) + ∑' a, min (P a) (c * Q a) := by
          rw [← tsum_add]
          exact tsum_congr fun a => tsub_add_min.symm
      _ ≤ ∑' a, min (P a) (c * Q a) + δ := by rw [add_comm]; gcongr
  have hpq : ∀ a, min (P a) (c * Q a) ≤ c * min (Q a) (c * P a) := fun a =>
    min_le_mul_min hc (Q a) (P a)
  have hqp : ∀ a, min (Q a) (c * P a) ≤ c * min (P a) (c * Q a) := fun a =>
    min_le_mul_min hc (P a) (Q a)
  rcases le_or_gt (∑' a, min (P a) (c * Q a)) (∑' a, min (Q a) (c * P a)) with hle | hlt
  · exact ⟨_, _, fun a => min_le_left _ _, fun a => min_le_left _ _, hpq, hqp, hle,
      hmass P Q hPQ⟩
  · have hfin : ∑' a, min (P a) (c * Q a) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        ((tsum_le_tsum fun a => min_le_left _ _).trans P.tsum_coe.le)
    obtain ⟨p, hpP, hpq', hqp', hsum⟩ := exists_mix hc _ _ (fun a => min_le_left _ _) hpq hqp
      hfin hlt
    refine ⟨p, _, hpP, fun a => min_le_left _ _, hpq', hqp', hsum.le, ?_⟩
    rw [hsum]
    exact hmass Q P hQP

end SubKernel

end Cslib.Privacy
