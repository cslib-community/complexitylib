/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Root errors and the homogeneous loss

The estimators of the OpenAI preprint measure the error of a nonnegative quantity by the
difference of `s`-th roots, `|H^{1/s} - H'^{1/s}|`, rather than by `|H - H'|`
[OpenAI2026LogSpace, Sections 5.6 and 7.3]. This file collects the scalar facts behind that choice.

**Ordinary versus root error** [OpenAI2026LogSpace, (5.21)]. For `0 ≤ z, w ≤ C`,
`|z - w| ≤ s C^{(s-1)/s} |z^{1/s} - w^{1/s}|` (`Cslib.abs_sub_le_mul_abs_rpow_inv_sub`).

**The homogeneous loss** [OpenAI2026LogSpace, (7.6), Lemma 7.2]. For nonnegative `H`, `H'`,
`L(H, H') = |H - H'|^s / (H + H')^{s-1}` (`Cslib.homogeneousLoss`; for `s ≥ 1`, Lean's division
by zero gives the preprint's value `0` at `H = H' = 0`). It is homogeneous of degree one. It is
comparable to the root error,
`|H^{1/s} - H'^{1/s}|^s / 2^{s-1} ≤ L(H, H') ≤ s^s |H^{1/s} - H'^{1/s}|^s`
(`Cslib.rpow_inv_sub_pow_le_homogeneousLoss`, `Cslib.homogeneousLoss_le_rpow_inv_sub_pow`).
Unlike the root error, it contracts under nonnegative mixtures
(`Cslib.homogeneousLoss_sum_le`), so it passes through conditional expectations. Finally it
controls a clipped relative error: if `0 ≤ H ≤ C₀ G`, then for every `a > 0` and `H' ≥ 0`,
`a · min (1, |H - H'| / (a + G))^s ≤ 2 (3 C₀ + 3)^{s-1} L(H, H')`
(`Cslib.mul_min_pow_le_homogeneousLoss`, (7.7)).

## Main definitions

* `Cslib.homogeneousLoss`: the loss `|H - H'|^s / (H + H')^{s-1}`.

## Main results

* `Cslib.abs_sub_le_mul_abs_rpow_inv_sub`: ordinary error is controlled by root error.
* `Cslib.homogeneousLoss_nonneg`, `Cslib.homogeneousLoss_self`, `Cslib.homogeneousLoss_comm`,
  `Cslib.homogeneousLoss_mul`: basic properties.
* `Cslib.rpow_inv_sub_pow_le_homogeneousLoss`, `Cslib.homogeneousLoss_le_rpow_inv_sub_pow`:
  comparability with the root error.
* `Cslib.homogeneousLoss_sum_le`: contraction under nonnegative mixtures and sums.
* `Cslib.mul_min_pow_le_homogeneousLoss`: the clipped relative error bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  (5.21), (7.6), (7.7) and Lemma 7.2 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Cslib

/-- **Ordinary error is controlled by root error** [OpenAI2026LogSpace, (5.21)]. For
`0 ≤ z, w ≤ C` and `s ≥ 1`, `|z - w| ≤ s C^{(s-1)/s} |z^{1/s} - w^{1/s}|`. -/
theorem abs_sub_le_mul_abs_rpow_inv_sub {s : ℕ} (hs : s ≠ 0) {z w C : ℝ} (hz : 0 ≤ z)
    (hw : 0 ≤ w) (hzC : z ≤ C) (hwC : w ≤ C) :
    |z - w| ≤ s * C ^ (((s : ℝ) - 1) / s) * |z ^ (s⁻¹ : ℝ) - w ^ (s⁻¹ : ℝ)| := by
  have hC : 0 ≤ C := hz.trans hzC
  have hroot : C ^ (((s : ℝ) - 1) / s) = (C ^ (s⁻¹ : ℝ)) ^ (s - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hs),
      Nat.cast_one, div_eq_inv_mul]
  have hmax : max |z ^ (s⁻¹ : ℝ)| |w ^ (s⁻¹ : ℝ)| ≤ C ^ (s⁻¹ : ℝ) := by
    have hs' : (0 : ℝ) ≤ (s : ℝ)⁻¹ := by positivity
    rw [abs_of_nonneg (Real.rpow_nonneg hz _), abs_of_nonneg (Real.rpow_nonneg hw _)]
    exact max_le (Real.rpow_le_rpow hz hzC hs') (Real.rpow_le_rpow hw hwC hs')
  calc |z - w| = |(z ^ (s⁻¹ : ℝ)) ^ s - (w ^ (s⁻¹ : ℝ)) ^ s| := by
        rw [Real.rpow_inv_natCast_pow hz hs, Real.rpow_inv_natCast_pow hw hs]
    _ ≤ |z ^ (s⁻¹ : ℝ) - w ^ (s⁻¹ : ℝ)| * s * max |z ^ (s⁻¹ : ℝ)| |w ^ (s⁻¹ : ℝ)| ^ (s - 1) :=
        abs_pow_sub_pow_le _ _ _
    _ ≤ |z ^ (s⁻¹ : ℝ) - w ^ (s⁻¹ : ℝ)| * s * (C ^ (s⁻¹ : ℝ)) ^ (s - 1) := by gcongr
    _ = s * C ^ (((s : ℝ) - 1) / s) * |z ^ (s⁻¹ : ℝ) - w ^ (s⁻¹ : ℝ)| := by rw [hroot]; ring

/-- The **homogeneous loss** `L(H, H') = |H - H'|^s / (H + H')^{s-1}` of the OpenAI preprint
[OpenAI2026LogSpace, (7.6)]. On nonnegative arguments with `s ≥ 1` it agrees with the preprint's
definition, which sets `L(0, 0) = 0`. -/
noncomputable def homogeneousLoss (s : ℕ) (H H' : ℝ) : ℝ :=
  |H - H'| ^ s / (H + H') ^ (s - 1)

variable {s : ℕ} {H H' : ℝ}

theorem homogeneousLoss_nonneg (hH : 0 ≤ H) (hH' : 0 ≤ H') : 0 ≤ homogeneousLoss s H H' := by
  unfold homogeneousLoss; positivity

@[simp]
theorem homogeneousLoss_self (hs : s ≠ 0) (H : ℝ) : homogeneousLoss s H H = 0 := by
  simp [homogeneousLoss, hs]

theorem homogeneousLoss_comm (s : ℕ) (H H' : ℝ) :
    homogeneousLoss s H H' = homogeneousLoss s H' H := by
  rw [homogeneousLoss, homogeneousLoss, abs_sub_comm, add_comm]

/-- The loss is homogeneous of degree one. -/
theorem homogeneousLoss_mul (hs : s ≠ 0) {c : ℝ} (hc : 0 ≤ c) (H H' : ℝ) :
    homogeneousLoss s (c * H) (c * H') = c * homogeneousLoss s H H' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
  rcases hc.eq_or_lt with rfl | hc
  · simp [homogeneousLoss]
  simp only [homogeneousLoss, ← mul_sub, ← mul_add, abs_mul, abs_of_pos hc, mul_pow,
    Nat.add_sub_cancel]
  rw [mul_div_mul_comm, pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero k hc.ne')]

/-- The loss in terms of the roots `a = H^{1/s}` and `b = H'^{1/s}`, with `b ≤ a`. -/
private theorem homogeneousLoss_pow_pow {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    homogeneousLoss s (a ^ s) (b ^ s) = (a ^ s - b ^ s) ^ s / (a ^ s + b ^ s) ^ (s - 1) := by
  rw [homogeneousLoss, abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hb hba s))]

/-- `a^{s-1} (a - b) ≤ a^s - b^s ≤ s a^{s-1} (a - b)` for `0 ≤ b ≤ a`. -/
private theorem pow_sub_pow_bounds {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hs : s ≠ 0) :
    a ^ (s - 1) * (a - b) ≤ a ^ s - b ^ s ∧ a ^ s - b ^ s ≤ s * a ^ (s - 1) * (a - b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
  have ha : 0 ≤ a := hb.trans hba
  have hk : b ^ k ≤ a ^ k := pow_le_pow_left₀ hb hba k
  simp only [Nat.add_sub_cancel]
  constructor
  · simp only [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hk hb]
  · have h := abs_pow_sub_pow_le a b (k + 1)
    rw [abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hb hba _)), abs_of_nonneg (sub_nonneg.2 hba),
      abs_of_nonneg ha, abs_of_nonneg hb, max_eq_left hba, Nat.add_sub_cancel] at h
    exact h.trans (le_of_eq (by ring))

/-- Comparability in terms of the roots, with `b ≤ a`. -/
private theorem homogeneousLoss_pow_pow_bounds {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hs : s ≠ 0) :
    (a - b) ^ s / 2 ^ (s - 1) ≤ homogeneousLoss s (a ^ s) (b ^ s) ∧
      homogeneousLoss s (a ^ s) (b ^ s) ≤ (s : ℝ) ^ s * (a - b) ^ s := by
  have ha : 0 ≤ a := hb.trans hba
  rw [homogeneousLoss_pow_pow hb hba]
  rcases ha.eq_or_lt with rfl | ha
  · have : b = 0 := le_antisymm hba hb
    subst this
    simp [zero_pow hs]
  obtain ⟨hlo, hhi⟩ := pow_sub_pow_bounds hb hba hs
  have hab : 0 ≤ a - b := sub_nonneg.2 hba
  have hden : 0 < (a ^ s + b ^ s) ^ (s - 1) := by positivity
  have hbs : b ^ s ≤ a ^ s := pow_le_pow_left₀ hb hba s
  have key : (a ^ (s - 1)) ^ s = (a ^ s) ^ (s - 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
  constructor
  · rw [div_le_div_iff₀ (by positivity) hden]
    calc (a - b) ^ s * (a ^ s + b ^ s) ^ (s - 1) ≤ (a - b) ^ s * (2 * a ^ s) ^ (s - 1) := by
          gcongr; linarith
      _ = (a ^ (s - 1) * (a - b)) ^ s * 2 ^ (s - 1) := by rw [mul_pow, mul_pow, key]; ring
      _ ≤ (a ^ s - b ^ s) ^ s * 2 ^ (s - 1) := by gcongr
  · rw [div_le_iff₀ hden]
    calc (a ^ s - b ^ s) ^ s ≤ (s * a ^ (s - 1) * (a - b)) ^ s := by
          gcongr
      _ = (s : ℝ) ^ s * (a - b) ^ s * (a ^ s) ^ (s - 1) := by rw [mul_pow, mul_pow, key]; ring
      _ ≤ (s : ℝ) ^ s * (a - b) ^ s * (a ^ s + b ^ s) ^ (s - 1) := by
          gcongr; linarith [pow_nonneg hb s]

/-- Reduce a statement about `H, H'` to their roots in decreasing order. -/
private theorem homogeneousLoss_bounds (hs : s ≠ 0) (hH : 0 ≤ H) (hH' : 0 ≤ H') :
    |H ^ (s⁻¹ : ℝ) - H' ^ (s⁻¹ : ℝ)| ^ s / 2 ^ (s - 1) ≤ homogeneousLoss s H H' ∧
      homogeneousLoss s H H' ≤ (s : ℝ) ^ s * |H ^ (s⁻¹ : ℝ) - H' ^ (s⁻¹ : ℝ)| ^ s := by
  wlog hle : H' ≤ H generalizing H H'
  · rw [homogeneousLoss_comm, abs_sub_comm]
    exact this hH' hH (le_of_not_ge hle)
  have hb : 0 ≤ H' ^ (s⁻¹ : ℝ) := Real.rpow_nonneg hH' _
  have hba : H' ^ (s⁻¹ : ℝ) ≤ H ^ (s⁻¹ : ℝ) := Real.rpow_le_rpow hH' hle (by positivity)
  have h := homogeneousLoss_pow_pow_bounds hb hba hs
  rw [Real.rpow_inv_natCast_pow hH hs, Real.rpow_inv_natCast_pow hH' hs] at h
  rwa [abs_of_nonneg (sub_nonneg.2 hba)]

/-- The homogeneous loss bounds the root error from above [OpenAI2026LogSpace, Lemma 7.2]. -/
theorem rpow_inv_sub_pow_le_homogeneousLoss (hs : s ≠ 0) (hH : 0 ≤ H) (hH' : 0 ≤ H') :
    |H ^ (s⁻¹ : ℝ) - H' ^ (s⁻¹ : ℝ)| ^ s ≤ 2 ^ (s - 1) * homogeneousLoss s H H' := by
  have h := (homogeneousLoss_bounds hs hH hH').1
  rwa [div_le_iff₀ (by positivity), mul_comm] at h

/-- The root error bounds the homogeneous loss from above [OpenAI2026LogSpace, Lemma 7.2]. -/
theorem homogeneousLoss_le_rpow_inv_sub_pow (hs : s ≠ 0) (hH : 0 ≤ H) (hH' : 0 ≤ H') :
    homogeneousLoss s H H' ≤ (s : ℝ) ^ s * |H ^ (s⁻¹ : ℝ) - H' ^ (s⁻¹ : ℝ)| ^ s :=
  (homogeneousLoss_bounds hs hH hH').2

/-- **Mixture contraction** [OpenAI2026LogSpace, Lemma 7.2]: the homogeneous loss of two
nonnegative mixtures is at most the mixture of the losses. With unit weights this is
subadditivity over finite sums. -/
theorem homogeneousLoss_sum_le {ι : Type*} (t : Finset ι) (hs : s ≠ 0) {w F F' : ι → ℝ}
    (hw : ∀ i ∈ t, 0 ≤ w i) (hF : ∀ i ∈ t, 0 ≤ F i) (hF' : ∀ i ∈ t, 0 ≤ F' i) :
    homogeneousLoss s (∑ i ∈ t, w i * F i) (∑ i ∈ t, w i * F' i) ≤
      ∑ i ∈ t, w i * homogeneousLoss s (F i) (F' i) := by
  set S : ι → ℝ := fun i => F i + F' i
  set D : ι → ℝ := fun i => |F i - F' i|
  set A := ∑ i ∈ t, w i * S i
  have hS : ∀ i ∈ t, 0 ≤ S i := fun i hi => add_nonneg (hF i hi) (hF' i hi)
  have hD : ∀ i ∈ t, D i ≤ S i := fun i hi =>
    (abs_sub _ _).trans (by rw [abs_of_nonneg (hF i hi), abs_of_nonneg (hF' i hi)])
  have hrhs : 0 ≤ ∑ i ∈ t, w i * homogeneousLoss s (F i) (F' i) :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (homogeneousLoss_nonneg (hF i hi) (hF' i hi))
  have hdiff : |∑ i ∈ t, w i * F i - ∑ i ∈ t, w i * F' i| ≤ ∑ i ∈ t, w i * D i := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i hi => ?_))
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
  have hsumS : ∑ i ∈ t, w i * F i + ∑ i ∈ t, w i * F' i = A := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => by simp only [S]; ring
  have hA : 0 ≤ A := sum_nonneg fun i hi => mul_nonneg (hw i hi) (hS i hi)
  rcases hA.eq_or_lt with hA0 | hApos
  · -- Every weighted pair vanishes, so the left side is `L(0, 0) = 0`.
    have hzero : ∀ i ∈ t, w i * S i = 0 :=
      (sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hw i hi) (hS i hi)).1 hA0.symm
    have hD0 : ∑ i ∈ t, w i * D i = 0 := sum_eq_zero fun i hi => by
      have := mul_le_mul_of_nonneg_left (hD i hi) (hw i hi)
      have := mul_nonneg (hw i hi) (abs_nonneg (F i - F' i))
      linarith [hzero i hi]
    have hl : |∑ i ∈ t, w i * F i - ∑ i ∈ t, w i * F' i| = 0 :=
      le_antisymm (hD0 ▸ hdiff) (abs_nonneg _)
    rw [homogeneousLoss, hl, zero_pow hs, zero_div]
    exact hrhs
  -- Jensen's inequality for `x ↦ x^s` with weights `w i S i / A` at the points `D i / S i`.
  set lam : ι → ℝ := fun i => w i * S i / A
  set x : ι → ℝ := fun i => D i / S i
  have hlam : ∀ i ∈ t, 0 ≤ lam i := fun i hi => div_nonneg (mul_nonneg (hw i hi) (hS i hi)) hA
  have hlam1 : ∑ i ∈ t, lam i = 1 := by rw [← sum_div, div_self hApos.ne']
  have hx : ∀ i ∈ t, 0 ≤ x i := fun i hi => div_nonneg (abs_nonneg _) (hS i hi)
  have hjensen := Real.pow_arith_mean_le_arith_mean_pow t lam x hlam hlam1 hx s
  have hmean : ∑ i ∈ t, lam i * x i = (∑ i ∈ t, w i * D i) / A := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    rcases (hS i hi).eq_or_lt with h0 | hpos
    · have : D i = 0 := le_antisymm (h0 ▸ hD i hi) (abs_nonneg _)
      simp only [lam, x, this, ← h0]; simp
    · simp only [lam, x]; field_simp
  have hmeanpow : ∑ i ∈ t, lam i * x i ^ s =
      (∑ i ∈ t, w i * homogeneousLoss s (F i) (F' i)) / A := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
    rcases (hS i hi).eq_or_lt with h0 | hpos
    · have : D i = 0 := le_antisymm (h0 ▸ hD i hi) (abs_nonneg _)
      simp only [lam, x, homogeneousLoss, this, ← h0]
      simp only [show |F i - F' i| = 0 from this]; simp
    · simp only [lam, x, homogeneousLoss, Nat.add_sub_cancel, D, S] at *
      rw [div_pow, pow_succ (F i + F' i) k]
      field_simp
  rw [hmean, hmeanpow, div_pow, div_le_div_iff₀ (by positivity) hApos] at hjensen
  rw [homogeneousLoss, hsumS]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
  rw [Nat.add_sub_cancel, div_le_iff₀ (by positivity)]
  have hk := pow_le_pow_left₀ (abs_nonneg _) hdiff (k + 1)
  rw [pow_succ A k, ← mul_assoc] at hjensen
  exact hk.trans (le_of_mul_le_mul_right hjensen hApos)

/-- **The clipped relative error** [OpenAI2026LogSpace, (7.7)]. If `0 ≤ H ≤ C₀ G`, then for every
`a > 0` and `H' ≥ 0`, `a · min (1, |H - H'| / (a + G))^s ≤ 2 (3 C₀ + 3)^{s-1} L(H, H')`. -/
theorem mul_min_pow_le_homogeneousLoss (hs : s ≠ 0) {C₀ G a : ℝ} (hC₀ : 0 ≤ C₀) (hG : 0 ≤ G)
    (ha : 0 < a) (hH : 0 ≤ H) (hHG : H ≤ C₀ * G) (hH' : 0 ≤ H') :
    a * min 1 (|H - H'| / (a + G)) ^ s ≤ 2 * (3 * C₀ + 3) ^ (s - 1) * homogeneousLoss s H H' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
  simp only [Nat.add_sub_cancel, homogeneousLoss]
  have haG : 0 < a + G := by positivity
  have hmin0 : 0 ≤ min 1 (|H - H'| / (a + G)) := le_min zero_le_one (by positivity)
  have hC : (3 : ℝ) ^ k ≤ (3 * C₀ + 3) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
  by_cases hcase : H' ≤ 2 * H + a
  · -- `H + H' ≤ (3 C₀ + 3) (a + G)`, and `a / (a + G)^{k+1} ≤ 1 / (a + G)^k`.
    have hsum : H + H' ≤ (3 * C₀ + 3) * (a + G) := by nlinarith
    rcases (add_nonneg hH hH').eq_or_lt with h0 | hpos
    · have h1 : H = 0 := by linarith
      have h2 : H' = 0 := by linarith
      simp [h1, h2]
    have hd : 0 ≤ |H - H'| := abs_nonneg _
    calc a * min 1 (|H - H'| / (a + G)) ^ (k + 1)
        ≤ a * (|H - H'| / (a + G)) ^ (k + 1) := by gcongr; exact min_le_right _ _
      _ ≤ |H - H'| ^ (k + 1) / (a + G) ^ k := by
          rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity),
            pow_succ (a + G) k]
          have hX : 0 ≤ |H - H'| ^ (k + 1) * (a + G) ^ k := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (show a ≤ a + G by linarith) hX]
      _ = (3 * C₀ + 3) ^ k * (|H - H'| ^ (k + 1) / ((3 * C₀ + 3) * (a + G)) ^ k) := by
          rw [mul_pow]; field_simp
      _ ≤ (3 * C₀ + 3) ^ k * (|H - H'| ^ (k + 1) / (H + H') ^ k) := by gcongr
      _ ≤ 2 * (3 * C₀ + 3) ^ k * (|H - H'| ^ (k + 1) / (H + H') ^ k) := by
          have : 0 ≤ (3 * C₀ + 3) ^ k * (|H - H'| ^ (k + 1) / (H + H') ^ k) := by positivity
          linarith
  · -- `|H - H'| > H' / 2`, `H + H' < 3 H' / 2` and `H' > a`, so the loss is at least
    -- `H' / (2 · 3^k) ≥ a / (2 · 3^k)`.
    push Not at hcase
    have hH'pos : 0 < H' := by linarith
    have hd : H' / 2 ≤ |H - H'| := by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    have hden : 0 < (H + H') ^ k := by positivity
    have hlow : H' / (2 * 3 ^ k) ≤ |H - H'| ^ (k + 1) / (H + H') ^ k := by
      rw [div_le_div_iff₀ (by positivity) hden]
      calc H' * (H + H') ^ k ≤ H' * (3 * (H' / 2)) ^ k := by gcongr; linarith
        _ = 2 * 3 ^ k * (H' / 2) ^ (k + 1) := by rw [mul_pow, pow_succ]; ring
        _ ≤ |H - H'| ^ (k + 1) * (2 * 3 ^ k) := by
            rw [mul_comm]; gcongr
    calc a * min 1 (|H - H'| / (a + G)) ^ (k + 1) ≤ a * 1 := by
          gcongr
          exact pow_le_one₀ hmin0 (min_le_left _ _)
      _ ≤ 2 * 3 ^ k * (H' / (2 * 3 ^ k)) := by field_simp; linarith
      _ ≤ 2 * (3 * C₀ + 3) ^ k * (|H - H'| ^ (k + 1) / (H + H') ^ k) := by
          gcongr

end Cslib
