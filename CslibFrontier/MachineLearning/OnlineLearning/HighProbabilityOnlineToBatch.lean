/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.AzumaPi
public import CslibFrontier.MachineLearning.LossMinimization.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod

/-!
# High-probability online-to-batch conversion

Run an online learner on an i.i.d. sample `S = (z₀, …, z_{T-1})` from `D`. In round `t` it
commits to a loss function `f t S` that depends only on the examples before round `t`, and then
suffers the online loss `f t S (S t)`. If every `f t S` takes values in `[a, b]`, then with
probability at least `1 - δ`

  `(1 / T) ∑ t, ∫ f t S dD ≤ (1 / T) ∑ t, f t S (S t) + (b - a) √(ln (1 / δ) / (2 T))`

(`measureReal_average_integral_gt_le`). The differences `∫ f t S dD - f t S (S t)` are martingale
differences of the natural filtration of the sample, and Hoeffding's lemma bounds each of them on
an interval of length `b - a`. The Azuma–Hoeffding inequality under a product measure
(`ProbabilityTheory.measure_sum_ge_le_pi`) then bounds their sum. This is the conversion of
[CesaBianchiConconiGentile2004] for bounded losses; there the loss range is `[0, 1]` and the
deviation term comes from Azuma's inequality (locator and constant unverified).

For the iterates `w t S` of an online learner and a loss `ℓ` with values in `[a, b]`, the
average true risk `(1 / T) ∑ t, L_D (w t S)` is at most the average online loss plus the same
deviation term (`measureReal_average_trueRisk_gt_le`). For convex losses, Jensen's inequality
turns a regret bound into a bound on the true risk of the average iterate
(`measureReal_trueRisk_average_gt_le`). If the regret against `u ∈ K` is at most `R` on every
sample and `|ℓ w z - ℓ u z| ≤ c` for `w ∈ K`, then with probability at least `1 - δ`

  `L_D ((1 / T) ∑ t, w t S) ≤ L_D u + R / T + c √(2 ln (1 / δ) / T)`.

The in-expectation conversion uses only that `w t S` does not depend on `S t`. Here `f t S`
must not depend on any of the examples `S t, S (t + 1), …`, so that the differences form a
martingale. The faster rates for strongly convex losses and running time are not treated here.

## Main results

* `Cslib.MachineLearning.OnlineLearning.hasSubgaussianMGF_sum_integral_sub`: the sum of the
  differences between expected and online losses is sub-Gaussian.
* `Cslib.MachineLearning.OnlineLearning.measureReal_sum_integral_gt_le`,
  `Cslib.MachineLearning.OnlineLearning.measureReal_average_integral_gt_le`: the high-probability
  conversion in sum and average form.
* `Cslib.MachineLearning.OnlineLearning.measureReal_average_trueRisk_gt_le`: the form for the
  true risks of the iterates of an online learner.
* `Cslib.MachineLearning.OnlineLearning.measureReal_trueRisk_average_gt_le`: the bound for the
  average iterate under a convex loss and a regret bound.

## References

* [N. Cesa-Bianchi, A. Conconi, C. Gentile, *On the generalization ability of on-line learning
  algorithms*][CesaBianchiConconiGentile2004]
* [K. Azuma, *Weighted sums of certain dependent random variables*][Azuma1967]
-/

public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

namespace Cslib.MachineLearning.OnlineLearning

variable {Z : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D] {T : ℕ}

/-- If `f t S` depends only on the examples before round `t` and takes values in `[a, b]`, the sum
of the differences `∫ f t S dD - f t S (S t)` between expected and online losses has a
sub-Gaussian moment generating function with parameter `T ((b - a) / 2) ^ 2`. -/
theorem hasSubgaussianMGF_sum_integral_sub {f : Fin T → (Fin T → Z) → Z → ℝ}
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, f t (Function.update S s z) = f t S)
    {a b : ℝ} (hab : ∀ t S z, f t S z ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun S => ∑ t, (∫ z, f t S z ∂D - f t S (S t)))
      (T * (‖b - a‖₊ / 2) ^ 2) (Measure.pi fun _ => D) := by
  have hint : ∀ t S, Integrable (f t S) D := fun t S =>
    Integrable.of_mem_Icc a b ((hf t).comp (measurable_const.prodMk measurable_id)).aemeasurable
      (Filter.Eventually.of_forall (hab t S))
  have h := hasSubgaussianMGF_sum_pi (μ := fun _ => D)
    (Y := fun t S => ∫ z, f t S z ∂D - f t S (S t)) (c := fun _ => ‖b - a‖₊)
    (fun t => (hf t).stronglyMeasurable.integral_prod_right'.measurable.sub
      ((hf t).comp (measurable_id.prodMk (measurable_pi_apply t))))
    (fun t s hts S z => by
      simp only [hfresh t s hts.le, Function.update_of_ne hts.ne])
    (fun t S => by
      simp only [hfresh t t le_rfl, Function.update_self]
      rw [integral_sub (integrable_const _) (hint t S)]
      simp)
    (fun t S => ⟨∫ z, f t S z ∂D - b, fun z => by
      simp only [hfresh t t le_rfl, Function.update_self, coe_nnnorm, Real.norm_eq_abs]
      constructor
      · linarith [(hab t S z).2]
      · linarith [(hab t S z).1, le_abs_self (b - a)]⟩)
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- **High-probability online-to-batch conversion, sum form.** If `f t S` depends only on the
examples before round `t` and takes values in `[a, b]`, then for `δ ∈ (0, 1]`, with probability at
least `1 - δ`, `∑ t, ∫ f t S dD ≤ ∑ t, f t S (S t) + (b - a) √(T ln (1 / δ) / 2)`. -/
theorem measureReal_sum_integral_gt_le {f : Fin T → (Fin T → Z) → Z → ℝ}
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, f t (Function.update S s z) = f t S)
    {a b : ℝ} (hab : ∀ t S z, f t S z ∈ Set.Icc a b) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ => D).real {S | ∑ t, f t S (S t) + (b - a) * √(T * log (1 / δ) / 2) <
      ∑ t, ∫ z, f t S z ∂D} ≤ δ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [hδ.le]
  have hle : a ≤ b := by
    obtain ⟨z⟩ := nonempty_of_isProbabilityMeasure D
    obtain ⟨S⟩ := nonempty_of_isProbabilityMeasure (Measure.pi fun _ : Fin T => D)
    exact (hab ⟨0, hT⟩ S z).1.trans (hab ⟨0, hT⟩ S z).2
  refine le_trans (measureReal_mono fun S hS => ?_)
    ((hasSubgaussianMGF_sum_integral_sub hf hfresh hab).measure_sqrt_lt_le hδ hδ1)
  have hsq : √(2 * ((T * (‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * log (1 / δ)) =
      (b - a) * √(T * log (1 / δ) / 2) := by
    rw [show (b - a) * √(T * log (1 / δ) / 2) = √((b - a) ^ 2 * (T * log (1 / δ) / 2)) by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq (sub_nonneg.2 hle)]]
    congr 1
    push_cast
    simp only [Real.norm_of_nonneg (sub_nonneg.2 hle)]
    ring
  simp only [Set.mem_ofPred_eq, hsq, Finset.sum_sub_distrib] at hS ⊢
  linarith

/-- **High-probability online-to-batch conversion.** If `f t S` depends only on the examples
before round `t` and takes values in `[a, b]`, then for `δ ∈ (0, 1]`, with probability at least
`1 - δ`, the average expected loss `(1 / T) ∑ t, ∫ f t S dD` is at most the average online loss
`(1 / T) ∑ t, f t S (S t)` plus `(b - a) √(ln (1 / δ) / (2 T))`. -/
theorem measureReal_average_integral_gt_le {f : Fin T → (Fin T → Z) → Z → ℝ}
    (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, f t (Function.update S s z) = f t S)
    {a b : ℝ} (hab : ∀ t S z, f t S z ∈ Set.Icc a b) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ => D).real {S | (T : ℝ)⁻¹ * ∑ t, f t S (S t) +
      (b - a) * √(log (1 / δ) / (2 * T)) < (T : ℝ)⁻¹ * ∑ t, ∫ z, f t S z ∂D} ≤ δ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [hδ.le]
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  refine le_trans (measureReal_mono fun S hS => ?_)
    (measureReal_sum_integral_gt_le hf hfresh hab hδ hδ1)
  have hsq : (T : ℝ) * √(log (1 / δ) / (2 * T)) = √(T * log (1 / δ) / 2) := by
    rw [show (T : ℝ) * log (1 / δ) / 2 = (T : ℝ) ^ 2 * (log (1 / δ) / (2 * T)) by
      field_simp, sqrt_mul (sq_nonneg _), sqrt_sq hTr.le]
  have hcancel : ∀ x : ℝ, (T : ℝ) * ((T : ℝ)⁻¹ * x) = x := fun x => by
    rw [← mul_assoc, mul_inv_cancel₀ hTr.ne', one_mul]
  simp only [Set.mem_ofPred_eq] at hS ⊢
  have h := mul_lt_mul_of_pos_left hS hTr
  rw [mul_add, hcancel, hcancel, mul_left_comm (T : ℝ) (b - a), hsq] at h
  exact h

/-- **High-probability online-to-batch conversion for the iterates of an online learner.** If the
iterate `w t S` depends only on the examples before round `t` and the loss `ℓ` takes values in
`[a, b]`, then for `δ ∈ (0, 1]`, with probability at least `1 - δ`, the average true risk
`(1 / T) ∑ t, L_D (w t S)` is at most the average online loss `(1 / T) ∑ t, ℓ (w t S) (S t)` plus
`(b - a) √(ln (1 / δ) / (2 T))`. -/
theorem measureReal_average_trueRisk_gt_le {W : Type*} [MeasurableSpace W] {ℓ : W → Z → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) {w : Fin T → (Fin T → Z) → W}
    (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, w t (Function.update S s z) = w t S)
    {a b : ℝ} (hab : ∀ t S z, ℓ (w t S) z ∈ Set.Icc a b) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ => D).real {S | (T : ℝ)⁻¹ * ∑ t, ℓ (w t S) (S t) +
      (b - a) * √(log (1 / δ) / (2 * T)) < (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S)} ≤ δ := by
  simp only [trueRisk_def]
  exact measureReal_average_integral_gt_le (f := fun t S z => ℓ (w t S) z)
    (fun t => hℓ.comp (((hwm t).comp measurable_fst).prodMk measurable_snd))
    (fun t s hts S z => by simp only [hfresh t s hts]) hab hδ hδ1

/-- **High-probability online-to-batch conversion for convex losses.** Let `ℓ · z` be convex on a
convex set `K`, let `u ∈ K` with `ℓ u` integrable, and let `|ℓ w z - ℓ u z| ≤ c` for `w ∈ K`. If
the iterates `w t S ∈ K` depend only on the examples before round `t` and their regret against `u`
is at most `R` on every sample, then for `δ ∈ (0, 1]`, with probability at least `1 - δ`, the
average iterate has true risk at most `L_D u + R / T + c √(2 ln (1 / δ) / T)`. -/
theorem measureReal_trueRisk_average_gt_le (hT : 0 < T) {E : Type*} [AddCommGroup E]
    [Module ℝ E] [MeasurableSpace E] {K : Set E} (hK : Convex ℝ K) {ℓ : E → Z → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) (hconv : ∀ z, ConvexOn ℝ K fun w => ℓ w z)
    {u : E} (hui : Integrable (ℓ u) D) {c : ℝ}
    (hc : ∀ w ∈ K, ∀ z, |ℓ w z - ℓ u z| ≤ c) {w : Fin T → (Fin T → Z) → E}
    (hwK : ∀ t S, w t S ∈ K) (hwm : ∀ t, Measurable (w t))
    (hfresh : ∀ t s, t ≤ s → ∀ S z, w t (Function.update S s z) = w t S) {R : ℝ}
    (hR : ∀ S, ∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ => D).real {S | trueRisk ℓ D u + R / T + c * √(2 * log (1 / δ) / T) <
      trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S)} ≤ δ := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hint : ∀ v ∈ K, Integrable (ℓ v) D := fun v hv =>
    (hui.norm.add (integrable_const c)).mono'
      (hℓ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        have h1 := hc v hv z
        have h2 := abs_sub_abs_le_abs_sub (ℓ v z) (ℓ u z)
        simp only [Real.norm_eq_abs, Pi.add_apply]
        linarith)
  have hgen := measureReal_average_integral_gt_le (D := D)
    (f := fun t S z => ℓ (w t S) z - ℓ u z)
    (fun t => (hℓ.comp (((hwm t).comp measurable_fst).prodMk measurable_snd)).sub
      (hℓ.comp (measurable_const.prodMk measurable_snd)))
    (fun t s hts S z => by simp only [hfresh t s hts])
    (a := -c) (b := c) (fun t S z => abs_le.1 (hc _ (hwK t S) z)) hδ hδ1
  refine le_trans (measureReal_mono fun S hS => ?_) hgen
  have hjensen : trueRisk ℓ D ((T : ℝ)⁻¹ • ∑ t, w t S) ≤
      (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) := by
    have h := (convexOn_trueRisk hK hconv hint).map_sum_le (t := Finset.univ)
      (w := fun _ => (T : ℝ)⁻¹) (p := fun t => w t S) (fun _ _ => inv_nonneg.2 hTr.le)
      (by simp [hTr.ne']) (fun t _ => hwK t S)
    simpa [Finset.smul_sum, Finset.mul_sum] using h
  have hrisk : ∑ t, ∫ z, (ℓ (w t S) z - ℓ u z) ∂D =
      ∑ t, trueRisk ℓ D (w t S) - T * trueRisk ℓ D u := by
    simp only [trueRisk_def]
    rw [Finset.sum_congr rfl fun t _ => integral_sub (hint _ (hwK t S)) hui,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have honline : (T : ℝ)⁻¹ * ∑ t, (ℓ (w t S) (S t) - ℓ u (S t)) ≤ R / T := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hR S) (inv_nonneg.2 hTr.le)
  have hsplit : (T : ℝ)⁻¹ * (∑ t, trueRisk ℓ D (w t S) - T * trueRisk ℓ D u) =
      (T : ℝ)⁻¹ * ∑ t, trueRisk ℓ D (w t S) - trueRisk ℓ D u := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hTr.ne', one_mul]
  have hsqrt : (c - -c) * √(log (1 / δ) / (2 * T)) = c * √(2 * log (1 / δ) / T) := by
    rw [show 2 * log (1 / δ) / T = (2 : ℝ) ^ 2 * (log (1 / δ) / (2 * T)) by field_simp,
      sqrt_mul (sq_nonneg _), sqrt_sq zero_le_two]
    ring
  simp only [Set.mem_ofPred_eq] at hS ⊢
  rw [hrisk, hsplit, hsqrt]
  linarith

end Cslib.MachineLearning.OnlineLearning
