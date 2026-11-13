/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACBayes.Basic
public import CslibFrontier.Probability.BinaryKL
import CslibFrontier.Probability.BernoulliComparison

/-!
# The PAC-Bayes-kl bound

The PAC-Bayes-kl bound, [Seeger2002, Theorem 1] for losses in `[0, 1]`; Seeger states it for
the zero-one loss and [Maurer2004, Lemma 3] extends it. Hypotheses are indexed by a
countable type `ι`, `ℓ i z ∈ [0, 1]` is the loss of the hypothesis `i` on the example `z`, and
`P` is a prior on `ι` fixed before the sample. Under `m ≥ 1` i.i.d. examples `S` from `D` and for
every `δ > 0`, with probability at least `1 - δ` every probability measure `Q` on `ι` with
`KL(Q ‖ P) < ∞` satisfies

`kl(𝔼_{i∼Q} L_S(i) ‖ 𝔼_{i∼Q} L_D(i)) ≤ (KL(Q ‖ P) + log ((m + 1) / δ)) / m`,

where `kl(q ‖ p)` is the binary relative entropy `Cslib.Probability.binaryKL q p`. The bound is
implicit in the true risk; inverting `kl` in its second argument bounds `𝔼_Q L_D`, and the
bound is tighter than McAllester's (`Cslib.MachineLearning.PACBayes.Basic`) when the empirical
risk is small.

The proof follows [Seeger2002, Appendix A] and [Maurer2004, Section 3]: the change-of-measure
inequality applied to
`f(i) = m kl(L_S(i) ‖ L_D(i))`, Jensen's inequality for `kl`
(`Cslib.Probability.binaryKL_integral_le_integral`), Maurer's exponential moment
`𝔼_S exp (m kl(L_S(i) ‖ L_D(i))) ≤ m + 1`
(`Cslib.Probability.lintegral_exp_mul_binaryKL_sum_div_le`) and Markov's inequality over the
prior (`Cslib.MachineLearning.PACBayes.measure_ofReal_div_le_lintegral_le`). The function `f` can
be unbounded under `Q`; its `Q`-integrability follows from the change of measure
(`Cslib.Probability.integrable_of_lintegral_exp_ne_top`). Jensen's inequality for `kl` needs
`L_S(i) = L_D(i)` whenever `L_D(i) ∈ {0, 1}`, where the true divergence is otherwise infinite;
this holds for every `i` on almost every sample.

Taking point-mass posteriors gives the Occam form: every hypothesis `i` with `P {i} > 0`
satisfies `kl(L_S(i) ‖ L_D(i)) ≤ (log (1 / P {i}) + log ((m + 1) / δ)) / m`.

Differences from the sources: the hypothesis space is countable with measurable singletons;
`δ < 1` is not needed; posteriors with infinite divergence are excluded; each `ℓ i` must be
measurable. [Maurer2004, Theorem 5] proves the sharper `log (2√m / δ)` for `m ≥ 8` from the
exponential moment bound `2√m` of its Theorem 1, which is not formalized here.

## Main results

* `measure_pi_exists_binaryKL_integral_risk_gt`: the PAC-Bayes-kl bound.
* `measure_pi_exists_binaryKL_risk_gt`: its Occam form for point-mass posteriors.

## References

* [A. Maurer, *A note on the PAC Bayesian theorem*][Maurer2004]
* [M. Seeger, *PAC-Bayesian generalisation error bounds for Gaussian process
  classification*][Seeger2002]
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Cslib.MachineLearning.PACBayes

open Cslib.Probability

variable {ι Z : Type*} [MeasurableSpace Z] {D : Measure Z} [IsProbabilityMeasure D]
  {ℓ : ι → Z → ℝ}

section Boundary

/-- A hypothesis with true risk `0` has empirical risk `0` on almost every sample. -/
private theorem ae_empiricalRisk_eq_zero {i : ι} (hℓ : Measurable (ℓ i))
    (hℓ01 : ∀ z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) (h : trueRisk ℓ D i = 0) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), empiricalRisk ℓ S i = 0 := by
  have hint : Integrable (ℓ i) D := Integrable.of_mem_Icc 0 1 hℓ.aemeasurable (ae_of_all _ hℓ01)
  rw [trueRisk_def] at h
  have h0 : ∀ᵐ z ∂D, ℓ i z = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => (hℓ01 z).1) hint).1 h
  have hS : ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), ∀ j, ℓ i (S j) = 0 :=
    ae_all_iff.2 fun j => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => D) (i := j)).eventually
      (p := fun z => ℓ i z = 0) h0
  filter_upwards [hS] with S hS
  simp [empiricalRisk_eq_sum_div, hS]

/-- A hypothesis with true risk `1` has empirical risk `1` on almost every nonempty sample. -/
private theorem ae_empiricalRisk_eq_one {i : ι} (hℓ : Measurable (ℓ i))
    (hℓ01 : ∀ z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (h : trueRisk ℓ D i = 1) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), empiricalRisk ℓ S i = 1 := by
  have hint : Integrable (ℓ i) D := Integrable.of_mem_Icc 0 1 hℓ.aemeasurable (ae_of_all _ hℓ01)
  rw [trueRisk_def] at h
  have h1 : ∀ᵐ z ∂D, 1 - ℓ i z = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sub_nonneg.2 (hℓ01 z).2)
      ((integrable_const 1).sub hint)).1 (by
        rw [integral_sub (integrable_const 1) hint, h]
        simp)
  have hS : ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), ∀ j, ℓ i (S j) = 1 :=
    ae_all_iff.2 fun j => ((Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => D)
      (i := j)).eventually (p := fun z => 1 - ℓ i z = 0) h1).mono fun S (hS : 1 - ℓ i (S j) = 0) =>
        by linarith
  filter_upwards [hS] with S hS
  simp [empiricalRisk_eq_sum_div, hS, hm.ne']

/-- On almost every nonempty sample, every hypothesis whose true risk is `0` or `1` has the same
empirical risk. -/
private theorem ae_forall_empiricalRisk_eq [Countable ι] (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), ∀ i,
      (trueRisk ℓ D i = 0 → empiricalRisk ℓ S i = 0) ∧
        (trueRisk ℓ D i = 1 → empiricalRisk ℓ S i = 1) := by
  refine ae_all_iff.2 fun i => ?_
  by_cases h0 : trueRisk ℓ D i = 0
  · filter_upwards [ae_empiricalRisk_eq_zero (hℓ i) (hℓ01 i) m h0] with S hS
    exact ⟨fun _ => hS, fun h1 => absurd (h0.symm.trans h1) zero_ne_one⟩
  by_cases h1 : trueRisk ℓ D i = 1
  · filter_upwards [ae_empiricalRisk_eq_one (hℓ i) (hℓ01 i) hm h1] with S hS
    exact ⟨fun h => absurd h h0, fun _ => hS⟩
  · exact ae_of_all _ fun S => ⟨fun h => absurd h h0, fun h => absurd h h1⟩

end Boundary

/-- Maurer's exponential moment for one hypothesis:
`𝔼_S exp (m kl(L_S(i) ‖ L_D(i))) ≤ m + 1`. -/
private theorem lintegral_exp_mul_binaryKL_risk_le {i : ι} (hℓ : Measurable (ℓ i))
    (hℓ01 : ∀ z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    ∫⁻ S, ENNReal.ofReal (Real.exp (m * binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i)))
      ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal (m + 1) := by
  have h := lintegral_exp_mul_binaryKL_sum_div_le (ι := Fin m) (μ := D) hℓ hℓ01
  simp only [Fintype.card_fin] at h
  simpa only [empiricalRisk_eq_sum_div, trueRisk_def] using h

section Bounds

variable [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

/-- **The PAC-Bayes-kl bound** [Seeger2002, Theorem 1] [Maurer2004]: for a prior `P` on a
countable index, losses `ℓ i z ∈ [0, 1]`, `m ≥ 1` and `δ > 0`, the samples on which some
posterior `Q` with `KL(Q ‖ P) < ∞` has
`(KL(Q ‖ P) + log ((m + 1) / δ)) / m < kl(𝔼_Q L_S ‖ 𝔼_Q L_D)` have probability at most `δ`. -/
theorem measure_pi_exists_binaryKL_integral_risk_gt (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ((klDiv Q P).toReal + Real.log ((m + 1) / δ)) / m <
        binaryKL (∫ i, empiricalRisk ℓ S i ∂Q) (∫ i, trueRisk ℓ D i ∂Q)} ≤
      ENNReal.ofReal δ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set F : (Fin m → Z) → ι → ℝ≥0∞ := fun S i =>
    ENNReal.ofReal (Real.exp (m * binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i)))
  have hF (i : ι) : Measurable fun S => F S i := by
    have := measurable_empiricalRisk (ℓ := ℓ) m (hℓ i)
    have hc := (continuous_binaryKL_left (trueRisk ℓ D i)).measurable
    exact (measurable_const.mul (hc.comp this)).exp.ennreal_ofReal
  have hmarkov := measure_ofReal_div_le_lintegral_le (Measure.pi fun _ : Fin m => D) P hF
    (fun i => lintegral_exp_mul_binaryKL_risk_le (hℓ i) (hℓ01 i) m) (by positivity) hδ
  refine le_trans (measure_mono_ae ?_) hmarkov
  filter_upwards [ae_forall_empiricalRisk_eq hℓ hℓ01 hm] with S hS hbad
  obtain ⟨Q, hQ, hQP, hlt⟩ := hbad
  by_contra hB
  rw [not_le] at hB
  set f : ι → ℝ := fun i => m * binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i)
  have hkl0 (i : ι) : 0 ≤ binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i) :=
    binaryKL_nonneg (empiricalRisk_mem_Icc ℓ S (hℓ01 i)) (trueRisk_mem_Icc ℓ D (hℓ01 i))
  have hf0 (i : ι) : 0 ≤ f i := mul_nonneg hmR.le (hkl0 i)
  have hfQ : Integrable f Q :=
    integrable_of_lintegral_exp_ne_top hQP (measurable_of_countable f) hf0
      (hB.trans ENNReal.ofReal_lt_top).ne
  have hexpP : Integrable (fun i => Real.exp (f i)) P :=
    ⟨(measurable_of_countable _).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun i => (Real.exp_pos _).le)).2 (hB.trans ENNReal.ofReal_lt_top)⟩
  -- Change of measure: `𝔼_Q f ≤ KL(Q ‖ P) + log 𝔼_P exp f < KL(Q ‖ P) + log ((m + 1) / δ)`.
  have hcm := integral_le_toReal_klDiv_add_log_integral_exp hQP hfQ hexpP
  have hpos : 0 < ∫ i, Real.exp (f i) ∂P := integral_exp_pos hexpP
  rw [← ofReal_integral_eq_lintegral_ofReal hexpP (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos.le] at hB
  have hlog := Real.log_lt_log hpos hB
  -- Jensen: `kl(𝔼_Q L_S ‖ 𝔼_Q L_D) ≤ 𝔼_Q kl(L_S ‖ L_D) = 𝔼_Q f / m`.
  have hklQ : Integrable (fun i => binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i)) Q := by
    simpa [f, ← mul_assoc, inv_mul_cancel₀ hmR.ne'] using hfQ.const_mul (m : ℝ)⁻¹
  have hj := binaryKL_integral_le_integral (μ := Q) (fun i => empiricalRisk_mem_Icc ℓ S (hℓ01 i))
    (fun i => trueRisk_mem_Icc ℓ D (hℓ01 i)) (fun i => (hS i).1) (fun i => (hS i).2)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable hklQ
  have hfint : ∫ i, f i ∂Q = m * ∫ i, binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i) ∂Q :=
    integral_const_mul _ _
  rw [div_lt_iff₀ hmR] at hlt
  nlinarith

/-- **The Occam form of the PAC-Bayes-kl bound**: taking point-mass posteriors, with probability at
least `1 - δ` every index `i` with `P {i} > 0` satisfies
`kl(L_S(i) ‖ L_D(i)) ≤ (log (1 / P {i}) + log ((m + 1) / δ)) / m`. -/
theorem measure_pi_exists_binaryKL_risk_gt (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ i, P {i} ≠ 0 ∧
      (Real.log (1 / P.real {i}) + Real.log ((m + 1) / δ)) / m <
        binaryKL (empiricalRisk ℓ S i) (trueRisk ℓ D i)} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_exists_binaryKL_integral_risk_gt hℓ hℓ01 hm P hδ)
  obtain ⟨i, hi, hlt⟩ := hS
  refine ⟨Measure.dirac i, inferInstance, klDiv_dirac_ne_top hi, ?_⟩
  rwa [integral_dirac, integral_dirac, toReal_klDiv_dirac hi, ← Real.log_inv, ← one_div]

end Bounds

end Cslib.MachineLearning.PACBayes
