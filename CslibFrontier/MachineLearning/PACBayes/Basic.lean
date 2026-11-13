/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.LossMinimization.Basic
public import CslibFrontier.Probability.ChangeOfMeasure
import CslibFrontier.Probability.SubGaussian
import Mathlib.Probability.Moments.Variance

/-!
# PAC-Bayes bounds for countable hypothesis spaces

A prior `P` over hypotheses, fixed before the sample, controls the generalization gap of every
posterior `Q` at once, through the Kullback–Leibler divergence `KL(Q ‖ P)` [McAllester1999].
Hypotheses are indexed by a countable type `ι`, and `ℓ i z ∈ [0, 1]` is the loss of the
hypothesis `i` on the example `z`; the true and empirical risks are `L_D(i) = trueRisk ℓ D i` and
`L_S(i) = empiricalRisk ℓ S i` (`Cslib.MachineLearning.trueRisk`,
`Cslib.MachineLearning.empiricalRisk`). Under `m ≥ 2` i.i.d. examples `S` from `D` and for every
`δ > 0`, with probability at least `1 - δ` every probability measure `Q` on `ι` with
`KL(Q ‖ P) < ∞` satisfies

`𝔼_{i∼Q} L_D(i) ≤ 𝔼_{i∼Q} L_S(i) + √((KL(Q ‖ P) + log (m / δ)) / (2 (m - 1)))`,

which is [ShalevShwartzBenDavid2014, Theorem 31.1] with the source's constants. Each bound is
stated, as in the rest of the library, as an upper bound `δ` on the measure of the samples on
which some posterior violates it. The posterior is quantified inside that event, so it may depend
on the sample. The proof follows the source: the change-of-measure inequality
(`Cslib.Probability.integral_le_toReal_klDiv_add_log_integral_exp`) and Jensen's inequality bound
`2 (m - 1) (𝔼_Q Δ)² - KL(Q ‖ P)` by `log 𝔼_P exp (2 (m - 1) Δ²)` for the gap
`Δ(i) = L_D(i) - L_S(i)`; because `P` does not depend on the sample, Tonelli's theorem and the
one-hypothesis exponential moment bound the sample average of the right side; Markov's inequality
finishes. The exponential moment comes from Hoeffding's lemma
(`Cslib.Probability.hasSubgaussianMGF_integral_sub_sum_div`) and is at most `√m`, sharper than the
source's `m` (its Exercise 31.1), so `measure_pi_exists_integral_risk_gt` proves the bound with
`log (√m / δ)` and `measure_pi_exists_integral_risk_gt_log_div` derives the source's form.

Taking point-mass posteriors gives the Occam bound of [ShalevShwartzBenDavid2014, Exercise 31.2]:
every hypothesis `i` with `P {i} > 0` satisfies
`L_D(i) ≤ L_S(i) + √((log (1 / P {i}) + log (m / δ)) / (2 (m - 1)))`, using
`KL(δ_i ‖ P) = log (1 / P {i})` (`Cslib.Probability.toReal_klDiv_dirac`). For the uniform prior
on a finite class this is the bound with `log |H|` of the exercise.

Differences from the source: the hypothesis space is countable with measurable singletons (the
source also allows densities); `δ < 1` is not needed; posteriors with infinite divergence are
excluded, for which the source's bound is vacuous; each `ℓ i` must be measurable. The divergence
is Mathlib's `klDiv`, in nats as in the source.

## Main results

* `measure_pi_exists_integral_risk_gt`: McAllester's bound with `log (√m / δ)`.
* `measure_pi_exists_integral_risk_gt_log_div`: McAllester's bound with the source's
  `log (m / δ)`.
* `measure_pi_exists_risk_gt`: the Occam bound for point-mass posteriors.

## References

* [D. A. McAllester, *PAC-Bayesian model averaging*][McAllester1999]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Cslib.MachineLearning.PACBayes

variable {ι Z : Type*} [MeasurableSpace Z]

private theorem measurable_empiricalRisk {ℓ : ι → Z → ℝ} (hℓ : ∀ i, Measurable (ℓ i)) (m : ℕ)
    (i : ι) : Measurable fun S : Fin m → Z => empiricalRisk ℓ S i := by
  simp only [empiricalRisk_eq_sum_div]
  exact (Finset.measurable_sum _ fun k _ => (hℓ i).comp (measurable_pi_apply k)).div_const _

section ChangeOfMeasure

variable [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

/-- Change of measure for a squared deviation: for `g` bounded by `C` on a countable index,
`λ > 0` and `𝔼_P exp (λ g²) ≤ B`, `∫ g ∂Q ≤ √((KL(Q ‖ P) + log B) / λ)`
[ShalevShwartzBenDavid2014, (31.2) and (31.6)]. -/
private theorem integral_le_sqrt_klDiv_add_log {P Q : Measure ι} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hQP : klDiv Q P ≠ ⊤) {g : ι → ℝ} {C : ℝ} (hg : ∀ i, |g i| ≤ C)
    {lam : ℝ} (hlam : 0 < lam) {B : ℝ}
    (hB : ∫⁻ i, ENNReal.ofReal (Real.exp (lam * g i ^ 2)) ∂P ≤ ENNReal.ofReal B) :
    ∫ i, g i ∂Q ≤ Real.sqrt (((klDiv Q P).toReal + Real.log B) / lam) := by
  have hsq (i : ι) : lam * g i ^ 2 ≤ lam * C ^ 2 := by
    rw [← sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hg i) 2) hlam.le
  have hfQ : Integrable (fun i => lam * g i ^ 2) Q :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (lam * C ^ 2)
      (ae_of_all _ fun i => by rw [Real.norm_of_nonneg (by positivity)]; exact hsq i)
  have hexpP : Integrable (fun i => Real.exp (lam * g i ^ 2)) P :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Real.exp (lam * C ^ 2))
      (ae_of_all _ fun i => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.2 (hsq i))
  -- Change of measure: `λ 𝔼_Q g² ≤ KL(Q ‖ P) + log 𝔼_P exp (λ g²) ≤ KL(Q ‖ P) + log B`.
  have hcm := Probability.integral_le_toReal_klDiv_add_log_integral_exp hQP hfQ hexpP
  rw [integral_const_mul] at hcm
  have hpos : 0 < ∫ i, Real.exp (lam * g i ^ 2) ∂P := integral_exp_pos hexpP
  rw [← ofReal_integral_eq_lintegral_ofReal hexpP (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ENNReal.ofReal_le_ofReal_iff'] at hB
  have hlog := Real.log_le_log hpos (hB.resolve_right (not_le.2 hpos))
  -- Jensen: `(𝔼_Q g)² ≤ 𝔼_Q g²`, since the variance is nonnegative.
  have hmem : MemLp g 2 Q :=
    MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (ae_of_all _ fun i => by rw [Real.norm_eq_abs]; exact hg i)
  have hjensen : (∫ i, g i ∂Q) ^ 2 ≤ ∫ i, g i ^ 2 ∂Q := by
    have := variance_nonneg g Q
    rw [variance_eq_sub hmem] at this
    simpa only [Pi.pow_apply, sub_nonneg] using this
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [le_div_iff₀ hlam]
  nlinarith

end ChangeOfMeasure

section ExponentialMoment

variable (D : Measure Z) [IsProbabilityMeasure D] {ℓ : ι → Z → ℝ}

/-- The exponential moment of one hypothesis: `𝔼_S exp (2 (m - 1) (L_D(h) - L_S(h))²) ≤ √m`.
[ShalevShwartzBenDavid2014, Section 31.1] uses the weaker bound `m`. -/
private theorem lintegral_exp_sq_risk_sub_le (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (i : ι) :
    ∫⁻ S, ENNReal.ofReal (Real.exp (2 * (m - 1) * (trueRisk ℓ D i - empiricalRisk ℓ S i) ^ 2))
        ∂Measure.pi (fun _ : Fin m => D) ≤ ENNReal.ofReal (Real.sqrt m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
  have hc : (((4 * m : NNReal)⁻¹ : NNReal) : ℝ) = (4 * (m : ℝ))⁻¹ := by push_cast; ring
  have key : 1 - 2 * (2 * ((m : ℝ) - 1)) * (4 * (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by field_simp; ring
  have h := (Probability.hasSubgaussianMGF_integral_sub_sum_div D (hℓ i) (hℓ01 i)
    hm).lintegral_exp_mul_sq_le (s := 2 * (m - 1)) (by linarith) (by
      rw [hc]; have := inv_pos.2 hmR; linarith)
  simp only [trueRisk_def, empiricalRisk_eq_sum_div]
  refine h.trans_eq ?_
  rw [hc, key, Real.sqrt_inv, inv_inv]

variable [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

/-- Markov's inequality for the prior-averaged exponential moment: since `P` does not depend on
the sample, `𝔼_S 𝔼_{h∼P} exp (2 (m - 1) Δ(h)²) ≤ √m`, so the average reaches `√m / δ` with
probability at most `δ` [ShalevShwartzBenDavid2014, (31.4)–(31.5)]. -/
private theorem measure_le_lintegral_exp_sq_risk_sub (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 0 < m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal (Real.sqrt m / δ) ≤
      ∫⁻ i, ENNReal.ofReal (Real.exp (2 * (m - 1) * (trueRisk ℓ D i - empiricalRisk ℓ S i) ^ 2))
        ∂P} ≤ ENNReal.ofReal δ := by
  set F : (Fin m → Z) → ι → ℝ≥0∞ := fun S i =>
    ENNReal.ofReal (Real.exp (2 * (m - 1) * (trueRisk ℓ D i - empiricalRisk ℓ S i) ^ 2))
  have hFm : Measurable (Function.uncurry F) :=
    measurable_from_prod_countable_left fun i => by
      have := measurable_empiricalRisk hℓ m i
      simp only [Function.uncurry_apply_pair, F]
      fun_prop
  have hswap : ∫⁻ S, ∫⁻ i, F S i ∂P ∂Measure.pi (fun _ : Fin m => D) ≤
      ENNReal.ofReal (Real.sqrt m) := by
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    calc ∫⁻ i, ∫⁻ S, F S i ∂Measure.pi (fun _ : Fin m => D) ∂P
        ≤ ∫⁻ _, ENNReal.ofReal (Real.sqrt m) ∂P :=
          lintegral_mono fun i => lintegral_exp_sq_risk_sub_le D hℓ hℓ01 hm i
      _ = ENNReal.ofReal (Real.sqrt m) := by simp
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have hthr : ENNReal.ofReal (Real.sqrt m / δ) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos hsqrt hδ
  refine (meas_ge_le_lintegral_div hFm.lintegral_prod_right.aemeasurable hthr
    ENNReal.ofReal_ne_top).trans ?_
  refine (ENNReal.div_le_div_right hswap _).trans_eq ?_
  rw [← ENNReal.ofReal_div_of_pos (div_pos hsqrt hδ)]
  congr 1
  field_simp

end ExponentialMoment

section Bounds

variable {D : Measure Z} [IsProbabilityMeasure D] {ℓ : ι → Z → ℝ}

private theorem risk_mem_Icc (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) (i : ι) : trueRisk ℓ D i ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (ℓ i) D :=
    Integrable.of_mem_Icc 0 1 (hℓ i).aemeasurable (ae_of_all _ (hℓ01 i))
  rw [trueRisk_def]
  refine ⟨integral_nonneg fun z => (hℓ01 i z).1, ?_⟩
  calc ∫ z, ℓ i z ∂D ≤ ∫ _, (1 : ℝ) ∂D :=
        integral_mono hint (integrable_const 1) fun z => (hℓ01 i z).2
    _ = 1 := by simp

omit [MeasurableSpace Z] [IsProbabilityMeasure D] in
private theorem empiricalRisk_mem_Icc (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ}
    (S : Fin m → Z) (i : ι) : empiricalRisk ℓ S i ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalRisk_eq_sum_div]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rw [empiricalRisk_eq_sum_div]
  refine ⟨div_nonneg (Finset.sum_nonneg fun k _ => (hℓ01 i (S k)).1) hmR.le, ?_⟩
  rw [div_le_one hmR]
  calc ∑ k, ℓ i (S k) ≤ ∑ _k : Fin m, (1 : ℝ) := Finset.sum_le_sum fun k _ => (hℓ01 i (S k)).2
    _ = m := by simp

variable [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]

/-- **McAllester's PAC-Bayes bound** [McAllester1999], with `log (√m / δ)`: for a prior `P`
on a countable index, losses `ℓ i z ∈ [0, 1]`, `m ≥ 2` and `δ > 0`, the samples on which some
posterior `Q` with `KL(Q ‖ P) < ∞` has
`𝔼_Q L_S + √((KL(Q ‖ P) + log (√m / δ)) / (2 (m - 1))) < 𝔼_Q L_D` have probability at most `δ`.
-/
theorem measure_pi_exists_integral_risk_gt (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 2 ≤ m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q +
        Real.sqrt (((klDiv Q P).toReal + Real.log (Real.sqrt m / δ)) / (2 * (m - 1))) <
      ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_le_lintegral_exp_sq_risk_sub D hℓ hℓ01 (by omega) P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  by_contra hB
  rw [Set.mem_ofPred_eq, not_le] at hB
  have hlam : (0 : ℝ) < 2 * (m - 1) := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hg (i : ι) : |trueRisk ℓ D i - empiricalRisk ℓ S i| ≤ 1 := by
    have h1 := risk_mem_Icc (D := D) hℓ hℓ01 i
    have h2 := empiricalRisk_mem_Icc hℓ01 S i
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hbound := integral_le_sqrt_klDiv_add_log hQP hg hlam hB.le
  have hintR : Integrable (fun i => trueRisk ℓ D i) Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun i => risk_mem_Icc hℓ hℓ01 i)
  have hintE : Integrable (fun i => empiricalRisk ℓ S i) Q :=
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun i => empiricalRisk_mem_Icc hℓ01 S i)
  rw [integral_sub hintR hintE] at hbound
  linarith

/-- **McAllester's PAC-Bayes bound** with the constants of [ShalevShwartzBenDavid2014,
Theorem 31.1]: `log (m / δ)`. -/
theorem measure_pi_exists_integral_risk_gt_log_div (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 2 ≤ m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ Q : Measure ι, IsProbabilityMeasure Q ∧
      klDiv Q P ≠ ⊤ ∧ ∫ i, empiricalRisk ℓ S i ∂Q +
        Real.sqrt (((klDiv Q P).toReal + Real.log (m / δ)) / (2 * (m - 1))) <
      ∫ i, trueRisk ℓ D i ∂Q} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans (measure_pi_exists_integral_risk_gt hℓ hℓ01 hm P hδ)
  obtain ⟨Q, hQ, hQP, hlt⟩ := hS
  refine ⟨Q, hQ, hQP, lt_of_le_of_lt ?_ hlt⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsqrt : Real.sqrt m ≤ m := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hlog : Real.log (Real.sqrt m / δ) ≤ Real.log (m / δ) :=
    Real.log_le_log (div_pos (Real.sqrt_pos.2 (by linarith)) hδ)
      (div_le_div_of_nonneg_right hsqrt hδ.le)
  have hlam : (0 : ℝ) ≤ 2 * (m - 1) := by linarith
  exact add_le_add le_rfl
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (add_le_add le_rfl hlog) hlam))

/-- **The Occam bound as a PAC-Bayes corollary** [ShalevShwartzBenDavid2014, Exercise 31.2]:
taking point-mass posteriors, with probability at least `1 - δ` every index `i` with `P {i} > 0`
satisfies `L_D(i) ≤ L_S(i) + √((log (1 / P {i}) + log (m / δ)) / (2 (m - 1)))`. -/
theorem measure_pi_exists_risk_gt (hℓ : ∀ i, Measurable (ℓ i))
    (hℓ01 : ∀ i z, ℓ i z ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 2 ≤ m) (P : Measure ι)
    [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D) {S | ∃ i, P {i} ≠ 0 ∧ empiricalRisk ℓ S i +
        Real.sqrt ((Real.log (1 / P.real {i}) + Real.log (m / δ)) / (2 * (m - 1))) <
      trueRisk ℓ D i} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_exists_integral_risk_gt_log_div hℓ hℓ01 hm P hδ)
  obtain ⟨i, hi, hlt⟩ := hS
  refine ⟨Measure.dirac i, inferInstance, Probability.klDiv_dirac_ne_top hi, ?_⟩
  rwa [integral_dirac, integral_dirac, Probability.toReal_klDiv_dirac hi, ← Real.log_inv,
    ← one_div]

end Bounds

end Cslib.MachineLearning.PACBayes
