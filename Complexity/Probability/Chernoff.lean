/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Moments.Basic
import Complexity.Foundations.Analysis.SpecialFunctions.ExpBounds
import Complexity.Probability.PMF.Event
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Multiplicative Chernoff bounds

Let `X = ∑ i, score i (outcome i)` be a sum of independent scores with values in `[0, 1]`, the
coordinates of `outcome` drawn from the product `Cslib.Probability.PMF.pi p`, and let `μ` bound
its mean `∑ i, ∑ a, p i a * score i a`. The multiplicative Chernoff bounds compare `X` with
multiples of `μ`; Mitzenmacher and Upfal prove them for sums of independent `0`/`1` trials with
`μ` the mean [Mitzenmacher and Upfal, Section 4.2][MitzenmacherUpfal2017], and the same proofs
apply to `[0, 1]`-valued scores and to a bound `μ` on the mean in the appropriate direction:

* if the mean is at most `μ`, then `X ≥ (1 + δ) μ` with probability at most
  `exp (μ (δ - (1 + δ) log (1 + δ)))`, hence at most `exp (-δ² μ / (2 + δ))`, and at most
  `exp (-δ² μ / 3)` when `δ ≤ 1`;
* if the mean is at least `μ`, then `X ≤ (1 - δ) μ` with probability at most `exp (-δ² μ / 2)`.

The proofs follow the moment generating function method: Mathlib's Chernoff bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf`, multiplicativity of the moment generating function
under independence, and the convexity estimate `exp (t s) ≤ 1 + s (exp t - 1)` for `s ∈ [0, 1]`
(`Cslib.Probability.PMF.mgf_pi_sum_le`). All client-facing statements are about ordinary PMF event
probabilities. For fair coins, counting bit strings whose weight deviates from half the length,
the additive Hoeffding bound `Cslib.BitString.card_filter_le_card_filter_sub_half_le` is already
stronger than the multiplicative forms, so no separate counting form is given here.

## Main results

* `Cslib.Probability.PMF.mgf_pi_sum_le`: the moment generating function of the sum is at most
  `exp (mean * (exp t - 1))`.
* `Cslib.Probability.PMF.pi_sum_ge_le_exp`, `Cslib.Probability.PMF.pi_sum_le_le_exp`: the
  Chernoff bound for every parameter `t`.
* `Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log`: the sharp multiplicative upper tail.
* `Cslib.Probability.PMF.pi_sum_ge_one_add_mul`,
  `Cslib.Probability.PMF.pi_sum_ge_one_add_mul_of_le_one`: the simplified upper tails.
* `Cslib.Probability.PMF.pi_sum_le_one_sub_mul`: the lower tail.
* `Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_mul`: the two-sided bound for `δ ≤ 1`.

## References

* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 4.2][MitzenmacherUpfal2017]
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Appendix A][AlonSpencer2016]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- For `s ∈ [0, 1]`, convexity of the exponential bounds `exp (t s)` by the chord
`1 + s (exp t - 1)`. -/
private theorem exp_mul_le_one_add_mul {s : ℝ} (hs : s ∈ Set.Icc 0 1) (t : ℝ) :
    Real.exp (t * s) ≤ 1 + s * (Real.exp t - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (sub_nonneg.mpr hs.2) hs.1
    (sub_add_cancel 1 s)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (t * s) = Real.exp (s * t) := by rw [mul_comm]
    _ ≤ 1 - s + s * Real.exp t := h
    _ = 1 + s * (Real.exp t - 1) := by ring

/-- Scores in `[0, 1]` on the support have a nonnegative mean. -/
private theorem mean_nonneg (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) :
    0 ≤ ∑ i, ∑ a, (p i a).toReal * score i a := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => ?_
  by_cases ha : a ∈ (p i).support
  · exact mul_nonneg ENNReal.toReal_nonneg (hscore i a ha).1
  · rw [PMF.apply_eq_zero_iff _ _ |>.mpr ha, ENNReal.toReal_zero, zero_mul]

/-- **The Chernoff moment bound**: the moment generating function of a sum of independent scores
in `[0, 1]` is at most `exp (mean * (exp t - 1))`. -/
theorem mgf_pi_sum_le [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) (t : ℝ) :
    mgf (fun outcome => ∑ i, score i (outcome i)) (pi p).toMeasure t ≤
      Real.exp ((∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp t - 1)) := by
  let μ := (pi p).toMeasure
  let X (i : ι) (outcome : ∀ i, α i) := score i (outcome i)
  have hindep : iIndepFun X μ :=
    (iIndepFun_pi p).comp score (fun _ => measurable_of_countable _)
  have hsum : (fun outcome => ∑ i, score i (outcome i)) = ∑ i, X i := by
    funext outcome
    simp only [Finset.sum_apply, X]
  have hcoord (i : ι) : mgf (X i) μ t = ∑ a, (p i a).toReal * Real.exp (t * score i a) := by
    have hmap := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable
      (f := fun a => Real.exp (t * score i a)) (measurable_of_countable _).aestronglyMeasurable
    change ∫ outcome, (fun a => Real.exp (t * score i a)) (outcome i) ∂μ = _
    rw [← hmap]
    simp only [μ, PMF.toMeasure_map _ _ (measurable_pi_apply i), pi_map_eval,
      PMF.integral_eq_sum, smul_eq_mul]
  have hle (i : ι) : mgf (X i) μ t ≤
      Real.exp ((∑ a, (p i a).toReal * score i a) * (Real.exp t - 1)) := by
    rw [hcoord]
    calc ∑ a, (p i a).toReal * Real.exp (t * score i a)
        ≤ ∑ a, (p i a).toReal * (1 + score i a * (Real.exp t - 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases ha : a ∈ (p i).support
          · exact mul_le_mul_of_nonneg_left (exp_mul_le_one_add_mul (hscore i a ha) t)
              ENNReal.toReal_nonneg
          · rw [PMF.apply_eq_zero_iff _ _ |>.mpr ha, ENNReal.toReal_zero, zero_mul, zero_mul]
      _ = 1 + (∑ a, (p i a).toReal * score i a) * (Real.exp t - 1) := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_toReal, Finset.sum_mul,
            mul_assoc]
      _ ≤ _ := by linarith [Real.add_one_le_exp ((∑ a, (p i a).toReal * score i a) *
            (Real.exp t - 1))]
  rw [hsum, hindep.mgf_sum (fun _ => measurable_of_countable _), Finset.sum_mul, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ => mgf_nonneg) (fun i _ => hle i)

/-- **The Chernoff bound** for the upper tail, with a free parameter `t ≥ 0`: a sum of
independent scores in `[0, 1]` is at least `ε` with probability at most
`exp (-t ε + mean * (exp t - 1))`. -/
theorem pi_sum_ge_le_exp (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ) :
    ((pi p).toOuterMeasure {outcome | ε ≤ ∑ i, score i (outcome i)}).toReal ≤
      Real.exp (-t * ε + (∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp t - 1)) := by
  let (i : ι) : MeasurableSpace (α i) := ⊤
  have h := measure_ge_le_exp_mul_mgf (μ := (pi p).toMeasure)
    (X := fun outcome => ∑ i, score i (outcome i)) ε ht Integrable.of_finite
  simp only [measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    ((Set.to_countable _).measurableSet)] at h
  rw [Real.exp_add]
  exact h.trans (mul_le_mul_of_nonneg_left (mgf_pi_sum_le p score hscore t) (Real.exp_pos _).le)

/-- **The Chernoff bound** for the lower tail, with a free parameter `t ≤ 0`: a sum of
independent scores in `[0, 1]` is at most `ε` with probability at most
`exp (-t ε + mean * (exp t - 1))`. -/
theorem pi_sum_le_le_exp (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {t : ℝ} (ht : t ≤ 0)
    (ε : ℝ) :
    ((pi p).toOuterMeasure {outcome | ∑ i, score i (outcome i) ≤ ε}).toReal ≤
      Real.exp (-t * ε + (∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp t - 1)) := by
  let (i : ι) : MeasurableSpace (α i) := ⊤
  have h := measure_le_le_exp_mul_mgf (μ := (pi p).toMeasure)
    (X := fun outcome => ∑ i, score i (outcome i)) ε ht Integrable.of_finite
  simp only [measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
    ((Set.to_countable _).measurableSet)] at h
  rw [Real.exp_add]
  exact h.trans (mul_le_mul_of_nonneg_left (mgf_pi_sum_le p score hscore t) (Real.exp_pos _).le)

/-- **The sharp multiplicative Chernoff bound** [Mitzenmacher and Upfal, Section 4.2]
[MitzenmacherUpfal2017]: if independent scores in `[0, 1]` have mean at most `μ`, their sum is at
least `(1 + δ) μ` with probability at most `exp (μ (δ - (1 + δ) log (1 + δ)))`, that is,
`(exp δ / (1 + δ) ^ (1 + δ)) ^ μ`, for every `δ ≥ 0`. -/
theorem pi_sum_ge_one_add_mul_le_exp_log (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ : ∑ i, ∑ a, (p i a).toReal * score i a ≤ μ) (hδ : 0 ≤ δ) :
    ((pi p).toOuterMeasure {outcome | (1 + δ) * μ ≤ ∑ i, score i (outcome i)}).toReal ≤
      Real.exp (μ * (δ - (1 + δ) * Real.log (1 + δ))) := by
  have hpos : 0 < 1 + δ := by linarith
  refine (pi_sum_ge_le_exp p score hscore
    (Real.log_nonneg (show (1 : ℝ) ≤ 1 + δ by linarith)) _).trans ?_
  rw [Real.exp_log hpos, add_sub_cancel_left]
  gcongr
  nlinarith

/-- **The multiplicative Chernoff bound**: if independent scores in `[0, 1]` have mean at most
`μ`, their sum is at least `(1 + δ) μ` with probability at most `exp (-δ² μ / (2 + δ))`, for every
`δ ≥ 0`. This follows from the sharp bound and `2 δ / (2 + δ) ≤ log (1 + δ)`. -/
theorem pi_sum_ge_one_add_mul (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ : ∑ i, ∑ a, (p i a).toReal * score i a ≤ μ) (hδ : 0 ≤ δ) :
    ((pi p).toOuterMeasure {outcome | (1 + δ) * μ ≤ ∑ i, score i (outcome i)}).toReal ≤
      Real.exp (-(δ ^ 2 * μ / (2 + δ))) := by
  refine (pi_sum_ge_one_add_mul_le_exp_log p score hscore hμ hδ).trans (Real.exp_le_exp.mpr ?_)
  have hμ0 : 0 ≤ μ := (mean_nonneg p score hscore).trans hμ
  have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ
  have h2 : (0 : ℝ) < 2 + δ := by linarith
  have hmul : μ * (δ - (1 + δ) * Real.log (1 + δ)) ≤ μ * (δ - (1 + δ) * (2 * δ / (δ + 2))) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hμ0
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The multiplicative Chernoff bound for `δ ≤ 1`** [Mitzenmacher and Upfal, Section 4.2]
[MitzenmacherUpfal2017]: if independent scores in `[0, 1]` have mean at most `μ`, their sum is at
least `(1 + δ) μ` with probability at most `exp (-δ² μ / 3)`, for `0 ≤ δ ≤ 1`. -/
theorem pi_sum_ge_one_add_mul_of_le_one (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ : ∑ i, ∑ a, (p i a).toReal * score i a ≤ μ) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ((pi p).toOuterMeasure {outcome | (1 + δ) * μ ≤ ∑ i, score i (outcome i)}).toReal ≤
      Real.exp (-(δ ^ 2 * μ / 3)) := by
  refine (pi_sum_ge_one_add_mul p score hscore hμ hδ).trans (Real.exp_le_exp.mpr ?_)
  have hμ0 : 0 ≤ μ := (mean_nonneg p score hscore).trans hμ
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- **The multiplicative Chernoff bound for the lower tail** [Mitzenmacher and Upfal,
Section 4.2][MitzenmacherUpfal2017]: if independent scores in `[0, 1]` have mean at least `μ`,
their sum is at most `(1 - δ) μ` with probability at most `exp (-δ² μ / 2)`, for every `δ ≥ 0`.
The proof takes the parameter `t = -δ` and uses `exp (-δ) ≤ 1 - δ + δ² / 2`. -/
theorem pi_sum_le_one_sub_mul (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {μ δ : ℝ}
    (hμ : μ ≤ ∑ i, ∑ a, (p i a).toReal * score i a) (hδ : 0 ≤ δ) :
    ((pi p).toOuterMeasure {outcome | ∑ i, score i (outcome i) ≤ (1 - δ) * μ}).toReal ≤
      Real.exp (-(δ ^ 2 * μ / 2)) := by
  rcases lt_or_ge μ 0 with hμ0 | hμ0
  · refine (ENNReal.toReal_le_of_le_ofReal zero_le_one ?_).trans
      (Real.one_le_exp (by nlinarith [sq_nonneg δ]))
    rw [ENNReal.ofReal_one]
    exact toOuterMeasure_le_one _ _
  refine (pi_sum_le_le_exp p score hscore (neg_nonpos.mpr hδ) _).trans (Real.exp_le_exp.mpr ?_)
  have hexp : Real.exp (-δ) - 1 ≤ 0 := by
    rw [sub_nonpos, Real.exp_le_one_iff]
    linarith
  have hmean : (∑ i, ∑ a, (p i a).toReal * score i a) * (Real.exp (-δ) - 1) ≤
      μ * (Real.exp (-δ) - 1) := mul_le_mul_of_nonpos_right hμ hexp
  nlinarith [mul_le_mul_of_nonneg_left (Real.exp_neg_le_one_sub_add_sq_div_two hδ) hμ0]

/-- **The two-sided multiplicative Chernoff bound** [Mitzenmacher and Upfal, Section 4.2]
[MitzenmacherUpfal2017]: a sum of independent scores in `[0, 1]` deviates from its mean by at
least `δ` times the mean with probability at most `2 exp (-δ² mean / 3)`, for `0 ≤ δ ≤ 1`. -/
theorem pi_sum_abs_sub_mean_ge_mul (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hscore : ∀ i a, a ∈ (p i).support → score i a ∈ Set.Icc 0 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ((pi p).toOuterMeasure {outcome | δ * ∑ i, ∑ a, (p i a).toReal * score i a ≤
      |∑ i, score i (outcome i) - ∑ i, ∑ a, (p i a).toReal * score i a|}).toReal ≤
        2 * Real.exp (-(δ ^ 2 * (∑ i, ∑ a, (p i a).toReal * score i a) / 3)) := by
  set mean := ∑ i, ∑ a, (p i a).toReal * score i a
  have hmean0 : 0 ≤ mean := mean_nonneg p score hscore
  have hunion := toOuterMeasure_abs_sub_ge_toReal_le (pi p)
    (fun outcome => ∑ i, score i (outcome i)) mean (δ * mean)
  simp only [show mean + δ * mean = (1 + δ) * mean by ring,
    show mean - δ * mean = (1 - δ) * mean by ring] at hunion
  have hcmp : Real.exp (-(δ ^ 2 * mean / 2)) ≤ Real.exp (-(δ ^ 2 * mean / 3)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  linarith [pi_sum_ge_one_add_mul_of_le_one p score hscore le_rfl hδ hδ₁,
    pi_sum_le_one_sub_mul p score hscore le_rfl hδ]

end Cslib.Probability.PMF
