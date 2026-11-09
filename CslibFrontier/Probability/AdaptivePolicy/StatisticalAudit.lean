/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.ImportanceSampling
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Statistical auditing with finite actions and measurable contexts

[Aldridge2027], Section 5.1, PDF p. 5. `finiteActionLaw` first draws a latent
sample from an arbitrary probability measure, then draws an action with the
specified conditional probabilities. For contextual bandits the latent sample
is `(x, ℓ)`, the conditional action probabilities depend only on `x`, and the
observed cost is `ℓ a`. Thus the action draw and potential losses are
conditionally independent given context. No finiteness restriction on contexts
or losses is imposed.

The likelihood-ratio identity and the mean/variance guarantees are derived
from these actual laws. The support condition is almost everywhere, so null
contexts are permitted. `averageChiSquared` is the ordinary conditional
Pearson discrepancy integrated over contexts, in its centered-ratio form.

## Main definitions

* `finiteActionLaw`: actual conditional action sampling on a measurable latent space.
* `actionRatio`: the importance weight read from the selected action's propensities.
* `averageChiSquared`: average conditional Pearson discrepancy under overlap.

## Main results

* `finiteActionLaw_change`: the exact importance-sampling change of law.
* `finiteAction_auditor`: confidence for the actual median-of-means IPW estimator.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace Cslib.Probability.AdaptivePolicy
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A]

/-- Draw the latent sample from `μ`, then draw `a` with probability `b ω a`.
The counting measure is only on the finite action space. -/
@[expose] def finiteActionLaw (μ : Measure Ω) (b : Ω → A → ℝ) : Measure (Ω × A) :=
  (μ.prod Measure.count).withDensity (fun z => ENNReal.ofReal (b z.1 z.2))

/-- Logged likelihood ratio of the target and behavior propensities. -/
@[expose] def actionRatio (b q : Ω → A → ℝ) (z : Ω × A) : ℝ := q z.1 z.2 / b z.1 z.2

/-- The average of conditional chi-squared discrepancies. Under overlap the
summand is `(q a - b a)^2 / b a`, including zero target/behavior mass. -/
@[expose] def averageChiSquared (μ : Measure Ω) (b q : Ω → A → ℝ) : ℝ :=
  ∫ ω, ∑ a, b ω a * (1 - q ω a / b ω a) ^ 2 ∂μ

/-- Conditional Pearson divergence, with infinite value when the target puts
positive mass on a zero-probability behavior action. -/
@[expose] def conditionalPearson (b q : Ω → A → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑ a, ENNReal.ofReal ((q ω a - b ω a) ^ 2) / ENNReal.ofReal (b ω a)

/-- The extended-real average chi-squared divergence from Section 5.1. -/
@[expose] def averagePearson (μ : Measure Ω) (b q : Ω → A → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, conditionalPearson b q ω ∂μ

/-- Conditional probabilities normalized at every latent sample give an actual
probability law, regardless of the cardinality of the latent space. -/
theorem finiteActionLaw_isProbabilityMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hpos : ∀ ω a, 0 ≤ b ω a) (hsum : ∀ ω, ∑ a, b ω a = 1) :
    IsProbabilityMeasure (finiteActionLaw μ b) := by
  constructor
  rw [finiteActionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod _ (by fun_prop)]
  have heq (ω : Ω) : (∫⁻ a, ENNReal.ofReal (b ω a) ∂Measure.count) = 1 := by
    rw [lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun a _ => hpos ω a),
      hsum ω, ENNReal.ofReal_one]
  simp only [heq, lintegral_const, measure_univ, mul_one]

/-- The ordinary conditional-expectation formula for the actual sampling law. -/
theorem integral_finiteActionLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hpos : ∀ ω a, 0 ≤ b ω a) {f : Ω × A → ℝ}
    (hf : Integrable f (finiteActionLaw μ b)) :
    ∫ z, f z ∂finiteActionLaw μ b = ∫ ω, ∑ a, b ω a * f (ω, a) ∂μ := by
  have hi := (integrable_withDensity_iff (μ := μ.prod Measure.count)
    (by fun_prop : Measurable (fun z : Ω × A => ENNReal.ofReal (b z.1 z.2)))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hf
  simp only [ENNReal.toReal_ofReal (hpos _ _)] at hi
  unfold finiteActionLaw
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpos _ _), smul_eq_mul]
  rw [integral_prod]
  · simp only [integral_count]
  · simpa only [mul_comm] using hi

omit [Fintype A] [MeasurableSingletonClass A] in
/-- The logged ratio changes the behavior law into the target law. Overlap is
required only almost everywhere under the original latent distribution. -/
theorem finiteActionLaw_change [Finite A] (μ : Measure Ω)
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hoverlap : ∀ᵐ ω ∂μ, ∀ a, b ω a = 0 → q ω a = 0) :
    (finiteActionLaw μ b).withDensity (fun z => ENNReal.ofReal (actionRatio b q z)) =
      finiteActionLaw μ q := by
  unfold finiteActionLaw
  rw [← withDensity_mul _ (by fun_prop) (by unfold actionRatio; fun_prop)]
  apply withDensity_congr_ae
  have hae : ∀ᵐ z ∂μ.prod (Measure.count : Measure A),
      b z.1 z.2 = 0 → q z.1 z.2 = 0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [hoverlap] with ω hω
    exact ae_of_all _ fun a => hω a
  filter_upwards [hae] with z hz
  simp only [Pi.mul_apply, actionRatio]
  rw [← ENNReal.ofReal_mul (hbpos _ _)]
  congr 1
  by_cases h : b z.1 z.2 = 0
  · simp [h, hz h]
  · exact mul_div_cancel₀ _ h

/-- The density discrepancy is exactly the average conditional discrepancy,
not an assumed variance bound. -/
theorem densityChiSquared_actionRatio (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hbpos : ∀ ω a, 0 ≤ b ω a) (hbsum : ∀ ω, ∑ a, b ω a = 1)
    (hW : MemLp (actionRatio b q) 2 (finiteActionLaw μ b)) :
    densityChiSquared (finiteActionLaw μ b) (actionRatio b q) =
      averageChiSquared μ b q := by
  let := finiteActionLaw_isProbabilityMeasure μ hb hbpos hbsum
  exact integral_finiteActionLaw μ hb hbpos ((memLp_const 1).sub hW).integrable_sq

/-- Theorem 5.3's IPW auditor on the actual finite-action sampling experiment,
with arbitrary measurable latent samples and almost-everywhere overlap.
Square integrability of the ratio is precisely the finite-divergence regime;
the desired variance and confidence estimates are conclusions, not hypotheses. -/
theorem finiteAction_auditor (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hqpos : ∀ ω a, 0 ≤ q ω a) (hbsum : ∀ ω, ∑ a, b ω a = 1)
    (hqsum : ∀ ω, ∑ a, q ω a = 1)
    (hoverlap : ∀ᵐ ω ∂μ, ∀ a, b ω a = 0 → q ω a = 0)
    (hW : MemLp (actionRatio b q) 2 (finiteActionLaw μ b))
    {L : Ω × A → ℝ} (hL : Measurable L)
    (hcost : ∀ z, L z ∈ Set.Icc (0 : ℝ) 1)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * averageChiSquared μ b q ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw (finiteActionLaw μ b) m k).real
      {z | δ ≤ |blockMedianOfMeans (importanceScore L (actionRatio b q)) m k z -
        ((∫ x, L x ∂finiteActionLaw μ b) - ∫ x, L x ∂finiteActionLaw μ q)|} ≤ η := by
  let := finiteActionLaw_isProbabilityMeasure μ hb hbpos hbsum
  let := finiteActionLaw_isProbabilityMeasure μ hq hqpos hqsum
  apply importanceScore_confidence _ _ hL (by unfold actionRatio; fun_prop) hW
    (fun z => div_nonneg (hqpos _ _) (hbpos _ _))
    (finiteActionLaw_change μ hb hq hbpos hoverlap) (B := 1) (by norm_num)
    (ae_of_all _ fun z => (abs_le.mpr ⟨by linarith [(hcost z).1], (hcost z).2⟩))
    hδ hη hm hk
  · simpa only [one_pow, one_mul, densityChiSquared_actionRatio μ hb hbpos hbsum hW] using hsize
  · exact hblocks

/-- The open-loop action frequencies, computed from the latent law and the
behavior policy alone; costs play no role in this definition. -/
@[expose] def marginalAction (μ : Measure Ω) (b : Ω → A → ℝ) (a : A) : ℝ :=
  ∫ ω, b ω a ∂μ

omit [MeasurableSingletonClass A] in
private theorem integrable_actionWeight (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hbpos : ∀ ω a, 0 ≤ b ω a) (hbsum : ∀ ω, ∑ a, b ω a = 1) (a : A) :
    Integrable (fun ω => b ω a) μ := by
  have hm : Measurable (fun ω => b ω a) := hb.comp (measurable_id.prodMk measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbpos ω a)]
    exact (single_le_sum (fun i _ => hbpos ω i) (mem_univ a)).trans_eq (hbsum ω)

omit [MeasurableSingletonClass A] in
/-- The marginal frequencies form a normalized probability vector. -/
theorem marginalAction_properties (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hbpos : ∀ ω a, 0 ≤ b ω a) (hbsum : ∀ ω, ∑ a, b ω a = 1) :
    (∀ a, 0 ≤ marginalAction μ b a) ∧ ∑ a, marginalAction μ b a = 1 := by
  refine ⟨fun a => integral_nonneg (fun ω => hbpos ω a), ?_⟩
  unfold marginalAction
  rw [← integral_finsetSum univ (fun a _ => integrable_actionWeight μ hb hbpos hbsum a)]
  simp only [hbsum, integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- The paper's actual open-loop target is independent of the latent sample and
uses the behavior policy's marginal action frequencies. -/
theorem marginalAction_auditor (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hbpos : ∀ ω a, 0 ≤ b ω a) (hbsum : ∀ ω, ∑ a, b ω a = 1)
    (hoverlap : ∀ᵐ ω ∂μ, ∀ a, b ω a = 0 → marginalAction μ b a = 0)
    (hW : MemLp (actionRatio b (fun _ => marginalAction μ b)) 2 (finiteActionLaw μ b))
    {L : Ω × A → ℝ} (hL : Measurable L)
    (hcost : ∀ z, L z ∈ Set.Icc (0 : ℝ) 1)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * averageChiSquared μ b (fun _ => marginalAction μ b) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw (finiteActionLaw μ b) m k).real
      {z | δ ≤ |blockMedianOfMeans
        (importanceScore L (actionRatio b (fun _ => marginalAction μ b))) m k z -
        ((∫ x, L x ∂finiteActionLaw μ b) -
          ∫ x, L x ∂finiteActionLaw μ (fun _ => marginalAction μ b))|} ≤ η := by
  have hq := marginalAction_properties μ hb hbpos hbsum
  have hqm : Measurable (Function.uncurry (fun _ : Ω => marginalAction μ b)) :=
    (measurable_of_countable (marginalAction μ b)).comp measurable_snd
  exact finiteAction_auditor μ hb hqm hbpos (fun _ => hq.1) hbsum (fun _ => hq.2)
    hoverlap hW hL hcost hδ hη hm hk hsize hblocks

omit [MeasurableSingletonClass A] in
/-- Finite average Pearson divergence implies almost-everywhere overlap. -/
theorem overlap_of_averagePearson_ne_top (μ : Measure Ω)
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q))
    (hfinite : averagePearson μ b q ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ a, b ω a = 0 → q ω a = 0 := by
  classical
  have hm (a : A) : Measurable (fun ω => b ω a) :=
    hb.comp (measurable_id.prodMk measurable_const)
  have hqm (a : A) : Measurable (fun ω => q ω a) :=
    hq.comp (measurable_id.prodMk measurable_const)
  have hp := ae_lt_top (show Measurable (conditionalPearson b q) by
    unfold conditionalPearson; fun_prop) hfinite
  filter_upwards [hp] with ω hω
  intro a hba
  have ht : ENNReal.ofReal ((q ω a - b ω a) ^ 2) / ENNReal.ofReal (b ω a) < ⊤ :=
    (single_le_sum (fun i _ => (zero_le : (0 : ℝ≥0∞) ≤
      ENNReal.ofReal ((q ω i - b ω i) ^ 2) / ENNReal.ofReal (b ω i))) (mem_univ a)).trans_lt hω
  by_contra hqa
  have hn : ENNReal.ofReal ((q ω a - b ω a) ^ 2) ≠ 0 := by
    rw [hba, sub_zero, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sq_pos_of_ne_zero hqa)
  rw [hba] at hn
  rw [hba, ENNReal.ofReal_zero, ENNReal.div_zero hn] at ht
  exact (lt_irrefl _) ht

omit [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Under overlap, the Pearson sum equals the behavior-weighted centered-ratio square. -/
theorem conditionalPearson_eq {b q : Ω → A → ℝ}
    (hbpos : ∀ ω a, 0 ≤ b ω a) (ω : Ω)
    (hoverlap : ∀ a, b ω a = 0 → q ω a = 0) :
    conditionalPearson b q ω =
      ∑ a, ENNReal.ofReal (b ω a) * ENNReal.ofReal ((1 - q ω a / b ω a) ^ 2) := by
  apply sum_congr rfl
  intro a _
  by_cases hba : b ω a = 0
  · simp [hba, hoverlap a hba]
  · rw [← ENNReal.ofReal_div_of_pos (lt_of_le_of_ne (hbpos ω a) (Ne.symm hba)),
      ← ENNReal.ofReal_mul (hbpos ω a)]
    congr 1
    field_simp
    ring

/-- The actual squared density discrepancy has the extended average Pearson
value whenever overlap holds. This is the conditional second-moment identity. -/
theorem lintegral_actionRatio_sq (μ : Measure Ω)
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hoverlap : ∀ᵐ ω ∂μ, ∀ a, b ω a = 0 → q ω a = 0) :
    (∫⁻ z, ENNReal.ofReal ((1 - actionRatio b q z) ^ 2) ∂finiteActionLaw μ b) =
      averagePearson μ b q := by
  unfold finiteActionLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (by unfold actionRatio; fun_prop), lintegral_prod _ (by unfold actionRatio; fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hoverlap] with ω hω
  rw [lintegral_count, tsum_fintype, conditionalPearson_eq hbpos ω hω]
  rfl

/-- The finite-divergence hypothesis alone gives both overlap and the required
square integrability; neither statistical conclusion is assumed. -/
theorem memLp_actionRatio_of_averagePearson_ne_top (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hbsum : ∀ ω, ∑ a, b ω a = 1) (hfinite : averagePearson μ b q ≠ ⊤) :
    MemLp (actionRatio b q) 2 (finiteActionLaw μ b) := by
  let := finiteActionLaw_isProbabilityMeasure μ hb hbpos hbsum
  have ho := overlap_of_averagePearson_ne_top μ hb hq hfinite
  have hZ : Measurable (fun z : Ω × A => 1 - actionRatio b q z) :=
    measurable_const.sub (hq.div hb)
  have hi : Integrable (fun z : Ω × A => (1 - actionRatio b q z) ^ 2)
      (finiteActionLaw μ b) := by
    refine ⟨(hZ.pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).mpr
    rw [lintegral_actionRatio_sq μ hb hq hbpos ho]
    exact lt_top_iff_ne_top.mpr hfinite
  have hz := (memLp_two_iff_integrable_sq
    (show AEStronglyMeasurable (fun z : Ω × A => 1 - actionRatio b q z)
      (finiteActionLaw μ b) from hZ.aestronglyMeasurable)).mpr hi
  convert (memLp_const (1 : ℝ)).sub hz using 1
  ext z
  simp only [Pi.sub_apply]
  ring

/-- The finite real discrepancy used in the confidence bound is the real value
of the paper's extended average chi-squared divergence. -/
theorem averageChiSquared_eq_toReal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hbsum : ∀ ω, ∑ a, b ω a = 1) (hfinite : averagePearson μ b q ≠ ⊤) :
    averageChiSquared μ b q = (averagePearson μ b q).toReal := by
  let := finiteActionLaw_isProbabilityMeasure μ hb hbpos hbsum
  have hW := memLp_actionRatio_of_averagePearson_ne_top μ hb hq hbpos hbsum hfinite
  have ho := overlap_of_averagePearson_ne_top μ hb hq hfinite
  have hi := ((memLp_const (1 : ℝ)).sub hW).integrable_sq
  have heq := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)
  simp only [Pi.sub_apply] at heq
  rw [lintegral_actionRatio_sq μ hb hq hbpos ho] at heq
  change ENNReal.ofReal (densityChiSquared (finiteActionLaw μ b) (actionRatio b q)) =
    averagePearson μ b q at heq
  have hc := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal (densityChiSquared_nonneg (finiteActionLaw μ b)
    (actionRatio b q))] at hc
  rw [← densityChiSquared_actionRatio μ hb hbpos hbsum hW]
  exact hc

/-- Zero Pearson discrepancy gives identical actual action-sampling laws. -/
theorem finiteActionLaw_eq_of_averagePearson_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {b q : Ω → A → ℝ} (hb : Measurable (Function.uncurry b))
    (hq : Measurable (Function.uncurry q)) (hbpos : ∀ ω a, 0 ≤ b ω a)
    (hbsum : ∀ ω, ∑ a, b ω a = 1) (hzero : averagePearson μ b q = 0) :
    finiteActionLaw μ b = finiteActionLaw μ q := by
  let := finiteActionLaw_isProbabilityMeasure μ hb hbpos hbsum
  have hfinite : averagePearson μ b q ≠ ⊤ := by rw [hzero]; exact ENNReal.zero_ne_top
  have hW := memLp_actionRatio_of_averagePearson_ne_top μ hb hq hbpos hbsum hfinite
  have hd : densityChiSquared (finiteActionLaw μ b) (actionRatio b q) = 0 := by
    rw [densityChiSquared_actionRatio μ hb hbpos hbsum hW,
      averageChiSquared_eq_toReal μ hb hq hbpos hbsum hfinite, hzero, ENNReal.toReal_zero]
  have hw := ae_eq_one_of_densityChiSquared_eq_zero (finiteActionLaw μ b) hW hd
  have hc := finiteActionLaw_change μ hb hq hbpos
    (overlap_of_averagePearson_ne_top μ hb hq hfinite)
  have heq : (finiteActionLaw μ b).withDensity (fun z => ENNReal.ofReal (actionRatio b q z)) =
      (finiteActionLaw μ b).withDensity (fun _ => 1) := by
    apply withDensity_congr_ae
    filter_upwards [hw] with z hz
    rw [hz, ENNReal.ofReal_one]
  rw [heq] at hc
  change (finiteActionLaw μ b).withDensity 1 = finiteActionLaw μ q at hc
  rw [withDensity_one] at hc
  exact hc

end Cslib.Probability.AdaptivePolicy
