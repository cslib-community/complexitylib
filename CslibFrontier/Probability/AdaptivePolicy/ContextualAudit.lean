/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.StatisticalAudit
import Mathlib.Tactic

/-!
# Observable contextual-bandit auditing

[Aldridge2027], Theorem 5.3, PDF p. 5. A potential-outcome sample consists of a
context and a vector of costs in `[0,1]`. Their joint probability law is arbitrary
on the measurable context space. The action probabilities depend only on the
context, so sampling an action is conditionally independent of the cost vector.
Only context, the behavior propensities, the selected action and its cost are
recorded. The target frequencies are known, as in Remark 5.1. The actual
observation law is a pushforward; all repetitions and blocks are independent
products of that law.

## Main definitions

* `banditObservation`: the complete observable record, without counterfactual costs.
* `banditScore`: the IPW score computed solely from that record.

## Main results

* `contextual_auditor_finite_divergence`: observable confidence from finite average divergence.
* `contextual_auditor_ceiling`: exact integer sample and block counts.
* `contextual_gap_eq_zero`: exact zero-sample output at zero divergence.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace Cslib.Probability.AdaptivePolicy
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A]

/-- One latent context and bounded potential-cost vector. -/
abbrev BanditPotential (X A : Type*) := X × (A → Set.Icc (0 : ℝ) 1)

/-- A record retaining the context, all behavior propensities, observed loss,
and selected action. It omits every unobserved counterfactual loss. -/
abbrev BanditRecord (X A : Type*) := (X × (A → ℝ) × ℝ) × A

/-- The behavior policy ignores the potential-cost vector when drawing its action. -/
@[expose] def banditBehavior (π : X → A → ℝ) : BanditPotential X A → A → ℝ :=
  fun (x, _) => π x

/-- The selected loss, used to define the latent experiment's expected cost. -/
@[expose] def banditLoss : BanditPotential X A × A → ℝ :=
  fun ((_, losses), a) => losses a

/-- The actual record available to the auditor. -/
@[expose] def banditObservation (π : X → A → ℝ) :
    BanditPotential X A × A → BanditRecord X A :=
  fun ((x, losses), a) => ((x, π x, losses a), a)

/-- The estimator's one-round score, using only the observed loss and propensities. -/
@[expose] def banditScore (q : A → ℝ) : BanditRecord X A → ℝ :=
  fun ((_, propensities, loss), a) => loss * (1 - q a / propensities a)

omit [Fintype A] in
/-- The selected-loss map is measurable for arbitrary measurable contexts. -/
@[fun_prop] theorem measurable_banditLoss [Countable A] : Measurable (@banditLoss X A) := by
  apply measurable_from_prod_countable_left
  intro a
  exact measurable_subtype_coe.comp ((measurable_pi_apply a).comp measurable_snd)

omit [Fintype A] in
/-- Complete observed records are measurable. -/
@[fun_prop] theorem measurable_banditObservation [Countable A] {π : X → A → ℝ}
    (hπ : Measurable (Function.uncurry π)) : Measurable (banditObservation π) := by
  have hπm : Measurable π := Measurable.of_eval fun a =>
    hπ.comp (measurable_id.prodMk measurable_const)
  apply measurable_from_prod_countable_left
  intro a
  unfold banditObservation
  fun_prop

omit [Fintype A] in
/-- The one-round auditor is a measurable function of its record. -/
@[fun_prop] theorem measurable_banditScore [Countable A] (q : A → ℝ) :
    Measurable (@banditScore X A q) := by
  apply measurable_from_prod_countable_left
  intro a
  unfold banditScore
  fun_prop

omit [MeasurableSpace X] [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
/-- The record contains exactly the information needed to compute the latent
importance score. This identity excludes access to unobserved costs. -/
theorem banditScore_observation (π : X → A → ℝ) (q : A → ℝ) :
    banditScore q ∘ banditObservation π =
      importanceScore banditLoss (actionRatio (banditBehavior π) (fun _ => q)) := rfl

/-- Theorem 5.3 for actual stochastic bounded losses, arbitrary measurable
contexts, known marginal frequencies and logged propensities. The two explicit
finiteness conditions (overlap and an `L²` ratio) express the finite chi-squared
regime. The output uses only i.i.d. observed records. -/
theorem contextual_auditor (μ : Measure (BanditPotential X A)) [IsProbabilityMeasure μ]
    {π : X → A → ℝ} (hπ : Measurable (Function.uncurry π))
    (hπpos : ∀ x a, 0 ≤ π x a) (hπsum : ∀ x, ∑ a, π x a = 1)
    (hoverlap : ∀ᵐ ω ∂μ, ∀ a, π ω.1 a = 0 → marginalAction μ (banditBehavior π) a = 0)
    (hW : MemLp (actionRatio (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π))) 2
        (finiteActionLaw μ (banditBehavior π)))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * averageChiSquared μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π)) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw ((finiteActionLaw μ (banditBehavior π)).map (banditObservation π)) m k).real
      {z | δ ≤ |medianOfMeans (banditScore (marginalAction μ (banditBehavior π))) m k z -
        ((∫ x, banditLoss x ∂finiteActionLaw μ (banditBehavior π)) -
          ∫ x, banditLoss x ∂finiteActionLaw μ
            (fun _ => marginalAction μ (banditBehavior π)))|} ≤ η := by
  have hb : Measurable (Function.uncurry (banditBehavior π)) :=
    hπ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  let := finiteActionLaw_isProbabilityMeasure μ hb (fun ω => hπpos ω.1)
    (fun ω => hπsum ω.1)
  rw [medianOfMeans_observation_failure _ (measurable_banditObservation hπ)
    (measurable_banditScore _) m k, banditScore_observation]
  exact marginalAction_auditor μ hb (fun ω => hπpos ω.1) (fun ω => hπsum ω.1)
    hoverlap hW measurable_banditLoss (fun ⟨(_, losses), a⟩ => (losses a).property)
    hδ hη hm hk hsize hblocks

/-- Theorem 5.3 in the paper's finite-divergence form. Almost-everywhere overlap
and finite second moments are derived from that single extended-real hypothesis. -/
theorem contextual_auditor_finite_divergence
    (μ : Measure (BanditPotential X A)) [IsProbabilityMeasure μ]
    {π : X → A → ℝ} (hπ : Measurable (Function.uncurry π))
    (hπpos : ∀ x a, 0 ≤ π x a) (hπsum : ∀ x, ∑ a, π x a = 1)
    (hfinite : averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π)) ≠ ⊤)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * (averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π))).toReal ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw ((finiteActionLaw μ (banditBehavior π)).map (banditObservation π)) m k).real
      {z | δ ≤ |medianOfMeans (banditScore (marginalAction μ (banditBehavior π))) m k z -
        ((∫ x, banditLoss x ∂finiteActionLaw μ (banditBehavior π)) -
          ∫ x, banditLoss x ∂finiteActionLaw μ
            (fun _ => marginalAction μ (banditBehavior π)))|} ≤ η := by
  have hb : Measurable (Function.uncurry (banditBehavior π)) :=
    hπ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hq : Measurable (Function.uncurry
      (fun _ : BanditPotential X A => marginalAction μ (banditBehavior π))) :=
    (measurable_of_countable _).comp measurable_snd
  apply contextual_auditor μ hπ hπpos hπsum
    (overlap_of_averagePearson_ne_top μ hb hq hfinite)
    (memLp_actionRatio_of_averagePearson_ne_top μ hb hq (fun ω => hπpos ω.1)
      (fun ω => hπsum ω.1) hfinite) hδ hη hm hk
  · rw [averageChiSquared_eq_toReal μ hb hq (fun ω => hπpos ω.1)
      (fun ω => hπsum ω.1) hfinite]
    exact hsize
  · exact hblocks

/-- With positive divergence, the literal ceiling block sizes printed in
Theorem 5.3 suffice. The rectangular experiment has exactly `m * k` observations.
Zero divergence is handled separately, rather than forming zero-length means. -/
theorem contextual_auditor_ceiling
    (μ : Measure (BanditPotential X A)) [IsProbabilityMeasure μ]
    {π : X → A → ℝ} (hπ : Measurable (Function.uncurry π))
    (hπpos : ∀ x a, 0 ≤ π x a) (hπsum : ∀ x, ∑ a, π x a = 1)
    (hfinite : averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π)) ≠ ⊤)
    (hpositive : 0 < (averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π))).toReal)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hηone : η < 1) :
    let v := (averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π))).toReal
    let m := ⌈4 * v / δ ^ 2⌉₊
    let k := ⌈8 * Real.log (1 / η)⌉₊
    (blockSampleLaw ((finiteActionLaw μ (banditBehavior π)).map (banditObservation π)) m k).real
      {z | δ ≤ |medianOfMeans (banditScore (marginalAction μ (banditBehavior π))) m k z -
        ((∫ x, banditLoss x ∂finiteActionLaw μ (banditBehavior π)) -
          ∫ x, banditLoss x ∂finiteActionLaw μ
            (fun _ => marginalAction μ (banditBehavior π)))|} ≤ η := by
  dsimp only
  apply contextual_auditor_finite_divergence μ hπ hπpos hπsum hfinite hδ hη
  · exact Nat.one_le_ceil_iff.mpr (div_pos (mul_pos (by norm_num) hpositive) (sq_pos_of_pos hδ))
  · apply Nat.one_le_ceil_iff.mpr
    have : 1 < 1 / η := (lt_div_iff₀ hη).mpr (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos this)
  · exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp (Nat.le_ceil _)
  · exact Nat.le_ceil _

/-- The zero-divergence branch outputs zero without observing a sample.
Its target is exactly zero, so it has zero failure probability at every positive tolerance. -/
theorem contextual_gap_eq_zero
    (μ : Measure (BanditPotential X A)) [IsProbabilityMeasure μ]
    {π : X → A → ℝ} (hπ : Measurable (Function.uncurry π))
    (hπpos : ∀ x a, 0 ≤ π x a) (hπsum : ∀ x, ∑ a, π x a = 1)
    (hzero : averagePearson μ (banditBehavior π)
      (fun _ => marginalAction μ (banditBehavior π)) = 0) :
    (∫ x, banditLoss x ∂finiteActionLaw μ (banditBehavior π)) -
      ∫ x, banditLoss x ∂finiteActionLaw μ
        (fun _ => marginalAction μ (banditBehavior π)) = 0 := by
  have hb : Measurable (Function.uncurry (banditBehavior π)) :=
    hπ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hq : Measurable (Function.uncurry
      (fun _ : BanditPotential X A => marginalAction μ (banditBehavior π))) :=
    (measurable_of_countable _).comp measurable_snd
  have heq := finiteActionLaw_eq_of_averagePearson_zero μ hb hq
    (fun ω => hπpos ω.1) (fun ω => hπsum ω.1) hzero
  rw [heq, sub_self]

omit [Fintype A] [MeasurableSingletonClass A] in
/-- The marginal frequencies depend only on the context marginal of the
potential-outcome law, not on the conditional cost distribution. -/
theorem bandit_marginal_contextLaw
    (μ : Measure (BanditPotential X A)) {π : X → A → ℝ}
    (hπ : Measurable (Function.uncurry π)) (a : A) :
    marginalAction μ (banditBehavior π) a = ∫ x, π x a ∂μ.map Prod.fst := by
  have hm : Measurable (fun x => π x a) := hπ.comp (measurable_id.prodMk measurable_const)
  rw [integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable]
  rfl

omit [MeasurableSingletonClass A] in
/-- The divergence parameter is exactly the context-averaged conditional
chi-squared divergence from the paper; potential costs do not enter it. -/
theorem bandit_averagePearson_contextLaw
    (μ : Measure (BanditPotential X A)) {π : X → A → ℝ}
    (hπ : Measurable (Function.uncurry π)) (q : A → ℝ) :
    averagePearson μ (banditBehavior π) (fun _ => q) =
      averagePearson (μ.map Prod.fst) π (fun _ => q) := by
  have hm (a : A) : Measurable (fun x => π x a) := hπ.comp (measurable_id.prodMk measurable_const)
  have hc : Measurable (conditionalPearson π (fun _ => q)) := by
    unfold conditionalPearson
    fun_prop
  unfold averagePearson
  rw [lintegral_map hc measurable_fst]
  rfl

end Cslib.Probability.AdaptivePolicy
