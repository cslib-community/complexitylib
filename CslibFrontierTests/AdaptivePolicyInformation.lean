/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.AdaptivePolicy.Regret
import CslibFrontier.Probability.AdaptivePolicy.Sharpness
import CslibFrontier.Probability.AdaptivePolicy.Pathwise
import CslibFrontier.Probability.AdaptivePolicy.MeasurableNonidentifiability
import CslibFrontier.Probability.PMF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! Checked clients of the source information, regret and measurable logging contracts. -/
noncomputable section
open Finset Cslib.Probability.AdaptivePolicy
namespace CslibFrontierTests.AdaptivePolicyInformation

/-- A valid noisy channel has a nonzero adaptivity benefit, rather than an assumed gap. -/
example : ∃ π : MarkovPolicy Bool Bool,
    Sharpness.experiment.totalCost π 1 -
      Sharpness.experiment.totalCost (Sharpness.experiment.openLoop π) 1 = -1/4 ∧
    Sharpness.experiment.actionSpan π 0
      (Sharpness.experiment.actionValue (Sharpness.experiment.openLoop π) 1 0) = 1 := by
  have hv : |(1/2:ℝ)| ≤ 1 := by norm_num
  refine ⟨Sharpness.policy (1/2) hv, ?_, Sharpness.span_eq_one _ _⟩
  rw [(Sharpness.costs _ _).1, (Sharpness.costs _ _).2]
  norm_num

/-- The limiting zero-information channel has exactly zero gap and a nonzero cost span. -/
example : ∃ π : MarkovPolicy Bool Bool,
    Sharpness.experiment.mutualInformation π 0 = 0 ∧
    Sharpness.experiment.totalCost π 1 =
      Sharpness.experiment.totalCost (Sharpness.experiment.openLoop π) 1 ∧
    Sharpness.experiment.actionSpan π 0
      (Sharpness.experiment.actionValue (Sharpness.experiment.openLoop π) 1 0) = 1 := by
  have hv : |(0:ℝ)| ≤ 1 := by norm_num
  refine ⟨Sharpness.policy 0 hv, ?_, ?_, Sharpness.span_eq_one _ _⟩
  · rw [Sharpness.mutualInformation_eq]
    norm_num [Sharpness.information]
  · rw [(Sharpness.costs _ _).1, (Sharpness.costs _ _).2]
    norm_num

/-- A two-round path beats every fixed action; its static gap is zero. -/
example :
    Pathwise.covariance (fun t i : Bool => if t = i then (1:ℝ) else 0)
      (fun t i : Bool => if t ≠ i then (1:ℝ) else 0) = -1 ∧
    Pathwise.regret (fun t i : Bool => if t = i then (1:ℝ) else 0)
      (fun t i : Bool => if t ≠ i then (1:ℝ) else 0) (fun _ => 1/2) = -1 := by
  norm_num [Pathwise.covariance, Pathwise.mean, Pathwise.regret]

/-- Large impossible-action costs do not inflate the supported span. -/
def fixedPolicy : MarkovPolicy Bool Bool where
  prob _ _ a := if a then 1 else 0
  nonneg _ _ _ := by split <;> norm_num
  sum_prob _ _ := by simp

/-- A support-sensitive bound can vanish even when the global action range is large. -/
example : Sharpness.experiment.actionSpan fixedPolicy 0
    (fun _ a => if a then 0 else 1000000) = 0 := by
  apply le_antisymm
  · apply FiniteMDP.actionSpan_le _ _ (by norm_num : (0:ℝ) ≤ 0)
    intro s a _ ha
    cases a
    · norm_num [FiniteMDP.stateLaw, Sharpness.experiment, fixedPolicy] at ha
    · norm_num
  · exact FiniteMDP.actionSpan_nonneg _ _ _ _

open MeasureTheory
open Cslib.Probability

/-- A continuous signal paired with a fair binary context component. -/
def gaussianContext : Measure (ℝ × Bool) :=
  (ProbabilityTheory.gaussianReal 0 1).prod (PMF.uniformOfFintype Bool).toMeasure

/-- A genuinely infinite-context client: the policy reads the binary component
of a Gaussian/binary context, and its full logs cannot identify adaptivity cost. -/
example : ∃ loss₀ loss₁ : (ℝ × Bool) × Bool → Bool,
    Measurable loss₀ ∧ Measurable loss₁ ∧
    (∀ T, measurableSampleLaw
      (gaussianContext.map (fun x => (x, x.2))) loss₀ T =
      measurableSampleLaw (gaussianContext.map (fun x => (x, x.2))) loss₁ T) ∧
    measurableGap (gaussianContext.map (fun x => (x, x.2))) loss₁ ≠
      measurableGap (gaussianContext.map (fun x => (x, x.2))) loss₀ := by
  have : IsProbabilityMeasure gaussianContext := by unfold gaussianContext; infer_instance
  apply deterministic_nonidentifiability gaussianContext Prod.snd measurable_snd
  intro a ha
  have hz : gaussianContext {x | x.2 ≠ a} = 0 := ae_iff.mp ha
  have he : {x : ℝ × Bool | x.2 ≠ a} = Set.univ ×ˢ {(!a)} := by
    ext x
    cases a <;> cases x.2 <;> simp
  rw [he, gaussianContext, Measure.prod_prod, measure_univ, one_mul,
    _root_.PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply] at hz
  norm_num at hz

end CslibFrontierTests.AdaptivePolicyInformation
