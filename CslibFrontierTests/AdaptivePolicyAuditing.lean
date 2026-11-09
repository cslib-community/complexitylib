/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.AdaptivePolicy.ContextualAudit
import CslibFrontier.Probability.AdaptivePolicy.AuditLowerBound
import CslibFrontier.Probability.AdaptivePolicy.EpisodicAudit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! Concrete clients for observable auditing, hard-instance constants and whole episodes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Cslib.Probability Cslib.Probability.AdaptivePolicy
open Finset
namespace CslibFrontierTests.AdaptivePolicyAuditing

/-- One outlier among three means cannot move the median out of the unit interval. -/
example : |lowerMedian ![0, 0, 100] - (0 : ℝ)| < 1 := by
  apply abs_lowerMedian_sub_lt (by norm_num)
  norm_num [Fin.card_filter_univ_succ]

/-- Even block counts and empty blocks have explicit behavior. -/
example : lowerMedian (fun _ : Fin 4 => (7 : ℝ)) = 7 ∧
    medianOfMeans (fun x : ℝ => x) 0 4 (fun _ => Fin.elim0) = 0 :=
  ⟨lowerMedian_const (by norm_num) 7, medianOfMeans_zero_length _ _ _⟩

open AuditLowerBound in
/-- The boundary parameters yield the exact source gap, discrepancy and rare-event mass. -/
example : hardGap (1/4) (1/4) = -1/32 ∧ hardGap (1/4) (-1/4) = 1/32 ∧
    hardMass (1/4) (1/4) (true, true, true) = 3/32 ∧
    averagePearson (PMF.uniformOfFintype Bool).toMeasure (hardAction (1/4))
      (fun _ _ => 1/2) = ENNReal.ofReal (1/3) := by
  rw [hardGap_eq, hardGap_eq, hard_averagePearson (by norm_num) (by norm_num)]
  norm_num [hardMass, hardAction, hardMean]

open AuditLowerBound in
/-- Conditional independence is realized before the selected cost is observed. -/
example : (∑ yfalse : Bool, ∑ ytrue : Bool,
    hardPotentialMass (1/4) true yfalse ytrue * hardAction (1/4) true true *
      (if ytrue = true then 1 else 0)) = 3/32 := by
  have h := hardMass_observation (1/4) (1/4) true true true
  norm_num [hardMass, hardAction, hardMean] at h ⊢
  exact h

open AuditLowerBound in
/-- A positive-divergence auditor with concrete integer blocks: 22 samples in
each of 56 independent blocks, error tolerance 1/4 and failure at most 1/8. -/
example :
    let μ := (PMF.uniformOfFintype Bool).toMeasure
    let b := hardAction (1/4)
    let q := fun _ _ : Bool => (1/2 : ℝ)
    let L : Bool × Bool → ℝ := fun (x, a) => if x && a then (1 : ℝ) else 0
    (blockSampleLaw (finiteActionLaw μ b) 22 56).real
      {z | (1/4 : ℝ) ≤ |medianOfMeans (importanceScore L (actionRatio b q)) 22 56 z + 1/8|}
        ≤ 1/8 := by
  dsimp only
  let μ := (PMF.uniformOfFintype Bool).toMeasure
  let b := hardAction (1/4)
  let q := fun _ _ : Bool => (1/2 : ℝ)
  let L : Bool × Bool → ℝ := fun (x, a) => if x && a then (1 : ℝ) else 0
  have hb : Measurable (Function.uncurry b) := measurable_of_countable _
  have hq : Measurable (Function.uncurry q) := measurable_of_countable _
  have hbp (x a : Bool) : 0 ≤ b x a := by cases x <;> cases a <;> norm_num [b, hardAction]
  have hbs (x : Bool) : ∑ a, b x a = 1 := by cases x <;> norm_num [b, hardAction]
  have hqp (x a : Bool) : 0 ≤ q x a := by norm_num [q]
  have hqs (x : Bool) : ∑ a, q x a = 1 := by norm_num [q]
  let := finiteActionLaw_isProbabilityMeasure μ hb hbp hbs
  let := finiteActionLaw_isProbabilityMeasure μ hq hqp hqs
  have hc : averagePearson μ b q = ENNReal.ofReal (1/3) := by
    dsimp only [μ, b, q]
    rw [hard_averagePearson (p := 1/4) (by norm_num) (by norm_num)]
    norm_num
  have hf : averagePearson μ b q ≠ ⊤ := by rw [hc]; exact ENNReal.ofReal_ne_top
  have hW := memLp_actionRatio_of_averagePearson_ne_top μ hb hq hbp hbs hf
  have hgap : (∫ z, L z ∂finiteActionLaw μ b) - ∫ z, L z ∂finiteActionLaw μ q = -1/8 := by
    rw [integral_finiteActionLaw μ hb hbp Integrable.of_finite,
      integral_finiteActionLaw μ hq hqp Integrable.of_finite]
    norm_num [μ, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, L, b, q, hardAction]
  have hsize : 4 * averageChiSquared μ b q ≤ (22 : ℝ) * (1/4) ^ 2 := by
    rw [averageChiSquared_eq_toReal μ hb hq hbp hbs hf, hc]
    norm_num
  have hblocks : 8 * Real.log (1 / (1/8 : ℝ)) ≤ (56 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h ⊢
    linarith
  have h := finiteAction_auditor μ hb hq hbp hqp hbs hqs
    (overlap_of_averagePearson_ne_top μ hb hq hf) hW (measurable_of_countable L)
    (fun ⟨x, a⟩ => by cases x <;> cases a <;> norm_num [L])
    (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) < 1/8)
    (by norm_num : 0 < 22) (by norm_num : 0 < 56) hsize hblocks
  rw [hgap] at h
  simpa only [μ, b, q, L, neg_div, sub_neg_eq_add] using h

/-- A continuous context paired with a fixed bounded potential-cost vector. -/
def gaussianPotential : Measure (BanditPotential ℝ Bool) :=
  (gaussianReal 0 1).map (fun x => (x, fun a : Bool =>
    if a then (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) else ⟨0, by norm_num⟩))

/-- The zero-divergence branch applies to a genuinely continuous context law,
without a finite context enumeration or a positive-divergence assumption. -/
example :
    (∫ z, banditLoss z ∂finiteActionLaw gaussianPotential (banditBehavior (fun _ _ => 1/2))) -
      ∫ z, banditLoss z ∂finiteActionLaw gaussianPotential
        (fun _ => marginalAction gaussianPotential (banditBehavior (fun _ _ => 1/2))) = 0 := by
  have : IsProbabilityMeasure gaussianPotential := by
    unfold gaussianPotential
    infer_instance
  have hm (a : Bool) : marginalAction gaussianPotential
      (banditBehavior (fun _ : ℝ => fun _ : Bool => 1/2)) a = 1/2 := by
    simp [marginalAction, banditBehavior]
  apply contextual_gap_eq_zero gaussianPotential (π := fun _ _ => 1/2)
    (by fun_prop) (by intro x a; norm_num) (by intro x; norm_num)
  simp only [averagePearson, conditionalPearson, banditBehavior, hm, sub_self,
    zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero, ENNReal.zero_div,
    sum_const_zero, lintegral_zero]

/-- A deterministic two-state transition law, with both action probabilities positive. -/
def testMDP : FiniteMDP Bool Bool where
  initial s := if s then 0 else 1
  initial_nonneg s := by cases s <;> norm_num
  initial_sum := by norm_num
  transition _ s a s' := if s' = (s != a) then 1 else 0
  transition_nonneg _ _ _ _ := by split <;> norm_num
  transition_sum _ s a := by cases s <;> cases a <;> norm_num
  cost _ s a := if s = a then 1 else 0

/-- The behavior law chooses either action fairly at each reached state. -/
def fairPolicy : MarkovPolicy Bool Bool where
  prob _ _ _ := 1/2
  nonneg _ _ _ := by norm_num
  sum_prob _ _ := by norm_num

/-- A two-step path retains its actual changed state and accumulates both costs. -/
example : testMDP.episodeMassFrom fairPolicy 2 0 false
    (true, true, (true, false, PUnit.unit)) = 1/4 ∧
    testMDP.episodeLossFrom 2 0 false (true, true, (true, false, PUnit.unit)) = 1 := by
  norm_num [FiniteMDP.episodeMassFrom, FiniteMDP.episodeLossFrom, testMDP, fairPolicy]

/-- The real trajectory experiment normalizes and agrees with the MDP's total
cost for a nonzero horizon; no trajectory moment is assumed. -/
example : (∑ z, (testMDP.episodeLaw fairPolicy 2 z).toReal) = 1 ∧
    (∫ z, testMDP.episodeLoss 2 z ∂(testMDP.episodeLaw fairPolicy 2).toMeasure) =
      testMDP.totalCost fairPolicy 2 := by
  constructor
  · exact Cslib.Probability.PMF.sum_toReal _
  · exact testMDP.episodeLoss_integral fairPolicy 2

/-- Arbitrary fair logged trajectories admit the episode auditor, including
states unreachable under the deterministic transitions. -/
example {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * ((2 : ℝ) ^ 2 * testMDP.trajectoryChiSquared fairPolicy
      (testMDP.openLoop fairPolicy) 2) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw ((testMDP.episodeLaw fairPolicy 2).toMeasure.map
      (testMDP.episodeObservation fairPolicy (testMDP.openLoop fairPolicy) 2)) m k).real
      {z | δ ≤ |medianOfMeans (FiniteMDP.episodeObservedScore 2) m k z -
          (testMDP.totalCost fairPolicy 2 -
            testMDP.totalCost (testMDP.openLoop fairPolicy) 2)|} ≤ η := by
  apply testMDP.episodic_observed_auditor fairPolicy
    (fun _ _ _ _ _ h => by norm_num [fairPolicy] at h)
    (fun t _ s a => by cases s <;> cases a <;> norm_num [testMDP]) hδ hη hm hk hsize hblocks

/-- The terminal next state is absent from the observed record and score. -/
example : testMDP.episodeObservation fairPolicy fairPolicy 1
    (false, (true, true, PUnit.unit)) = testMDP.episodeObservation fairPolicy fairPolicy 1
      (false, (true, false, PUnit.unit)) := by
  funext i
  fin_cases i
  rfl

/-- Horizon zero has zero trajectory discrepancy, with no positive-horizon premise. -/
example : testMDP.trajectoryChiSquared fairPolicy fairPolicy 0 = 0 := by
  have hw (z : Bool × EpisodeTail Bool Bool 0) :
      FiniteMDP.episodeWeight fairPolicy fairPolicy 0 z = 1 := by obtain ⟨s, tail⟩ := z; rfl
  unfold FiniteMDP.trajectoryChiSquared densityChiSquared
  simp only [hw, sub_self, zero_pow (by norm_num : 2 ≠ 0), integral_zero]

end CslibFrontierTests.AdaptivePolicyAuditing
