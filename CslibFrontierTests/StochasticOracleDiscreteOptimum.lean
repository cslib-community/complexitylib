/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Optimum
import CslibFrontierTests.StochasticOracleDiscreteRetention
import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Prefix
import Mathlib.Tactic

/-!
# A sharp fixed-budget optimum with unbounded invoices

A single legal call has a geometric response. Response zero proposes the
singleton cover, while invoice `x + 1` has mean two and unbounded support.
At budget and deadline one, success one-half forces expected cost at least two
for every randomized successful-only competitor. The actual retaining policy
attains two. A greater success target has infinite optimum because no policy
is feasible. The deadline theorem is independent of invoice assumptions.
-/

noncomputable section
namespace CslibFrontierTests.DiscreteOptimum
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory
open StochasticOracleAdaptiveSelectionTests (toy)
open scoped ENNReal

private def propose (_ : List (Record Unit ℕ)) (_ : Unit) (x : ℕ) : List (Finset Unit) :=
  if x = 0 then [{()}] else []
private def respond (_ : List (Record Unit ℕ)) (_ : Unit) : PMF ℕ := DiscreteRetention.law []
private def select (_ : List (Record Unit ℕ)) : PMF Unit := PMF.pure ()
private def charge (_ : List (Record Unit ℕ)) (_ : Unit) (x : ℕ) : ℝ :=
  DiscreteRetention.charge [] x
private def duration (_ : List (Record Unit ℕ)) (_ : Unit) (_ : ℕ) : ℝ := 1

-- A single labeled opportunity can occur at most once in the actual transcript.
private def allowed (choose : List (Record Unit ℕ) → PMF (Option Unit))
    (_ : List (Record Unit ℕ) → PMF (Finset Unit)) : Prop :=
  ∀ h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) 1).support,
    count issued (PMF.seqHistory h) ≤ 1

private theorem allowed_all (choose : List (Record Unit ℕ) → PMF (Option Unit))
    (output : List (Record Unit ℕ) → PMF (Finset Unit)) : allowed choose output := by
  intro h _
  simpa only [PMF.length_seqHistory] using count_le_length issued (PMF.seqHistory h)

private theorem initial_events (x : ℕ) :
    productive toy 1 (recordProposals propose) 1 [] (some ((), x)) = decide (x = 0) ∧
      reveals toy (recordProposals propose) [] (some ((), x)) = decide (x = 0) := by
  by_cases hx : x = 0 <;>
    simp [productive, AdaptiveSelection.residual, selected, recordProposals, propose,
      Instance.retain, Instance.Certified, Instance.covered, Instance.cost, toy, reveals,
      revealed, hx]

private theorem zero_probability (h : List (Record Unit ℕ)) :
    ((respond h ()).toOuterMeasure {0}).toReal = (DiscreteRetention.half : ℝ) := by
  rw [PMF.toOuterMeasure_apply_singleton]
  norm_num [respond, DiscreteRetention.law_apply, DiscreteRetention.half]

-- The actual first issued record has arbitrarily large positive-probability invoices.
example (N : ℕ) :
    ∃ z ∈ (policyLaw (Discrete.retainingChoose toy 1 propose select) respond []).support,
    (N : ℝ) < recordResource charge [] z := by
  refine ⟨some ((), N + 1), ?_, ?_⟩
  · apply (mem_support_policyLaw_some _ _ _ _ _).mpr
    refine ⟨by simp, ?_, ne_of_gt (DiscreteRetention.law_pos _)⟩
    simp [Discrete.retainingChoose, select, selected, Instance.covered, toy]
  · norm_num [recordResource, charge, DiscreteRetention.charge]
    linarith

private theorem upper : Discrete.UpperBounds toy 1 propose select respond charge duration
    1 1 DiscreteRetention.half 2 1 where
  charge_nonneg := by intro h b x; dsimp [charge, DiscreteRetention.charge]; positivity
  progress := by
    intro t ht h hh hc b hb
    have he : t = 0 := by omega
    subst t
    rcases b with ⟨⟩
    simp only [PMF.seqHistory_zero]
    have he : {x | productive toy 1 (recordProposals propose) 1 [] (some ((), x)) = true} =
        ({0} : Set ℕ) := by
      ext x
      simp only [(initial_events x).1, decide_eq_true_eq, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
    rw [he, zero_probability]
  cost := by
    intro t ht h hh hc b hb
    simpa [respond, charge] using (DiscreteRetention.charge_mean []).le
  time := by intros; constructor <;> norm_num [duration]

private theorem lower (choose : List (Record Unit ℕ) → PMF (Option Unit))
    (output : List (Record Unit ℕ) → PMF (Finset Unit))
    (hA : Discrete.Admissible toy propose choose respond output duration 1 1 1) :
    Discrete.LowerBounds toy propose choose respond output charge duration
      1 1 DiscreteRetention.half 2 1 1 where
  charge_nonneg := by intro h b x; dsimp [charge, DiscreteRetention.charge]; positivity
  progress := by
    intro t ht h hh hs b hb
    have he : t = 0 := by omega
    subst t
    rcases b with ⟨⟩
    simp only [PMF.seqHistory_zero]
    have he : {x | reveals toy (recordProposals propose) [] (some ((), x)) = true} =
        ({0} : Set ℕ) := by
      ext x
      simp only [(initial_events x).2, decide_eq_true_eq, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
    rw [he, zero_probability]
  coverage := by
    intro t ht h hh hs b hb x hx
    simpa using Finset.card_le_card (Finset.subset_univ
      (revealed toy (recordProposals propose) (some (b, x) :: PMF.seqHistory h) \
        revealed toy (recordProposals propose) (PMF.seqHistory h)))
  cost := by
    intro t ht h hh hs b hb
    simpa [respond, charge] using (DiscreteRetention.charge_mean []).ge
  provenance := hA

private theorem time_lower (choose : List (Record Unit ℕ) → PMF (Option Unit)) :
    Discrete.LatencyBound choose respond duration 1 1 where
  time := by intros; exact le_rfl

private theorem binomial_failure :
    (ProbabilityTheory.binomial 1 DiscreteRetention.half).real (Set.Iio 1) = 1 / 2 := by
  have he : Set.Iio (1 : ℕ) = {0} := by ext x; simp
  rw [he, ProbabilityTheory.binomial_real_singleton]
  norm_num [DiscreteRetention.half]

private theorem binomial_success :
    (ProbabilityTheory.binomial 1 DiscreteRetention.half).real (Set.Ici 1) = 1 / 2 := by
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, binomial_failure]
  norm_num

private theorem threshold : ∀ k < 1, 1 * k < toy.ground.card := by
  intro k hk
  have he : k = 0 := by omega
  subst k
  norm_num [toy]

private theorem bounds :
    (2 : ℝ≥0∞) ≤ Discrete.optimalCost toy propose respond charge duration allowed 1 1 1 (1 / 2) ∧
      Discrete.optimalCost toy propose respond charge duration allowed 1 1 1 (1 / 2) ≤
        Discrete.expectedCost (Discrete.retainingChoose toy 1 propose select) respond charge 1 ∧
      Discrete.expectedCost (Discrete.retainingChoose toy 1 propose select) respond charge 1 ≤
        2 := by
  have hs := Discrete.optimalCost_sandwich toy propose respond charge duration allowed select
    1 1 1 1 1 (by norm_num [toy])
    threshold
    DiscreteRetention.half DiscreteRetention.half (by norm_num [DiscreteRetention.half])
    (by norm_num [DiscreteRetention.half]) 2 2 1 1 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [binomial_failure]; norm_num) (allowed_all _ _) upper
    (fun choose output _ hA => lower choose output hA)
  norm_num [DiscreteRetention.half, ENNReal.ofReal_div_of_pos] at hs
  exact hs

-- The infimum ranges over every actual randomized competitor, not a supplied optimum certificate.
example : Discrete.optimalCost toy propose respond charge duration allowed 1 1 1 (1 / 2) = 2 :=
  le_antisymm (bounds.2.1.trans bounds.2.2) bounds.1

-- The canonical policy attains the infimum with unbounded correlated invoices.
example :
    Discrete.expectedCost (Discrete.retainingChoose toy 1 propose select) respond charge 1 = 2 :=
  le_antisymm bounds.2.2 (bounds.1.trans bounds.2.1)

example (η : ℝ) (hη : 1 / 2 < η) :
    Discrete.optimalCost toy propose respond charge duration allowed 1 1 1 η = ⊤ := by
  apply Discrete.optimalCost_eq_top_of_deadline_bound toy propose respond charge duration allowed
    1 1 1
    threshold
    DiscreteRetention.half 1 1 1 η (by norm_num)
    (fun choose output _ hA => (lower choose output hA).toProgressBounds)
    (fun choose _ _ _ => time_lower choose)
  norm_num [binomial_success] at hη ⊢
  exact hη

private def haltOnly (choose : List (Record Unit ℕ) → PMF (Option Unit))
    (_ : List (Record Unit ℕ) → PMF (Finset Unit)) : Prop := choose [] = PMF.pure none

private theorem halt_progress (choose : List (Record Unit ℕ) → PMF (Option Unit))
    (output : List (Record Unit ℕ) → PMF (Finset Unit)) (hhalt : haltOnly choose output)
    (hA : Discrete.Admissible toy propose choose respond output duration 1 1 1) :
    Discrete.ProgressBounds toy propose choose respond output duration 1 1 0 1 1 := by
  refine { (lower choose output hA).toProgressBounds with progress := ?_ }
  intro t ht h hh hs b hb
  have he : t = 0 := by omega
  subst t
  simp [PMF.seqHistory_zero, show choose [] = PMF.pure none from hhalt] at hb

-- The policy class is part of the infimum: allowing only an initial halt changes
-- the same source's value from two to infinity at the same one-half success target.
example : Discrete.optimalCost toy propose respond charge duration haltOnly 1 1 1 (1 / 2) = ⊤ := by
  apply Discrete.optimalCost_eq_top_of_deadline_bound toy propose respond charge duration haltOnly
    1 1 1 threshold (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) 1 1 1 (1 / 2) (by norm_num)
    (fun choose output hhalt hA => halt_progress choose output hhalt hA)
    (fun choose _ _ _ => time_lower choose)
  norm_num [ProbabilityTheory.binomial_one_eq_bernoulliMeasure, measureReal_def]

end CslibFrontierTests.DiscreteOptimum
