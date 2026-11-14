/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init

import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Deadline
import CslibFrontier.Probability.PMF.SequentialPrefix
import CslibFrontier.Probability.PMF.Event
import CslibFrontierTests.StochasticOracleDiscreteRetention
import CslibFrontierTests.StochasticOracleSelectionPolicy
import Mathlib.Tactic

/-!
# A deadline shorter than the decision budget

A geometric zero response supplies a buffered bundle, rejected by local retention.
The competitor queries until it receives that bundle, then halts and randomly
returns its cheap or expensive singleton. The expensive failed output may also
be fabricated before receiving anything. Each issued call takes one unit of time:
three decision turns allow at most one call on a successful deadline-one run.
No token resource is supplied to the deadline theorem.
-/

-- This module checks public APIs through private fixtures and anonymous examples.
set_option linter.privateModule false

public section
noncomputable section
namespace CslibFrontierTests.DiscreteDeadline
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory
open StochasticOracleSelectionPolicyTests (bufferedInstance)
open scoped ENNReal

private def received (h : List (Record Unit ℕ)) : Bool :=
  h.any fun z => z = some ((), 0)
private def propose (_ : List (Record Unit ℕ)) (_ : Unit) (x : ℕ) : List (Finset Bool) :=
  if x = 0 then [Finset.univ] else []
private def respond (_ : List (Record Unit ℕ)) (_ : Unit) : PMF ℕ := DiscreteRetention.law []
private def choose (h : List (Record Unit ℕ)) : PMF (Option Unit) :=
  PMF.pure (if received h then none else some ())
private def output (h : List (Record Unit ℕ)) : PMF (Finset Bool) :=
  if received h then (PMF.uniformOfFintype Bool).map fun b => {b} else PMF.pure {false}
private def duration (_ : List (Record Unit ℕ)) (_ : Unit) (_ : ℕ) : ℝ := 1

private theorem proposed_eq (h : List (Record Unit ℕ)) :
    proposedSets (recordProposals propose) h = if received h then Finset.univ else ∅ := by
  induction h with
  | nil => simp [proposedSets, received]
  | cons z h ih =>
    cases z with
    | none => simpa [proposedSets, recordProposals, received] using ih
    | some z =>
      rcases z with ⟨⟨⟩, x⟩
      by_cases hx : x = 0
      · subst x
        rw [proposedSets, recordProposals_some, propose, ite_eq_left rfl]
        simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty]
        have hu : (Finset.univ : Finset Bool) ∪ proposedSets (recordProposals propose) h =
            Finset.univ := Finset.union_eq_left.mpr (Finset.subset_univ _)
        rw [hu]
        simp [received]
      · simpa [proposedSets, recordProposals, propose, hx, received] using ih

private theorem bad_not_certified (h : List (Record Unit ℕ)) :
    ¬CertifiedOutput bufferedInstance 1 1 duration h {false} := by
  intro hs
  have hc := hs.2.1
  norm_num [Instance.cost, bufferedInstance] at hc

private theorem envelopes (u : ℕ) :
    Discrete.ProgressBounds bufferedInstance propose choose respond output duration
      u 1 DiscreteRetention.half 1 1 where
  progress := by
    intro t ht h hh hs i hi
    have he : {x | reveals bufferedInstance (recordProposals propose) (PMF.seqHistory h)
        (some (i, x)) = true} ⊆ ({0} : Set ℕ) := by
      intro x hx
      by_contra hx0
      have hz : x ≠ 0 := hx0
      simp [reveals, revealed, recordProposals, propose, hz, Instance.covered] at hx
    apply le_trans (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) (measure_mono he))
    rw [PMF.toOuterMeasure_apply_singleton]
    norm_num [respond, DiscreteRetention.law_apply, DiscreteRetention.half]
  coverage := by
    intro t ht h hh hs i hi x hx
    simpa using Finset.card_le_card (Finset.subset_univ
      (revealed bufferedInstance (recordProposals propose) (some (i, x) :: PMF.seqHistory h) \
        revealed bufferedInstance (recordProposals propose) (PMF.seqHistory h)))
  provenance := by
    intro h hh C hC hs
    by_cases ha : received (PMF.seqHistory h) = true
    · rw [proposed_eq, ite_eq_left ha]
      exact Finset.subset_univ C
    · have he : C = {false} := by simpa [output, ha] using hC
      subst C
      exact (bad_not_certified _ hs).elim

private theorem time_envelope (u : ℕ) : Discrete.LatencyBound choose respond duration u 1 where
  time := by intros; exact le_rfl

-- The comparison uses one completed opportunity, even though the process has three turns.
example :
    ((Discrete.outputLaw choose respond output 3).toOuterMeasure
      {z | CertifiedOutput bufferedInstance 1 1 duration z.history z.returned}).toReal ≤
        (ProbabilityTheory.binomial 1 DiscreteRetention.half).real (Set.Ici 1) := by
  have hb := Discrete.deadline_probability_le bufferedInstance propose choose respond output
    duration
    3 1 1 (by
      intro k hk
      have he : k = 0 := by omega
      subst k
      norm_num [bufferedInstance])
    DiscreteRetention.half 1 1 1 (by norm_num) (envelopes 3) (time_envelope 3)
  norm_num at hb ⊢
  exact hb

private def timely : Fin 3 → Record Unit ℕ :=
  Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 (some ((), 0))) none) none

-- A supported deadline-one execution succeeds with positive probability; the bound is nonvacuous.
example : 0 < ((Discrete.outputLaw choose respond output 3).toOuterMeasure
    {z | CertifiedOutput bufferedInstance 1 1 duration z.history z.returned}).toReal := by
  apply (PMF.toOuterMeasure_toReal_pos_iff _ _).mpr
  refine ⟨⟨PMF.seqHistory timely, {true}⟩, ?_, ?_⟩
  · norm_num [CertifiedOutput, timely, PMF.seqHistory_snoc, Instance.covered, Instance.cost,
      bufferedInstance, accruedBill, recordResource, duration, Fin.snoc_zero]
  · apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨timely, ?_, ?_⟩
    · simp only [timely, PMF.mem_support_seqProcess_snoc]
      simp [responseStep, policyLaw, responseRecord, choose, received, respond,
        PMF.seqHistory_snoc, DiscreteRetention.law_pos, ne_of_gt, PMF.seqProcess, Fin.snoc_zero]
    · apply (PMF.mem_support_map_iff _ _ _).mpr
      refine ⟨{true}, ?_, rfl⟩
      simp [output, received, timely, PMF.seqHistory_snoc, Fin.snoc_zero]

end CslibFrontierTests.DiscreteDeadline
