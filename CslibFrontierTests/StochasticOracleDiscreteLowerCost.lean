/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.LowerCost
import CslibFrontierTests.StochasticOracleDiscreteRetention
import CslibFrontierTests.StochasticOracleSelectionPolicy
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic

/-!
# Non-retaining competitors and fabricated failed outputs

The oracle proposes the cheap and expensive original sets together. Local
retention rejects the bundle, but the competitor buffers it and may extract the
cheap certified singleton. It may instead halt before querying or return the
expensive failed singleton without ever receiving it. Geometric responses carry
unbounded invoices. Failed fabricated masks satisfy the successful-only contract.
-/

noncomputable section
namespace CslibFrontierTests.DiscreteLowerCost
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory
open StochasticOracleSelectionPolicyTests (bufferedInstance)
open scoped ENNReal

private def propose (_ : List (Record Unit ℕ)) (_ : Unit) (_ : ℕ) :
    List (Finset Bool) := [Finset.univ]
private def respond (_ : List (Record Unit ℕ)) (_ : Unit) : PMF ℕ := DiscreteRetention.law []
private def choose (h : List (Record Unit ℕ)) : PMF (Option Unit) :=
  if h.any Option.isSome then PMF.pure none
  else (PMF.uniformOfFintype Bool).map fun b => if b then some () else none
private def output (h : List (Record Unit ℕ)) : PMF (Finset Bool) :=
  if h.any Option.isSome then (PMF.uniformOfFintype Bool).map fun b => {b}
  else PMF.pure {false}
private def charge (fee : ℕ → ℝ) (_ : List (Record Unit ℕ)) (_ : Unit) (x : ℕ) : ℝ := fee x
private def duration (_ : List (Record Unit ℕ)) (_ : Unit) (_ : ℕ) : ℝ := 1

private theorem proposed_eq (h : List (Record Unit ℕ)) :
    proposedSets (recordProposals propose) h = if h.any Option.isSome then Finset.univ else ∅ := by
  induction h with
  | nil => simp [proposedSets]
  | cons z h ih =>
    cases z <;> cases hz : h.any Option.isSome <;>
      simp [proposedSets, recordProposals, propose, ih, hz]

private theorem bad_not_certified (h : List (Record Unit ℕ)) :
    ¬CertifiedOutput bufferedInstance 1 1 duration h {false} := by
  intro hs
  have hc := hs.2.1
  norm_num [Instance.cost, bufferedInstance] at hc

private theorem envelopes (fee : ℕ → ℝ) (hn : ∀ x, 0 ≤ fee x)
    (hm : (2 : ℝ≥0∞) ≤ ∑' x, DiscreteRetention.law [] x * ENNReal.ofReal (fee x))
    (u : ℕ) :
    Discrete.LowerBounds bufferedInstance propose choose respond output (charge fee) duration
      u 1 1 2 1 1 where
  charge_nonneg := by intro h i x; exact hn x
  progress := by intro t ht h hh hs i hi; exact PMF.toOuterMeasure_toReal_le_one _ _
  coverage := by
    intro t ht h hh hs i hi x hx
    simpa using Finset.card_le_card (Finset.subset_univ
      (revealed bufferedInstance (recordProposals propose) (some (i, x) :: PMF.seqHistory h) \
        revealed bufferedInstance (recordProposals propose) (PMF.seqHistory h)))
  cost := by intro t ht h hh hs i hi; simpa [respond, charge] using hm
  provenance := by
    intro h hh C hC hs
    by_cases ha : (PMF.seqHistory h).any Option.isSome = true
    · rw [proposed_eq, ite_eq_left ha]
      exact Finset.subset_univ C
    · have he : C = {false} := by simpa [output, ha] using hC
      subst C
      exact (bad_not_certified _ hs).elim

-- Actual local retention rejects the bundle that this competitor can filter.
example (x : ℕ) :
    selected bufferedInstance 1 (recordProposals propose) [some ((), x)] = ∅ := by
  norm_num [selected, recordProposals, propose, Instance.retain, Instance.Certified,
    Instance.covered, Instance.cost, bufferedInstance, Fintype.univ_bool]

private def finalStep (z : Record Unit ℕ) : PMF (Discrete.Outcome Unit ℕ Bool) :=
  (output [z]).map fun C => ⟨[z], C⟩
private def accepted : Set (Discrete.Outcome Unit ℕ Bool) :=
  {z | CertifiedOutput bufferedInstance 1 1 duration z.history z.returned}

private theorem outputLaw_one : Discrete.outputLaw choose respond output 1 =
    (policyLaw choose respond []).bind finalStep := by
  simp only [Discrete.outputLaw, PMF.seqProcess, PMF.pure_bind, responseStep,
    PMF.seqHistory_zero, PMF.bind_map, Function.comp_def, PMF.seqHistory_snoc]
  rfl

private theorem final_none : (finalStep none).toOuterMeasure accepted = 0 := by
  simp [finalStep, output, PMF.toOuterMeasure_pure_apply, accepted, bad_not_certified]

private theorem final_some (x : ℕ) :
    (finalStep (some ((), x))).toOuterMeasure accepted = 1 / 2 := by
  simp only [finalStep, output, List.any_cons, List.any_nil, Option.isSome_some,
    Bool.or_false, ite_true]
  rw [PMF.map_comp, PMF.toOuterMeasure_map_apply]
  have he : ((fun C => (⟨[some ((), x)], C⟩ : Discrete.Outcome Unit ℕ Bool)) ∘
      (fun b => ({b} : Finset Bool))) ⁻¹' accepted = {true} := by
    ext b
    cases b <;> norm_num [accepted, CertifiedOutput, Instance.covered, Instance.cost,
      bufferedInstance, accruedBill, recordResource, duration]
  rw [he, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  norm_num

private theorem call_success :
    (((respond [] ()).map fun x => some ((), x)).bind finalStep).toOuterMeasure accepted =
      1 / 2 := by
  rw [PMF.bind_map, PMF.toOuterMeasure_bind_apply]
  simp_rw [Function.comp_apply, final_some]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

private theorem actual_success :
    (Discrete.outputLaw choose respond output 1).toOuterMeasure accepted = 1 / 4 := by
  rw [outputLaw_one, policyLaw, ite_eq_right List.not_mem_nil]
  rw [choose]
  simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [PMF.bind_bind, PMF.bind_map, PMF.toOuterMeasure_bind_apply,
    tsum_fintype, Fintype.sum_bool]
  simp only [Function.comp_apply, ite_true, Bool.false_eq_true, ite_false, PMF.pure_bind]
  rw [call_success, final_none]
  norm_num [PMF.uniformOfFintype_apply]
  rw [← pow_two, ← ENNReal.inv_pow]
  norm_num

private def halted : Fin 1 → Record Unit ℕ := Fin.snoc Fin.elim0 none

private theorem halted_support :
    halted ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) 1).support := by
  have hnone : none ∈ (policyLaw choose respond []).support := by
    rw [policyLaw, ite_eq_right List.not_mem_nil]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨none, ?_, by simp⟩
    simp only [choose, List.any_nil, Bool.false_eq_true, ite_false]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨false, by simp, rfl⟩
  rw [PMF.seqProcess]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨Fin.elim0, by simp [PMF.seqProcess], ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨none, by simpa [responseStep] using hnone, rfl⟩

-- The fabricated expensive mask really occurs on an actual reached history,
-- and cannot satisfy an all-output provenance requirement.
example : halted ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) 1).support ∧
    {false} ∈ (output (PMF.seqHistory halted)).support ∧
    ¬({false} ⊆ proposedSets (recordProposals propose) (PMF.seqHistory halted)) ∧
    ¬CertifiedOutput bufferedInstance 1 1 duration (PMF.seqHistory halted) {false} := by
  refine ⟨halted_support, ?_, ?_, bad_not_certified _⟩
  · rw [halted, PMF.seqHistory_snoc]
    simp [output]
  · rw [halted, PMF.seqHistory_snoc]
    simp [proposed_eq]

private theorem bill_one (fee : ℕ → ℝ) :
    (∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) 1 h *
      ENNReal.ofReal (accruedBill (recordResource (charge fee)) (PMF.seqHistory h))) =
      (1 / 2 : ℝ≥0∞) * ∑' x, DiscreteRetention.law [] x * ENNReal.ofReal (fee x) := by
  rw [PMF.seqProcess, PMF.seqProcess, PMF.pure_bind, PMF.tsum_map_mul]
  simp only [PMF.seqHistory_snoc, PMF.seqHistory_zero, accruedBill, zero_add, responseStep]
  rw [policyLaw, ite_eq_right List.not_mem_nil, choose]
  simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [PMF.bind_map, PMF.tsum_bind_mul, tsum_fintype, Fintype.sum_bool]
  simp only [Function.comp_apply, ite_true, Bool.false_eq_true, ite_false]
  rw [PMF.tsum_map_mul]
  simp only [recordResource_some, charge]
  norm_num [PMF.uniformOfFintype_apply, PMF.pure_apply, ite_mul, respond]

-- Unbounded finite-mean invoices: success is exactly one quarter, actual bill one,
-- and the source lower theorem derives its nonzero one-half lower bound.
example :
    (1 / 2 : ℝ≥0∞) ≤
      ∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) 1 h *
        ENNReal.ofReal (accruedBill (recordResource (charge (DiscreteRetention.charge [])))
          (PMF.seqHistory h)) := by
  have H := envelopes (DiscreteRetention.charge []) (fun x => by
    dsimp [DiscreteRetention.charge]
    positivity) (by simpa using (DiscreteRetention.charge_mean []).ge) 1
  have hb := Discrete.lower_cost bufferedInstance propose choose respond output
    (charge (DiscreteRetention.charge [])) duration 1 1 1
    (by
      intro k hk
      have he : k = 0 := by omega
      subst k
      norm_num [bufferedInstance])
    1 2 1 1 (1 / 4) (by norm_num) (by norm_num) (by norm_num) H
    (by simpa [accepted] using actual_success.ge)
  norm_num [ENNReal.ofReal_div_of_pos] at hb ⊢
  exact hb

example :
    (∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) 1 h *
      ENNReal.ofReal (accruedBill (recordResource (charge (DiscreteRetention.charge [])))
        (PMF.seqHistory h))) = 1 := by
  rw [bill_one, DiscreteRetention.charge_mean, one_div,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

example (N : ℕ) : ∃ z ∈ (policyLaw choose respond []).support,
    (N : ℝ) < recordResource (charge (DiscreteRetention.charge [])) [] z := by
  refine ⟨some ((), N + 1), ?_, ?_⟩
  · apply (mem_support_policyLaw_some choose respond [] () (N + 1)).mpr
    refine ⟨List.not_mem_nil, ?_, ne_of_gt (DiscreteRetention.law_pos _)⟩
    simp only [choose, List.any_nil, Bool.false_eq_true, ite_false]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨true, by simp, rfl⟩
  · simp only [recordResource_some, charge, DiscreteRetention.charge, Nat.cast_add, Nat.cast_one]
    linarith

private theorem exponential_mean :
    (∑' x, DiscreteRetention.law [] x * ENNReal.ofReal ((2 : ℝ) ^ x)) = ⊤ := by
  have he (x : ℕ) : DiscreteRetention.law [] x * ENNReal.ofReal ((2 : ℝ) ^ x) = 1 / 2 := by
    rw [DiscreteRetention.law_apply, ← ENNReal.ofReal_mul (by positivity)]
    have hx : (1 / 2 : ℝ) ^ x * (1 / 2) * 2 ^ x = 1 / 2 := by
      calc
        _ = ((1 / 2 : ℝ) * 2) ^ x * (1 / 2) := by rw [mul_pow]; ring
        _ = 1 / 2 := by norm_num
    rw [hx, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  simp_rw [he]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

-- Infinite expected invoices are admitted, rather than ruled out by a hidden
-- finite-expectation premise. Every realized exponential invoice is still finite.
example : Discrete.LowerBounds bufferedInstance propose choose respond output
    (charge (fun x => (2 : ℝ) ^ x)) duration 1 1 1 2 1 1 := by
  apply envelopes _ (fun x => by positivity)
  rw [exponential_mean]
  exact le_top

example :
    (∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) 1 h *
      ENNReal.ofReal (accruedBill (recordResource (charge (fun x => (2 : ℝ) ^ x)))
        (PMF.seqHistory h))) = ⊤ := by
  rw [bill_one, exponential_mean]
  norm_num

end CslibFrontierTests.DiscreteLowerCost
