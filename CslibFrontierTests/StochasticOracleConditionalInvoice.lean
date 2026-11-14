/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeResidualRealMinima
import CslibFrontier.Probability.StochasticOracle.NativeResidualPathCost
import CslibFrontier.Computability.Probabilistic.NativeQueryAll
import CslibFrontier.Probability.FiniteTable.Expectation
import CslibFrontierTests.StochasticOracleResidualCover
import Mathlib.Tactic

/-!
# Conditional invoice kernels with correlated natural token reports

The source history changes the joint invoice distribution without changing any
conditional batch mean: the initial invoice is deterministic, while later calls
share a fair zero-or-two multiplier. A second example correlates the near invoice
with the newly drawn residual, so its mean is fixed only before that response.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleConditionalInvoice
open Cslib.Probability StochasticOracle NativeRetention ResidualCover ConcurrentBatch
open Cslib.Optimization.OneConstraint
open MeasureTheory
open scoped ENNReal

private def unit : Parameters 5 where
  missing := StochasticOracleResidualCover.parameters.missing
  full_support := StochasticOracleResidualCover.parameters.full_support
  nearCost := 1
  near_pos := by norm_num
  specialistCost _ := 1
  specialist_pos _ := by norm_num

private def coin : Distribution Bool ℝ where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num

/-- Every selected coordinate is charged together, so the coordinates are correlated. -/
private def sharedCoin : PMF (Fin 6 → ℕ) :=
  coin.toPMF.map fun b _ => if b then 2 else 0

private theorem unit_batchCost (A : ResidualCover.Batch 5) : batchCost unit A = A.card := by
  rw [batchCost_eq_sum]
  have h : (fun i : Option (Fin 5) => i.elim unit.nearCost unit.specialistCost) =
      fun _ => (1 : ℝ) := by
    funext i
    cases i <;> rfl
  rw [h]
  simp

private theorem sharedCoin_hasMean : NativeResidualInvoice.HasMean unit sharedCoin := by
  intro A
  rw [sharedCoin, PMF.tsum_map_mul, unit_batchCost]
  have h := Distribution.ofReal_mean coin
    (fun b => (NativeResidualOracle.invoiceCost (fun _ : Fin 6 => if b then 2 else 0) A : ℝ))
    (fun _ => by positivity)
  simp only [ENNReal.ofReal_natCast] at h
  rw [← h]
  congr 1
  norm_num [Distribution.mean, coin, NativeResidualOracle.invoiceCost]
  ring

/-- All accepted receipts, including prior invoices, are available to this kernel. -/
private def historyKernel : NativeResidualConditionalInvoice.Kernel 5 :=
  fun history _ _ => if history = [] then PMF.pure (fun _ => 1) else sharedCoin

private theorem historyKernel_hasMean :
    NativeResidualConditionalInvoice.HasMean unit historyKernel := by
  apply NativeResidualConditionalInvoice.hasMean_of_residual_mean
  intro history batch r
  have hmean : NativeResidualInvoice.HasMean unit
      (if history = [] then PMF.pure (fun _ : Fin 6 => 1) else sharedCoin) := by
    split_ifs
    · exact NativeResidualInvoice.hasMean_pure unit _ fun i => by
        cases h : finSuccEquiv 5 i <;> simp [unit]
    · exact sharedCoin_hasMean
  exact hmean (NativeResidualOracle.calls batch)

-- The primitive mean is derived for every history and batch, including arbitrary
-- query bytes. Neither total policy cost nor a conditional representation is assumed.
example : NativeResidualConditionalInvoice.HasMean unit historyKernel := historyKernel_hasMean

-- The second law is genuinely random and differs from the initial unit invoice.
private theorem sharedCoin_zero : (sharedCoin.map fun f => f 0) 0 = 1 / 2 := by
  simp [sharedCoin, PMF.map_comp, coin, Distribution.toPMF, PMF.map_apply,
    tsum_fintype]

example (history : List (Exchange 6)) (batch : ConcurrentBatch.Batch 6)
    (r : Option (Fin 5)) (hh : history ≠ []) :
    historyKernel history batch r = sharedCoin := by simp [historyKernel, hh]

-- An actual receipt changes the kernel; the history argument is not ignored.
example (receipt : Exchange 6) (batch : ConcurrentBatch.Batch 6) (r : Option (Fin 5)) :
    historyKernel [] batch r ≠ historyKernel [receipt] batch r := by
  intro h
  have he := congrArg (fun μ : PMF (Fin 6 → ℕ) => (μ.map fun f => f 0) 0) h
  simp only [historyKernel, List.cons_ne_nil, ite_false, ite_true, PMF.pure_map,
    PMF.pure_apply, zero_ne_one] at he
  rw [sharedCoin_zero] at he
  apply ENNReal.inv_ne_zero.mpr (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  simpa only [one_div] using he.symm

private def three : Parameters 3 where
  missing :=
    { weight := fun _ => 1 / 3
      nonneg := by intro _; norm_num
      total := by norm_num }
  full_support _ := by norm_num
  nearCost := 1
  near_pos := by norm_num
  specialistCost _ := 1
  specialist_pos _ := by norm_num

/-- The near invoice reveals the newly sampled residual numerically as well as
through the ordinary cover response. Specialists still cost one. -/
private def residualInvoice (r : Option (Fin 3)) : Fin 4 → ℕ :=
  Fin.cases (r.elim 1 Fin.val) (fun _ => 1)

private def residualKernel : NativeResidualConditionalInvoice.Kernel 3 :=
  fun _ _ r => PMF.pure (residualInvoice r)

private theorem residual_mean_coordinate (A : ResidualCover.Batch 3)
    (i : Option (Fin 3)) (hi : i ∈ A) :
    (reply three A).mean (fun r =>
      (residualInvoice r ((finSuccEquiv 3).symm i) : ℝ)) = 1 := by
  cases i with
  | none =>
    simp only [reply, hi, ite_true]
    rw [Distribution.mean_map]
    norm_num [Distribution.mean, three, residualInvoice, Fin.sum_univ_succ]
  | some j =>
    have h : (fun r => (residualInvoice r ((finSuccEquiv 3).symm (some j)) : ℝ)) =
        fun _ => (1 : ℝ) := by
      funext r
      simp [residualInvoice]
    rw [h, Distribution.mean_const]

private theorem residualKernel_hasMean :
    NativeResidualConditionalInvoice.HasMean three residualKernel := by
  intro history batch
  simp only [residualKernel, PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  have he := Distribution.ofReal_mean (reply three (NativeResidualOracle.calls batch))
    (fun r => (NativeResidualOracle.invoiceCost (residualInvoice r)
      (NativeResidualOracle.calls batch) : ℝ)) (fun _ => by positivity)
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he]
  congr 1
  rw [batchCost_eq_sum]
  simp only [NativeResidualOracle.invoiceCost, Nat.cast_sum, Distribution.mean,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := residual_mean_coordinate (NativeResidualOracle.calls batch) i hi
  cases i <;> simpa only [Distribution.mean, three, Option.elim_none, Option.elim_some] using hm

example : NativeResidualConditionalInvoice.HasMean three residualKernel :=
  residualKernel_hasMean

-- A mean conditional on each residual would exclude this valid calibrated law:
-- on residual zero the near invoice is zero, whereas its declared price is one.
example (history : List (Exchange 4)) (batch : ConcurrentBatch.Batch 4) :
    ∑' f, residualKernel history batch (some 0) f * (f 0 : ℝ≥0∞) = 0 := by
  simp [residualKernel, residualInvoice]

example (history : List (Exchange 4)) (batch : ConcurrentBatch.Batch 4) :
    ∑' f, residualKernel history batch (some 2) f * (f 0 : ℝ≥0∞) = 2 := by
  simp [residualKernel, residualInvoice]

private abbrev blocks := StochasticOracleResidualCover.blocks
private def points : Fin (Fintype.card (Point blocks)) ≃ Point blocks :=
  (Fintype.equivFin _).symm
private def candidates : Fin (Fintype.card (Candidate blocks)) ≃ Candidate blocks :=
  (Fintype.equivFin _).symm

private def limits : Limits 6 := ⟨fun _ => 1, by intro _; norm_num, 2, 2⟩
private def nearBatch : ConcurrentBatch.Batch 6 :=
  ⟨fun i => if i = 0 then some (NativeResidualOracle.query blocks points candidates 0) else none,
    ⟨0, by simp [active]⟩⟩
private def memory : NativeOpenExecution.Memory Unit (ServerState 6 Unit) :=
  ⟨ConcurrentBatch.initial (), []⟩

-- This actual native reader sends the original-instance near request and reads
-- its full correlated report. The initial source history is empty.
example (turns : ℕ) :
    NativeBatch.Quantitative.expected limits
      (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel)
      (NativeQueryAll.machine () 0) (NativeResidualInvoice.score unit) turns
      (NativeQueryAll.start () 0 (encodeBatch nearBatch) memory) =
    NativeBatch.Quantitative.expected limits
      (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel)
      (NativeQueryAll.machine () 0) NativeBatch.Trace.charge turns
      (NativeQueryAll.start () 0 (encodeBatch nearBatch) memory) :=
  NativeResidualConditionalInvoice.expected_score_eq_charge blocks points candidates unit
    limits historyKernel historyKernel_hasMean _ _ _

-- Every admitted native sure-success competitor pays at least two in expectation
-- on the same history-dependent oracle. The premise is ordinary certified source
-- success, not a behavioral representation or an expected-cost certificate.
example {k : ℕ} {Control : Type} {input : List Bool}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (world : NativeOpenExecution.World k Control Unit (ServerState 6 Unit) input)
    (hi : NativeBatch.Invariant limits world.memory)
    (hzero : world.memory.privateState.history = [])
    (hadmit : NativeUnboundedExecution.SelectionOnly machine
      (environment limits
        (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel))
      (NativeBatch.candidateParser (n := 6) (Fintype.card (Candidate blocks)))
      (decodeFamily (Fintype.card (Candidate blocks)))
      (NativeResidualPolicies.optimalAccept blocks candidates (by norm_num)) world)
    (hsuccess : ((NativeUnboundedExecution.terminal machine
      (environment limits
        (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel))
      world).map (fun result => decide (optimalOutput (T := blocks) (by norm_num)
        (NativeResidualPolicies.terminalOutput blocks candidates result) = 1))) true = 1) :
    2 ≤ NativeBatch.Quantitative.expected limits
      (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel)
      machine NativeBatch.Trace.charge 3 world := by
  have h := NativeResidualPolicies.native_two_lower blocks points candidates unit limits
    historyKernel machine world hi hzero rfl (by norm_num) historyKernel_hasMean hadmit hsuccess
  have hm : unit.missing.mean unit.specialistCost = 1 :=
    Distribution.mean_const unit.missing 1
  rw [hm] at h
  norm_num [unit, limits] at h ⊢
  exact h

-- The compiled adaptive strategy attains the lower bound on a genuinely changing
-- history-dependent invoice law, starting from the original encoded WSC instance.
example : NativeRetention.BatchOptimum.optimum NativeResidualAttainment.limits
    (NativeResidualConditionalInvoice.sample blocks points candidates unit historyKernel)
    (NativeResidualAttainment.input blocks points candidates) ()
    (NativeResidualAttainment.valid blocks points candidates (by norm_num)) 1 = 2 := by
  have h := NativeResidualRealMinima.native_optimum_conditional blocks points candidates
    unit historyKernel historyKernel_hasMean (by norm_num)
  have hm : unit.missing.mean unit.specialistCost = 1 := Distribution.mean_const unit.missing 1
  rw [hm] at h
  norm_num [unit] at h
  exact h

private def blocksThree : Fin 3 → Block := fun _ => StochasticOracleResidualCover.block
private def pointsThree : Fin (Fintype.card (Point blocksThree)) ≃ Point blocksThree :=
  (Fintype.equivFin _).symm
private def candidatesThree : Fin (Fintype.card (Candidate blocksThree)) ≃ Candidate blocksThree :=
  (Fintype.equivFin _).symm

-- Here the near invoice depends on J and does not have its declared mean on each
-- response branch. Both native optima and their ratio are nevertheless attained.
example : NativeRetention.BatchOptimum.optimum NativeResidualAttainment.limits
    (NativeResidualConditionalInvoice.sample blocksThree pointsThree candidatesThree
      three residualKernel)
    (NativeResidualAttainment.input blocksThree pointsThree candidatesThree) ()
    (NativeResidualAttainment.valid blocksThree pointsThree candidatesThree (by norm_num)) 1 =
      2 := by
  have h := NativeResidualRealMinima.native_optimum_conditional blocksThree pointsThree
    candidatesThree three residualKernel residualKernel_hasMean (by norm_num)
  have hm : three.missing.mean three.specialistCost = 1 :=
    Distribution.mean_const three.missing 1
  rw [hm] at h
  norm_num [three] at h
  exact h

example :
    (NativeRetention.BatchOptimum.optimum (NativeResidualAll.config 1)
      (NativeResidualConditionalInvoice.sample blocksThree pointsThree candidatesThree
        three residualKernel)
      (NativeResidualAttainment.input blocksThree pointsThree candidatesThree) ()
      (NativeResidualAttainment.valid blocksThree pointsThree candidatesThree (by norm_num))
      1).toReal /
    (NativeRetention.BatchOptimum.optimum NativeResidualAttainment.limits
      (NativeResidualConditionalInvoice.sample blocksThree pointsThree candidatesThree
        three residualKernel)
      (NativeResidualAttainment.input blocksThree pointsThree candidatesThree) ()
      (NativeResidualAttainment.valid blocksThree pointsThree candidatesThree (by norm_num))
      1).toReal =
        (3 : ℝ) / 2 := by
  have h := NativeResidualRealMinima.native_ratio_conditional blocksThree pointsThree
    candidatesThree three residualKernel residualKernel_hasMean (by norm_num)
    1 1 (by norm_num) (fun _ => rfl) (by norm_num [three])
  norm_num at h
  exact h

private def pricesThree : NativeResidualCostChoice.Prices :=
  ⟨1, List.ofFn (fun _ : Fin 3 => ⟨1 / 3, 1⟩)⟩
private def pricesThree_reflects : NativeResidualCostChoice.Reflects pricesThree three where
  rows _ := ⟨1 / 3, 1⟩
  entries := rfl
  near := by norm_num [pricesThree, three]
  probability _ := by norm_num [three]
  price _ := by norm_num [three]

-- The single price-aware compiled program also attains OPT on the coupled law;
-- its rational metadata contains declared means, not realized natural invoices.
example : NativeBatch.Quantitative.expected NativeResidualAttainment.limits
    (NativeResidualConditionalInvoice.sample blocksThree pointsThree candidatesThree
      three residualKernel)
    NativeResidualCostChoice.controller.program NativeBatch.Trace.charge 3
    ⟨NativeResidualCostChoice.controller.program.initialConfig
      (NativeResidualCostChoice.encoding
        ⟨NativeResidualAttainment.input blocksThree pointsThree candidatesThree, pricesThree⟩),
      NativeResidualAttainment.initialMemory⟩ = 2 := by
  rw [NativeResidualRealChoice.native_expected_cost_conditional blocksThree pointsThree
    candidatesThree three residualKernel residualKernel_hasMean (by norm_num)
    pricesThree pricesThree_reflects]
  have hm : three.missing.mean three.specialistCost = 1 :=
    Distribution.mean_const three.missing 1
  rw [hm]
  norm_num [three]

-- This is the actual infinite source-epoch path measure and its total invoice
-- series, not terminal billing substituted under an assumed integrability claim.
example : (∫ ω, (NativeBatch.PathCost.totalBill NativeBatch.Trace.charge ω).toReal
    ∂NativeResidualPathCost.executionConditional blocksThree pointsThree candidatesThree
      three residualKernel pricesThree) = 2 := by
  have h := (NativeResidualPathCost.integrable_totalBill_conditional blocksThree pointsThree
    candidatesThree three residualKernel residualKernel_hasMean (by norm_num)
    pricesThree pricesThree_reflects).2.2
  have hm : three.missing.mean three.specialistCost = 1 :=
    Distribution.mean_const three.missing 1
  rw [hm] at h
  norm_num [three] at h
  exact h

end CslibFrontierTests.StochasticOracleConditionalInvoice
