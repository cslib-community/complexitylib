/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverNativeExecution
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.FiniteGround
import Mathlib.Tactic

/-!
# Native billing against the source certified-risk optimum

[Wang2027], Theorem 4, PDF pp. 10–11. The objective ranges over every
risk-feasible repeated-call list from the original oracle table. Its infimum
is infinity when infeasible; no optimum or lower bound is supplied by a caller.

## Main definitions

* `Benchmark`, `riskOptimum`: source certified-risk feasibility and its cost infimum.

## Main results

* `startup_live`: the source assumptions imply live startup, without a liveness premise.
* `native_bill_le_riskOptimum`: the same named native program's terminal bill is at
  most the source factor times the risk optimum, from individual accrued caps.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
open Turing NativeOpenExecution ConcurrentBatch NativeRetention
open Cslib.Algorithms.Lean Multicover
open scoped ENNReal

/-- Risk-feasible original oracle calls; repetitions are allowed and are charged. -/
def Benchmark (x : Input) (bs : List (Oracle (Fin x.planner.val.ground))) : Prop :=
  (∀ row ∈ bs, row ∈ x.planner.val.rows.map (Native.interpret x.planner.val.ground)) ∧
    (∑ e : Fin x.planner.val.ground, (x.planner.val.parameters.q : ℝ) ^
      Instance.chances e (bs.map Oracle.eligible)) ≤ x.planner.val.parameters.budget

/-- Infimum of actual source risk-feasible batch-cost bounds; empty feasibility is infinity. -/
def riskOptimum (x : Input) : ℝ≥0∞ :=
  ⨅ bs : {bs : List (Oracle (Fin x.planner.val.ground)) // Benchmark x bs},
    ENNReal.ofReal (bill bs.val : ℝ)

/-- The risk budget of the computed native plan follows from the original
eligibility cover, without a feasible-benchmark or successful-output premise. -/
theorem computed_risk (x : Input) (hx : Valid x.system)
    (hcover : ∀ e : Fin x.planner.val.ground, ∃ row ∈ x.planner.val.rows,
      row.mask[e.val]?.getD false = true) :
    (∑ e : Fin x.planner.val.ground, (x.planner.val.parameters.q : ℝ) ^
      Instance.chances e (((GreedyNative.labels x.planner).map
        (GreedyNative.oracleAt x.planner.val)).map Oracle.eligible)) ≤
      x.planner.val.parameters.budget := by
  let I := FiniteGround.instanceOf x.system hx x.planner.val.ground x.ground_eq
  have hU : I.ground.Nonempty := ⟨⟨0, x.planner.property.ground_pos⟩, Finset.mem_univ _⟩
  have hc : ∀ e, ∃ row ∈ x.planner.val.rows.map (Native.interpret x.planner.val.ground),
      e ∈ row.eligible := by
    intro e
    obtain ⟨row, hr, he⟩ := hcover e
    exact ⟨_, List.mem_map.mpr ⟨row, hr, rfl⟩, by simpa [Native.interpret] using he⟩
  apply I.multicover_implies_risk
    (by exact_mod_cast x.planner.property.parameters_valid.q_pos)
    (by exact_mod_cast x.planner.property.parameters_valid.q_lt_one)
    (by exact_mod_cast x.planner.property.parameters_valid.budget_pos) hU
  intro e _
  have hn : I.ground.card = x.planner.val.ground := by simp [I, FiniteGround.instanceOf]
  rw [hn, GreedyNative.decoded_labels_eq]
  exact batch_chances _ hc _ e

/-- Source eligibility coverage and a failure budget below one force a nonempty
computed plan and a live native startup. No execution or desired-output premise
is required. -/
theorem startup_live (x : Input) (hx : Valid x.system)
    (hcover : ∀ e : Fin x.planner.val.ground, ∃ row ∈ x.planner.val.rows,
      row.mask[e.val]?.getD false = true)
    (hδone : x.planner.val.parameters.budget < 1) :
    RuntimeControl.stopped (initial x) = false := by
  have hn : 0 < (GreedyNative.labels x.planner).length := by
    by_contra! h
    have he : GreedyNative.labels x.planner = [] := List.length_eq_zero_iff.mp (by omega)
    have hr := computed_risk x hx hcover
    simp only [he, List.map_nil, Instance.chances, List.filter_nil, List.length_nil,
      pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hr
    have hn : (1 : ℝ) ≤ x.planner.val.ground := by
      exact_mod_cast x.planner.property.ground_pos
    have hδ : (x.planner.val.parameters.budget : ℝ) < 1 := by exact_mod_cast hδone
    linarith
  have hg : x.system.dual.length ≠ 0 := by
    rw [← x.ground_eq]
    exact Nat.ne_of_gt x.planner.property.ground_pos
  simpa [RuntimeControl.stopped, initial, Nat.ne_of_gt hn, Packets.decision,
    Packets.assemble, complete, covered, ground, retain] using
      (show ∃ i, i < x.system.dual.length from ⟨0, Nat.pos_of_ne_zero hg⟩)

/-- Composed source competitive bill bound for the actual named native program.
All premises describe original input or per-call charges on possible trajectories;
no bound on total cost, integrability, optimum or desired output is assumed. -/
theorem native_bill_le_riskOptimum {P : Type} (x : Input) (hx : Valid x.system)
    (hcover : ∀ e : Fin x.planner.val.ground, ∃ row ∈ x.planner.val.rows,
      row.mask[e.val]?.getD false = true)
    (hcost : ∀ row ∈ x.planner.val.rows, 0 ≤ row.cost)
    (hδone : x.planner.val.parameters.budget < 1)
    (limits : Limits (GreedyNative.labels x.planner).length)
    (sample : Sampler (GreedyNative.labels x.planner).length P) (seed : P)
    (hd : 0 < limits.deadline) (ht : 0 < limits.turns)
    (hcap : ∀ pair ∈ (sample (ConcurrentBatch.initial seed)
      (batch x (live_nonempty x (startup_live x hx hcover hδone)))).support, ∀ i,
      ((pair.1 i).accrued (limits.cutoff i) : ℝ) ≤
        (GreedyNative.oracleAt x.planner.val ((GreedyNative.labels x.planner).get i)).cost)
    (outcome : Option (NativeReplyContext.Observation
      (ServerState (GreedyNative.labels x.planner).length P)))
    (houtcome : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample) ⟨controller.program.initialConfig (encoding x),
        ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧
      (tokenBill final.memory.events : ℝ≥0∞) ≤
        ENNReal.ofReal (Asymptotics.factor x.planner.val.parameters.q
          x.planner.val.parameters.budget x.planner.val.ground) * riskOptimum x ∧
      elapsed final.memory.events ≤ limits.deadline := by
  have hs := startup_live x hx hcover hδone
  obtain ⟨final, he, hb, hdur, _, _⟩ :=
    native_resources x limits sample seed hs hd ht hcap outcome houtcome
  have hf := Asymptotics.factor_pos
    (show (0 : ℝ) < x.planner.val.parameters.q by
      exact_mod_cast x.planner.property.parameters_valid.q_pos)
    (show (x.planner.val.parameters.q : ℝ) < 1 by
      exact_mod_cast x.planner.property.parameters_valid.q_lt_one)
    (show (0 : ℝ) < x.planner.val.parameters.budget by
      exact_mod_cast x.planner.property.parameters_valid.budget_pos)
    (show (x.planner.val.parameters.budget : ℝ) < 1 by exact_mod_cast hδone)
    x.planner.property.ground_pos
  refine ⟨final, he, ?_, hdur⟩
  rw [riskOptimum, ENNReal.mul_iInf_of_ne (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hf))
    ENNReal.ofReal_ne_top]
  apply le_iInf
  intro bs
  have hg := GreedyNative.risk_bill x.planner
    (FiniteGround.instanceOf x.system hx x.planner.val.ground x.ground_eq) rfl
    hcover hcost hδone bs.val bs.property.1 bs.property.2
  have h := ENNReal.ofReal_le_ofReal (hb.trans hg.2)
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_mul hf.le] using h

end Cslib.Probability.StochasticOracle.PartialCover.NativeExecution
