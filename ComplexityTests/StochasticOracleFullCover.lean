/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.RationalFullCover
import Complexity.Probability.StochasticOracle.ExecutionFeasibility
import Complexity.Probability.StochasticOracle.RandomCost
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# Complete full-cover policy clients

The two-oracle deadline example is from [Wang2027], PDF p. 8. Additional clients
check internal randomization after failure, a genuinely mixed LP optimum, exact
rational program semantics, an infeasible positive target with zero turns and
random billed costs correlated with the current batch's success.
-/

noncomputable section
open Finset MeasureTheory Cslib Cslib.Probability
open Cslib.Optimization.OneConstraint Cslib.Probability.StochasticOracle
namespace ComplexityTests.StochasticOracleFullCover

/-- The paper's fast cheap oracle and slower-costly alternative, indexed by Boolean roles. -/
def exampleInput : FullCoverInstance Bool ℚ where
  success b := if b then 4 / 5 else 1 / 2
  success_pos b := by cases b <;> norm_num
  success_lt_one b := by cases b <;> norm_num
  cost b := if b then 1 else 5
  cost_pos b := by cases b <;> norm_num
  cutoff b := if b then 2 else 1
  cutoff_pos b := by cases b <;> norm_num

/-- Query the cheap high-success call first and pay for the second only on failure. -/
def twoCalls : Plan Bool 2 := ({true},({false},()))

example : Plan.success exampleInput twoCalls = 9 / 10 ∧
    Plan.expectedCost exampleInput twoCalls = 2 := by
  norm_num [twoCalls, Plan.success, Plan.failure, Plan.expectedCost,
    FullCoverInstance.batchFailure, FullCoverInstance.batchCost, exampleInput]

example : Plan.Feasible exampleInput twoCalls 3 ∧ ¬ Plan.Feasible exampleInput twoCalls 2 := by
  norm_num [Plan.Feasible, twoCalls, Plan.NoReuse, Plan.used, Plan.duration,
    FullCoverInstance.batchDuration, exampleInput, disjoint_singleton_left]

example : exampleInput.batchCost univ = 6 ∧ exampleInput.batchDuration univ = 2 := by
  norm_num [FullCoverInstance.batchCost, FullCoverInstance.batchDuration, exampleInput,
    Fintype.sum_bool, show (univ : Finset Bool) = {false,true} by decide]

/-- Randomize only after a real failed call, remembering the selected continuation. -/
def afterFailurePolicy : Policy Bool ℚ 2 :=
  .issue {true} (.random (pair true false (1 / 2) (by norm_num) (by norm_num))
    (fun b => if b then .issue {false} (.halt 0) else .halt 1))

example : (afterFailurePolicy.execution exampleInput).mean executionSuccess = 17 / 20 ∧
    (afterFailurePolicy.execution exampleInput).mean (executionCost exampleInput) = 3 / 2 := by
  rw [(execution_equivalence exampleInput afterFailurePolicy).1,
    (execution_equivalence exampleInput afterFailurePolicy).2]
  norm_num [afterFailurePolicy, Policy.scheduleLaw, Distribution.mean_map,
    Distribution.mean_bind, pair_mean, Distribution.mean_pure, Function.comp_def,
    Plan.success, Plan.failure, Plan.expectedCost, Plan.empty,
    FullCoverInstance.batchFailure, FullCoverInstance.batchCost, exampleInput]

example :
    ((preselect afterFailurePolicy.scheduleLaw).execution exampleInput).mean executionSuccess =
      (afterFailurePolicy.execution exampleInput).mean executionSuccess ∧
    ((preselect afterFailurePolicy.scheduleLaw).execution exampleInput).mean
        (executionCost exampleInput) =
      (afterFailurePolicy.execution exampleInput).mean (executionCost exampleInput) :=
  preselection_equivalent exampleInput afterFailurePolicy

private theorem feasible_example :
    (followPlan (K := ℝ) twoCalls).Feasible exampleInput.realify 3 := by
  classical
  intro B hB
  rw [followPlan_law, Distribution.mem_support_pure] at hB
  subst B
  have hmem : twoCalls ∈ feasiblePlans exampleInput 2 3 := by
    norm_num [feasiblePlans, Plan.Feasible, twoCalls, Plan.NoReuse, Plan.used, Plan.duration,
      FullCoverInstance.batchDuration, exampleInput, disjoint_singleton_left]
  exact (mem_filter.mp ((feasiblePlans_realify_iff exampleInput 3 twoCalls).mpr hmem)).2

/-- Existence of an optimal actual program, against every real-randomized policy,
with heterogeneous positive probabilities, costs and deadlines. -/
example : ∃ π : Policy Bool ℝ 2,
    ∃ program : ProbOracleComp (fun _ : Finset Bool => Bool) (Bool × Plan Bool 2),
      programLaw exampleInput.realify program = (π.execution exampleInput.realify).toPMF ∧
      π.Feasible exampleInput.realify 3 ∧ π.scheduleLaw.support.card ≤ 2 ∧
      (9 / 10 : ℝ) ≤ (π.execution exampleInput.realify).mean executionSuccess ∧
      ∀ ψ : Policy Bool ℝ 2, ψ.Feasible exampleInput.realify 3 →
        (9 / 10 : ℝ) ≤ (ψ.execution exampleInput.realify).mean executionSuccess →
        (π.execution exampleInput.realify).mean (executionCost exampleInput.realify) ≤
          (ψ.execution exampleInput.realify).mean (executionCost exampleInput.realify) := by
  have hfeas : ∃ π : Policy Bool ℝ 2, π.Feasible exampleInput.realify (3 : ℚ) ∧
      ((9 / 10 : ℚ) : ℝ) ≤ (π.execution exampleInput.realify).mean executionSuccess := by
    refine ⟨followPlan twoCalls,feasible_example,?_⟩
    rw [(execution_equivalence exampleInput.realify _).1, followPlan_law,
      Distribution.mean_pure, Plan.success_realify]
    norm_num [twoCalls, Plan.success, Plan.failure, FullCoverInstance.batchFailure, exampleInput]
  have h := optimal_rational_program (n := 2) exampleInput 3 (9 / 10) hfeas
  norm_num at h
  simpa using h

example (π : Policy Bool ℝ 2) (hπ : π.Feasible exampleInput.realify 3)
    (e : Bool × Plan Bool 2) (he : e ∈ (π.execution exampleInput.realify).support) :
    e.2.Feasible exampleInput.realify 3 := execution_feasible _ π 3 hπ e he

example (π : Policy Bool ℝ 0) :
    ¬ (1 / 10 : ℝ) ≤ (π.execution exampleInput.realify).mean executionSuccess := by
  rw [(execution_equivalence exampleInput.realify π).1]
  norm_num [Distribution.mean, Plan.success, Plan.failure]

/-- The target strictly between pure-success endpoints requires actual randomization. -/
def mixed : Distribution Bool ℚ := pair true false (1 / 3) (by norm_num) (by norm_num)

example : mixed.mean (fun b => if b then 1 else 0) = 1 / 3 ∧
    mixed.mean (fun b => if b then 2 else 0) = 2 / 3 := by
  norm_num [mixed, pair_mean]

example (v : Distribution Bool ℝ)
    (hv : (1 / 3 : ℝ) ≤ v.mean (fun b => if b then 1 else 0)) :
    ((mixed.mean (fun b => if b then 2 else 0) : ℚ) : ℝ) ≤
      v.mean (fun b => if b then 2 else 0) := by
  have hfun : (fun b : Bool => if b then (2 : ℝ) else 0) =
      (fun b => 2 * (if b then 1 else 0)) := by
    funext b
    cases b <;> norm_num
  have hval : ((mixed.mean (fun b => if b then 2 else 0) : ℚ) : ℝ) = 2 / 3 := by
    norm_num [mixed,pair_mean]
  rw [hval,hfun,Distribution.mean_mul]
  linarith

example : ∃ sampler : ProbComp Bool, ProbComp.eval sampler = mixed.realify.toPMF :=
  sample_two mixed (pair_support_card _ _ _ _ _)

example : (ProbComp.eval (ProbComp.rationalCoin (2 / 7) (by norm_num) (by norm_num)) true).toReal =
    (2 / 7 : ℝ) := by rw [ProbComp.rationalCoin_true]; norm_num

example : (ProbComp.eval (ProbComp.rationalCoin 0 (by norm_num) (by norm_num)) true).toReal =
    0 := by
  rw [ProbComp.rationalCoin_true]; norm_num

example : (ProbComp.eval (ProbComp.rationalCoin 1 (by norm_num) (by norm_num)) false).toReal =
    0 := by
  rw [ProbComp.rationalCoin_false]; norm_num

section RandomBilling

local instance : MeasurableSpace Bool := ⊤

/-- Uniform success flag, also controlling the realized billed amount. -/
def billingLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure billingLaw :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype Bool).toMeasure)

/-- A single call with mean cost three; realized charges below will be two and four. -/
def billedInput : FullCoverInstance Unit ℝ where
  success _ := 1 / 2
  success_pos _ := by norm_num
  success_lt_one _ := by norm_num
  cost _ := 3
  cost_pos _ := by norm_num
  cutoff _ := 1
  cutoff_pos _ := by norm_num

/-- The same reached call costs more on success. -/
def correlatedBill (_ : Fin 1) (success : Bool) : ℝ := if success then 4 else 2

example : (∫ ω, ∑ t : Fin 1, correlatedBill t ω ∂billingLaw) = 3 := by
  have hcost : ∀ (t : Fin 1) (A : Finset Unit),
      (∫ ω in {ω : Bool | ({()} : Finset Unit) = A}, correlatedBill t ω ∂billingLaw) =
        billingLaw.real {ω : Bool | ({()} : Finset Unit) = A} * billedInput.batchCost A := by
    intro t A
    by_cases hA : A = {()}
    · subst A
      simp only [Set.ofPred_true, Measure.restrict_univ, probReal_univ,
        one_mul]
      rw [billingLaw, _root_.PMF.integral_eq_sum]
      norm_num [Fintype.sum_bool, correlatedBill, PMF.uniformOfFintype_apply,
        FullCoverInstance.batchCost, billedInput]
    · have hn : ({()} : Finset Unit) ≠ A := Ne.symm hA
      simp [hn]
  have h := expected_bills_eq_batch_costs billingLaw billedInput 1
    (fun _ _ => {()}) (fun _ _ => (Set.toFinite _).measurableSet)
    correlatedBill (fun _ => Integrable.of_finite) hcost
  have hprob (A : Finset Unit) : billingLaw.real {ω : Bool | ({()} : Finset Unit) = A} =
      if A = {()} then 1 else 0 := by
    by_cases hA : A = {()}
    · subst A
      have hs : {ω : Bool | ({()} : Finset Unit) = {()}} = Set.univ :=
        Set.eq_univ_of_forall (fun _ => rfl)
      rw [hs, probReal_univ, ite_eq_left rfl]
    · have hn : ({()} : Finset Unit) ≠ A := Ne.symm hA
      simp [hn,hA]
  simpa [hprob, ite_mul, FullCoverInstance.batchCost, billedInput] using h

end RandomBilling

end ComplexityTests.StochasticOracleFullCover
