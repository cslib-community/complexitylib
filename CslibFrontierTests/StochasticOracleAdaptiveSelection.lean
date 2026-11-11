/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptivePath
public import CslibFrontierTests.StochasticOracleAdaptiveComparison
import Mathlib.Tactic

/-! Actual locally certified selection driven by correlated response kernels. -/

public section
noncomputable section
open Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover
namespace StochasticOracleAdaptiveSelectionTests

/-- A nonempty set system with a tight feasible dual and positive cost. -/
@[expose] def toy : Instance Unit Unit where
  ground := {()}
  sets := fun _ => {()}
  sets_subset := by simp
  weight := fun _ => 1
  weight_nonneg := by simp
  dual := fun _ => 1
  dual_nonneg := by simp
  dual_feasible := by simp

/-- Successful responses propose the actual singleton cover; failures propose nothing. -/
@[expose] def proposals (_ : List Bool) (x : Bool) : List (Finset Unit) :=
  if x then [{()}] else []

private theorem selected_eq (h : List Bool) :
    selected toy 1 proposals h = if true ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [selected]
  | cons x h ih =>
    cases x <;> simp only [selected, proposals, Bool.false_eq_true,
      ite_true, ite_false] <;> rw [ih] <;> by_cases hh : true ∈ h <;>
      simp [hh, Instance.retain, Instance.Certified, Instance.covered, Instance.cost, toy]

private theorem productive_eq (h : List Bool) (x : Bool) :
    productive toy 1 proposals 1 h x = (decide (true ∈ h) || x) := by
  simp only [productive, AdaptiveSelection.residual, selected_eq]
  cases x <;> by_cases hh : true ∈ h <;>
    simp [hh, Instance.covered, toy]

/-- The envelope holds at every full history, including after completion where the
productive extension is one. Actual response probabilities change after success. -/
theorem completion_bound :
    (∫ i, (if 1 ≤ i then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 2 ⟨1 / 4, by norm_num, by norm_num⟩) ≤
    historyExpectation StochasticOracleAdaptiveComparisonTests.law
      (fun h => if toy.covered (selected toy 1 proposals h) = toy.ground
        then 1 else 0) 2 [] := by
  apply binomial_le_completion toy 1 proposals _ 1 1 2 (by norm_num [toy])
  intro h
  by_cases hh : true ∈ h <;>
    simp [productive_eq, StochasticOracleAdaptiveComparisonTests.law, hh,
      Cslib.Optimization.OneConstraint.pair_mean]; norm_num

/-- The actual emitted cover succeeds with probability 7/16. Rejection, acceptance,
repeat responses, and early completion are evaluated by the selection implementation. -/
theorem actual_completion :
    historyExpectation StochasticOracleAdaptiveComparisonTests.law
      (fun h => if toy.covered (selected toy 1 proposals h) = toy.ground
        then 1 else 0) 2 [] = (7 / 16 : ℝ) := by
  have he (h : List Bool) :
      (if toy.covered (selected toy 1 proposals h) = toy.ground then (1 : ℝ) else 0) =
        if true ∈ h then 1 else 0 := by
    rw [selected_eq]
    by_cases hh : true ∈ h <;> simp [hh, Instance.covered, toy]
  simp_rw [he]
  norm_num [historyExpectation, StochasticOracleAdaptiveComparisonTests.law,
    Cslib.Optimization.OneConstraint.pair_mean]

/-- This execution is driven by a genuinely correlated law, as witnessed by the
probability of two successful oracle responses. -/
theorem two_responses :
    progressExpectation StochasticOracleAdaptiveComparisonTests.law (fun _ x => x)
      (fun k => if 2 ≤ k then 1 else 0) 2 [] 0 = (3 / 16 : ℝ) :=
  StochasticOracleAdaptiveComparisonTests.actual_tail

private theorem revealed_eq (h : List Bool) :
    revealed toy proposals h = if true ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [revealed]
  | cons x h ih =>
    cases x <;> simp only [revealed, proposals, Bool.false_eq_true,
      ite_true, ite_false] <;> rw [ih] <;> by_cases hh : true ∈ h <;>
      simp [hh, Instance.covered, toy]

/-- The universal revealed-set comparison is instantiated on the same correlated
execution, including histories after full revelation where progress is zero. -/
theorem universal_bound :
    historyExpectation StochasticOracleAdaptiveComparisonTests.law
      (fun h => if toy.ground ⊆ revealed toy proposals h then 1 else 0) 2 [] ≤
    ∫ i, (if 1 ≤ i then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 2 ⟨3 / 4, by norm_num, by norm_num⟩ := by
  apply revealed_completion_le_binomial toy proposals _ 1 1 2
  · intro k hk
    have : k = 0 := by omega
    simp [this, toy]
  · intro h x
    rw [revealed_eq, revealed_eq]
    cases x <;> by_cases hh : true ∈ h <;> simp [hh]
  · intro h
    simp only [reveals, revealed_eq]
    by_cases hh : true ∈ h <;>
      norm_num [StochasticOracleAdaptiveComparisonTests.law, hh,
        Cslib.Optimization.OneConstraint.pair_mean]

/-- Actual stopped unit billing on the correlated execution: the first turn is
issued surely and the second only after the first failure, of probability 3/4. -/
theorem stopped_unit_cost :
    executionCost StochasticOracleAdaptiveComparisonTests.law
      (fun h => if toy.covered (selected toy 1 proposals h) = toy.ground
        then 0 else 1) 2 [] = (7 / 4 : ℝ) := by
  have he (h : List Bool) :
      (if toy.covered (selected toy 1 proposals h) = toy.ground then (0 : ℝ) else 1) =
        if true ∈ h then 0 else 1 := by
    rw [selected_eq]
    by_cases hh : true ∈ h <;> simp [hh, Instance.covered, toy]
  simp_rw [executionCost, he]
  norm_num [StochasticOracleAdaptiveComparisonTests.law,
    Cslib.Optimization.OneConstraint.pair_mean]

/-- Response-level stopped billing agrees with the recursive cost calculation. -/
theorem actual_stopped_unit_cost :
    historyExpectation StochasticOracleAdaptiveComparisonTests.law
      (accruedBill (fun h _ =>
        if toy.covered (selected toy 1 proposals h) = toy.ground then 0 else 1))
      2 [] = (7 / 4 : ℝ) := by
  rw [historyExpectation_accruedBill, accruedBill, zero_add]
  simpa only [Cslib.Optimization.OneConstraint.Distribution.mean_const]
    using stopped_unit_cost

/-- Certain productivity has exactly the deterministic waiting time, including zero. -/
example (r : ℕ) : ∑' t, binomialFailure 1 r t = r := by
  simpa using tsum_binomialFailure ⟨1, by norm_num, by norm_num⟩ (by norm_num) r

/-- Positive but imperfect productivity: two required successes take eight turns in mean. -/
example : ∑' t, binomialFailure (1 / 4) 2 t = (8 : ℝ) := by
  have h := tsum_binomialFailure ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num) 2
  norm_num at h ⊢
  exact h

/-- The actual correlated response execution satisfies the horizon-uniform bill bound. -/
theorem actual_bill_bound (n : ℕ) :
    historyExpectation StochasticOracleAdaptiveComparisonTests.law
      (accruedBill (fun h _ =>
        if toy.covered (selected toy 1 proposals h) = toy.ground then 0 else 1))
      n [] ≤ (4 : ℝ) := by
  have h := accruedBill_le_mean toy 1 proposals
    StochasticOracleAdaptiveComparisonTests.law 1 1 n (by norm_num [toy])
    ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num) (by
      intro h
      by_cases hh : true ∈ h <;>
        simp [productive_eq, StochasticOracleAdaptiveComparisonTests.law, hh,
          Cslib.Optimization.OneConstraint.pair_mean]; norm_num)
    (fun h _ => if toy.covered (selected toy 1 proposals h) = toy.ground then 0 else 1)
    1 (by norm_num) (by
      intro h
      simp only [Cslib.Optimization.OneConstraint.Distribution.mean_const, one_mul, le_refl])
  norm_num at h ⊢
  exact h

/-- The correlated actual response law eventually retains the singleton cover. -/
theorem actual_ae_completion :
    ∀ᵐ ω ∂responseMeasure StochasticOracleAdaptiveComparisonTests.law,
      ∀ᶠ n in Filter.atTop,
        toy.covered (selected toy 1 proposals (responseHistory ω n)) = toy.ground := by
  apply ae_eventually_complete toy 1 proposals
    StochasticOracleAdaptiveComparisonTests.law 1 1 (by norm_num [toy])
    ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num)
  intro h
  by_cases hh : true ∈ h <;>
    simp [productive_eq, StochasticOracleAdaptiveComparisonTests.law, hh,
      Cslib.Optimization.OneConstraint.pair_mean]; norm_num

/-- Response-dependent positive charges: success costs two, failure costs one;
completion stops all further billing. The law still depends on full history. -/
@[expose] def responseBill : List Bool → Bool → ℝ :=
  stoppedBill toy 1 proposals (fun _ x => if x then 2 else 1)

/-- The actual correlated infinite total is finite almost surely, integrable as a
real random variable, and bounded in expectation by eight. -/
theorem actual_total_bill :
    (∀ᵐ ω ∂responseMeasure StochasticOracleAdaptiveComparisonTests.law,
      totalBill responseBill ω < ⊤) ∧
    MeasureTheory.Integrable (fun ω => (totalBill responseBill ω).toReal)
      (responseMeasure StochasticOracleAdaptiveComparisonTests.law) ∧
    (∫ ω, (totalBill responseBill ω).toReal
      ∂responseMeasure StochasticOracleAdaptiveComparisonTests.law) ≤ (8 : ℝ) := by
  have h := totalBill_integrable_le toy 1 proposals
    StochasticOracleAdaptiveComparisonTests.law 1 1 (by norm_num [toy])
    ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num) (by
      intro h
      by_cases hh : true ∈ h <;>
        simp [productive_eq, StochasticOracleAdaptiveComparisonTests.law, hh,
          Cslib.Optimization.OneConstraint.pair_mean]; norm_num)
    responseBill 2 (by norm_num) (by
      intro h x
      simp only [responseBill, stoppedBill]
      split_ifs <;> norm_num) (by
      intro h
      by_cases hc : toy.covered (selected toy 1 proposals h) = toy.ground
      · simp [responseBill, Cslib.Optimization.OneConstraint.Distribution.mean,
          stoppedBill, hc]
      · simp only [responseBill, Cslib.Optimization.OneConstraint.Distribution.mean,
          stoppedBill, hc, ite_false]
        by_cases hh : true ∈ h <;>
          norm_num [StochasticOracleAdaptiveComparisonTests.law, hh,
            Cslib.Optimization.OneConstraint.Distribution.mean, stoppedBill, hc,
            Cslib.Optimization.OneConstraint.pair])
  norm_num at h
  exact h

/-- Empty ground and certain productivity: no turn is billed, even with positive
raw charges. This checks the zero threshold and `p=1` endpoint together. -/
theorem empty_total_bill (law : List Bool →
    Cslib.Optimization.OneConstraint.Distribution Bool ℝ) :
    let I : Instance Unit Unit :=
      { toy with
        ground := ∅
        sets := fun _ => ∅
        sets_subset := by simp
        dual_feasible := by simp [toy] }
    let bill := stoppedBill I 1 proposals (fun _ _ => 7)
    MeasureTheory.Integrable (fun ω => (totalBill bill ω).toReal) (responseMeasure law) ∧
      (∫ ω, (totalBill bill ω).toReal ∂responseMeasure law) ≤ 0 := by
  dsimp only
  let I : Instance Unit Unit :=
    { toy with
        ground := ∅
        sets := fun _ => ∅
        sets_subset := by simp
        dual_feasible := by simp [toy] }
  have hcov (h : List Bool) : I.covered (selected I 1 proposals h) = I.ground := by
    ext e
    simp [Instance.covered, I]
  have h := totalBill_integrable_le I 1 proposals law 1 0 (by simp [I])
    ⟨1, by norm_num, by norm_num⟩ (by norm_num) (by
      intro h
      simp [productive, AdaptiveSelection.residual, hcov,
        Cslib.Optimization.OneConstraint.Distribution.mean_const])
    (stoppedBill I 1 proposals (fun _ _ => 7)) 7 (by norm_num)
    (by intro h x; simp [stoppedBill, hcov])
    (by intro h; simp [Cslib.Optimization.OneConstraint.Distribution.mean,
      stoppedBill, hcov])
  simpa using h.2

end StochasticOracleAdaptiveSelectionTests

-- Chronology and a genuine infinite probability law, including full-history conditioning.
example (ω : ℕ → Bool) : responseHistory ω 2 = [ω 1, ω 0] := by
  simp [responseHistory, List.ofFn_succ]

example : MeasureTheory.IsProbabilityMeasure
    (responseMeasure (fun _ =>
      Cslib.Optimization.OneConstraint.Distribution.pure true)) := inferInstance

example (law : List Bool → Cslib.Optimization.OneConstraint.Distribution Bool ℝ) (n : ℕ) :
    ProbabilityTheory.condDistrib (fun ω : ℕ → Bool => ω (n + 1))
        (Preorder.frestrictLe n) (responseMeasure law)
      =ᵐ[(responseMeasure law).map (Preorder.frestrictLe n)] responseKernel law n :=
  responseMeasure_condDistrib law n

/-- The actual infinite correlated process inherits the checked finite bill bound. -/
example (n : ℕ) :
    (∫ ω, accruedBill (fun h _ =>
      if StochasticOracleAdaptiveSelectionTests.toy.covered
        (selected StochasticOracleAdaptiveSelectionTests.toy 1
          StochasticOracleAdaptiveSelectionTests.proposals h) =
          StochasticOracleAdaptiveSelectionTests.toy.ground then 0 else 1)
        (responseHistory ω n)
      ∂responseMeasure StochasticOracleAdaptiveComparisonTests.law) ≤ (4 : ℝ) := by
  rw [integral_responseHistory]
  exact StochasticOracleAdaptiveSelectionTests.actual_bill_bound n
