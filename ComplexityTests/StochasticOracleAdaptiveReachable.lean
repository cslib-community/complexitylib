/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveReachable
public import ComplexityTests.StochasticOracleAdaptiveSelection
import Mathlib.Tactic

/-! Correlated execution with deliberately invalid envelopes on unreachable histories. -/

public section
noncomputable section
namespace StochasticOracleAdaptiveReachableTests
open Cslib.Probability.StochasticOracle Cslib.Optimization.OneConstraint
open AdaptiveSelection PartialCover MeasureTheory
open StochasticOracleAdaptiveSelectionTests (toy)

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- A null response poisons its future kernel; supported histories behave like the
previous correlated Boolean execution. -/
@[expose] def law (h : List (Option Bool)) : Distribution (Option Bool) ℝ :=
  if none ∈ h then Distribution.pure none
  else if some true ∈ h then pair (some true) (some false) (3 / 4) (by norm_num) (by norm_num)
  else pair (some true) (some false) (1 / 4) (by norm_num) (by norm_num)

/-- Only a genuine successful response proposes the singleton cover. -/
@[expose] def proposals (_ : List (Option Bool)) (x : Option Bool) : List (Finset Unit) :=
  if x = some true then [{()}] else []

private theorem selected_eq (h : List (Option Bool)) :
    selected toy 1 proposals h = if some true ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [selected]
  | cons x h ih =>
    rw [selected, ih]
    by_cases hx : x = some true <;> by_cases hh : some true ∈ h <;>
      simp [proposals, hx, hh, eq_comm, Instance.retain, Instance.Certified,
        Instance.covered, Instance.cost, toy]

private theorem productive_eq (h : List (Option Bool)) (x : Option Bool) :
    productive toy 1 proposals 1 h x = decide (some true ∈ h ∨ x = some true) := by
  simp only [productive, AdaptiveSelection.residual, selected_eq]
  by_cases hx : x = some true <;> by_cases hh : some true ∈ h <;>
    simp [hx, hh, eq_comm, Instance.covered, toy]

/-- The poisoned branch has probability zero at every supported prefix. -/
theorem reachable_no_none {h : List (Option Bool)} (hh : Reachable law h) : none ∉ h := by
  induction hh with
  | nil => simp
  | @cons h x hh hx ih =>
    have hn : (law h).weight none = 0 := by
      by_cases ht : some true ∈ h <;> simp [law, ih, ht, pair]
    have hx' : x ≠ none := by
      intro he
      subst x
      rw [hn] at hx
      exact lt_irrefl _ hx
    simp [Ne.symm hx', ih]

/-- The previous all-history productivity envelope is actually false. -/
theorem null_history_violates :
    (law [none]).mean (fun x => if productive toy 1 proposals 1 [none] x then 1 else 0) =
      (0 : ℝ) := by
  simp [law, Distribution.mean_pure, productive_eq]

private theorem envelope (h : List (Option Bool)) (hh : Reachable law h) :
    (1 / 4 : ℝ) ≤ (law h).mean
      (fun x => if productive toy 1 proposals 1 h x then 1 else 0) := by
  have hn := reachable_no_none hh
  by_cases ht : some true ∈ h <;>
    norm_num [law, hn, ht, productive_eq, pair_mean]

/-- Actual completion remains bounded by the binomial tail despite the poisoned
null-history kernel. -/
theorem completion (n : ℕ) :
    (∫ i, (if 1 ≤ i then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial n ⟨1 / 4, by norm_num, by norm_num⟩) ≤
    historyExpectation law
      (fun h => if toy.covered (selected toy 1 proposals h) = toy.ground then 1 else 0) n [] := by
  apply binomial_le_completion_reachable toy 1 proposals law 1 1 n (by norm_num [toy])
  exact fun h hh _ => envelope h hh

/-- Response costs also violate the old bound on null histories: only issued,
supported turns have the source's raw cost envelope. -/
@[expose] def charge (h : List (Option Bool)) (x : Option Bool) : ℝ :=
  if none ∈ h then 100 else if x = some true then 2 else 1

/-- The actual infinite stopped bill is finite, integrable and bounded by eight;
no all-history cost or productivity condition holds for this client. -/
theorem total_cost :
    let bill := stoppedBill toy 1 proposals charge
    (∀ᵐ ω ∂responseMeasure law, totalBill bill ω < ⊤) ∧
    Integrable (fun ω => (totalBill bill ω).toReal) (responseMeasure law) ∧
    (∫ ω, (totalBill bill ω).toReal ∂responseMeasure law) ≤ (8 : ℝ) := by
  have ht := totalStoppedBill_integrable_le_reachable toy 1 proposals law
    1 1 (by norm_num [toy]) ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num)
    (fun h hh _ => envelope h hh) charge 2 (by norm_num)
    (by intro h x; simp only [charge]; split_ifs <;> norm_num) (by
      intro h hh _
      have hn := reachable_no_none hh
      by_cases hs : some true ∈ h <;>
        norm_num [law, hn, hs, charge, pair_mean])
  norm_num at ht
  exact ht

/-- Correlation survives the null-history extension: two actual successes have
probability 3/16, while the first success probability is 1/4. -/
theorem correlated :
    progressExpectation law (fun _ x => decide (x = some true))
      (fun k => if 2 ≤ k then 1 else 0) 2 [] 0 = (3 / 16 : ℝ) := by
  norm_num [progressExpectation, law, pair_mean]

/-- Cost failure at the same genuinely null history is quantitative. -/
theorem null_cost_violates : (law [none]).mean (charge [none]) = (100 : ℝ) := by
  simp [law, Distribution.mean_pure, charge]

/-- Actual selected-batch disintegration also ignores a null batch whose response
is never productive. The positive-probability batch uses the correlated kernel. -/
theorem selected_batch_envelope (h : List (Bool × Option Bool))
    (hh : Reachable law (h.map Prod.snd)) :
    (1 / 4 : ℝ) ≤ (selectedBatchLaw
      (fun _ => Distribution.pure true)
      (fun h b => if b then law (h.map Prod.snd) else Distribution.pure none) h).mean
        (fun x => if productive toy 1 proposals 1 (h.map Prod.snd) x.2 then 1 else 0) := by
  apply selectedBatchLaw_mean_lower
  intro b hb
  have hb' : b = true := by
    cases b <;> simp_all [Distribution.pure]
  subst b
  exact envelope _ hh

/-- The original infinite law puts all its prefixes in the supported set. -/
theorem actual_supported :
    ∀ᵐ ω ∂responseMeasure law, ∀ n, none ∉ responseHistory ω n := by
  filter_upwards [ae_responseHistory_reachable law] with ω hω
  exact fun n => reachable_no_none (hω n)

/-- Almost-sure completion also uses only supported issued turns. -/
theorem actual_completion :
    ∀ᵐ ω ∂responseMeasure law, ∀ᶠ n in Filter.atTop,
      toy.covered (selected toy 1 proposals (responseHistory ω n)) = toy.ground := by
  apply ae_eventually_complete_reachable toy 1 proposals law 1 1 (by norm_num [toy])
    ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num)
  exact fun h hh _ => envelope h hh

/-- Full batch/response execution retaining the actual batch in every history. -/
@[expose] def batchResponse (h : List (Bool × Option Bool)) (b : Bool) :
    Distribution (Option Bool) ℝ :=
  if b then law (h.map Prod.snd) else Distribution.pure none

@[expose] def batchProposals (h : List (Bool × Option Bool)) (x : Bool × Option Bool) :
    List (Finset Unit) := proposals (h.map Prod.snd) x.2

private theorem batch_selected (h : List (Bool × Option Bool)) :
    selected toy 1 batchProposals h = selected toy 1 proposals (h.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [selected, batchProposals, List.map_cons, ih]

private theorem batch_reachable {h : List (Bool × Option Bool)}
    (hh : Reachable (selectedBatchLaw (fun _ => Distribution.pure true) batchResponse) h) :
    Reachable law (h.map Prod.snd) := by
  induction hh with
  | nil => exact .nil
  | @cons h x hh hx ih =>
    rcases x with ⟨b, x⟩
    have hb : b = true := by
      by_contra hb
      rw [selectedBatchLaw_weight] at hx
      simp [Distribution.pure, hb] at hx
    rw [selectedBatchLaw_weight] at hx
    apply Reachable.cons ih
    simpa [Distribution.pure, batchResponse, hb] using hx

/-- The composed actual selected-batch process satisfies the infinite stopped-cost
conclusion, with the null history and the null selected batch both unconstrained. -/
theorem batch_total_cost :
    let μ := responseMeasure
      (selectedBatchLaw (fun _ => Distribution.pure true) batchResponse)
    let bill := stoppedBill toy 1 batchProposals (fun h x => charge (h.map Prod.snd) x.2)
    (∀ᵐ ω ∂μ, totalBill bill ω < ⊤) ∧
    Integrable (fun ω => (totalBill bill ω).toReal) μ ∧
    (∫ ω, (totalBill bill ω).toReal ∂μ) ≤ (8 : ℝ) := by
  have ht := selectedBatch_totalStoppedBill toy 1 batchProposals
    (fun _ => Distribution.pure true) batchResponse 1 1 (by norm_num [toy])
    ⟨1 / 4, by norm_num, by norm_num⟩ (by norm_num) (by
      intro h hh _ b hb
      have hb' : b = true := by cases b <;> simp_all [Distribution.pure]
      subst b
      have he (x : Option Bool) :
          productive toy 1 batchProposals 1 h (true, x) =
            productive toy 1 proposals 1 (h.map Prod.snd) x := by
        simp only [productive, AdaptiveSelection.residual, batch_selected, List.map_cons]
        apply decide_eq_decide.mpr
        rfl
      simp only [batchResponse, ite_true, he]
      exact envelope _ (batch_reachable hh))
    (fun h x => charge (h.map Prod.snd) x.2) 2 (by norm_num)
    (by intro h x; simp only [charge]; split_ifs <;> norm_num) (by
      intro h hh _ b hb
      have hb' : b = true := by cases b <;> simp_all [Distribution.pure]
      subst b
      have hn := reachable_no_none (batch_reachable hh)
      by_cases hs : some true ∈ h.map Prod.snd <;>
        norm_num [batchResponse, law, hn, hs, charge, pair_mean])
  norm_num at ht
  exact ht

end StochasticOracleAdaptiveReachableTests
