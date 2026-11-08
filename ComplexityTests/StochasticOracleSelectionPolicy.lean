/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.SelectionOptimum
public import ComplexityTests.StochasticOracleAdaptiveSelection
import Mathlib.Tactic

/-! Actual randomized early halt, universal comparisons and matching envelopes. -/

public section
noncomputable section
namespace StochasticOracleSelectionPolicyTests
open Cslib.Probability.StochasticOracle Cslib.Optimization.OneConstraint
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory Finset
open StochasticOracleAdaptiveSelectionTests (toy)

/-- Success responses become more likely after success: the full response process
is correlated, while new revealed progress is impossible after full revelation. -/
@[expose] def oracle : Oracle Unit Bool Unit where
  respond h _ := if some ((), true) ∈ h then
    pair true false (3 / 4) (by norm_num) (by norm_num) else
    pair true false (1 / 2) (by norm_num) (by norm_num)
  proposed _ _ x := if x then [{()}] else []
  charge _ _ _ := 1
  duration _ _ _ := 1
  charge_nonneg := by intros; norm_num
  duration_nonneg := by intros; norm_num

private theorem decoder (h : List (Record Unit Bool)) (x : Record Unit Bool) :
    SelectionPolicy.proposals oracle h x = if x = some ((), true) then [{()}] else [] := by
  cases x with
  | none => simp [SelectionPolicy.proposals]
  | some z => rcases z with ⟨⟨⟩, x⟩; cases x <;> simp [SelectionPolicy.proposals, oracle]

private theorem revealed_eq (h : List (Record Unit Bool)) :
    revealed toy (SelectionPolicy.proposals oracle) h =
      if some ((), true) ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [revealed]
  | cons x h ih =>
    rw [revealed, decoder, ih]
    by_cases hx : x = some ((), true) <;> by_cases hh : some ((), true) ∈ h <;>
      simp [hx, hh, eq_comm, Instance.covered, toy]

private theorem selected_eq (h : List (Record Unit Bool)) :
    selected toy 1 (SelectionPolicy.proposals oracle) h =
      if some ((), true) ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [selected]
  | cons x h ih =>
    rw [selected, decoder, ih]
    by_cases hx : x = some ((), true) <;> by_cases hh : some ((), true) ∈ h <;>
      simp [hx, hh, eq_comm, Instance.retain, Instance.Certified, Instance.covered,
        Instance.cost, toy]

/-- These limitations hold for every admissible policy, not just the retaining
candidate or the test policy's selected histories. -/
theorem universal : UniversalBounds oracle toy 1 (1 / 2) 1 1 := by
  intro π _
  constructor
  · intro h _ _ b _
    rcases b with ⟨⟩
    have he (x : Bool) : reveals toy (SelectionPolicy.proposals oracle) h (some ((), x)) =
        decide (some ((), true) ∉ h ∧ x = true) := by
      simp only [reveals, revealed_eq]
      cases x <;> by_cases hh : some ((), true) ∈ h <;> simp [hh]
    simp only [he]
    by_cases hh : some ((), true) ∈ h <;> norm_num [oracle, hh, pair_mean]
  · intro h _ _ b _ x _
    rcases b with ⟨⟩
    simp only [revealed_eq]
    cases x <;> by_cases hh : some ((), true) ∈ h <;> simp [hh]
  · intro h _ _ b _
    simp [oracle, Distribution.mean_const]
  · intro h _ _ b _ x _
    norm_num [oracle]

/-- The upper envelopes are checked for the actual constructed retaining policy. -/
theorem upper : UpperBounds oracle toy 1 (fun _ => Distribution.pure ()) 1 (1 / 2) 1 1 := by
  constructor
  · intro h _ hc b _
    rcases b with ⟨⟩
    have hn : some ((), true) ∉ h := by
      intro hh
      apply hc
      rw [selected_eq]
      simp [hh, Instance.covered, toy]
    have he (x : Bool) : productive toy 1 (SelectionPolicy.proposals oracle) 1 h (some ((), x)) =
        decide (some ((), true) ∈ h ∨ x = true) := by
      simp only [productive, AdaptiveSelection.residual, selected_eq]
      cases x <;> by_cases hh : some ((), true) ∈ h <;> simp [hh, Instance.covered, toy]
    simp only [he]
    norm_num [oracle, hn, pair_mean]
  · intro h _ _ b _
    simp [oracle, Distribution.mean_const]
  · intro h _ _ b _ x _
    norm_num [oracle]

/-- Randomized early halt is allowed independently of retained completion. -/
@[expose] def early : Policy Unit Bool Unit where
  choose _ := pair (some ()) none (1 / 2) (by norm_num) (by norm_num)
  output h := Distribution.pure (available oracle h)

theorem early_admissible : Admissible oracle early := by
  intro h _ C hC
  have he : C = available oracle h := by
    by_contra he
    simp [early, Distribution.pure, he] at hC
  subst C
  exact fun j hj => hj

/-- A genuinely random issue/halt decision has one-turn success 1/4 and token mean
1/2. Both are computed from the actual constructed policy law and output kernel. -/
theorem early_actual : successProbability oracle early toy 1 2 1 = (1 / 4 : ℝ) ∧
    expectedCost oracle early 1 = (1 / 2 : ℝ) := by
  norm_num [successProbability, expectedCost, historyExpectation, law, early, oracle,
    Distribution.mean_bind, Distribution.mean_map, Function.comp_def, pair_mean,
    Distribution.mean_pure, success, available, SelectionPolicy.proposals, Instance.covered,
    Instance.cost, toy, accruedBill, bill, latency]

/-- The source lower cost is derived for the random policy, rather than supplied
as a policy field. The necessary deadline bound uses v=min(2,floor(1/1))=1. -/
theorem early_lower : (1 / 2 : ℝ) ≤ expectedCost oracle early 1 := by
  have h := universal_lower_cost oracle toy 1 1 1 (by intro k hk; simp [toy]; omega)
    (1 / 2) 1 1 1 2 (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    universal early early_admissible (by rw [early_actual.1])
  norm_num at h
  exact h

/-- Matching envelopes compare the actual upper policy against the infimum over
all admissible policies, including early halt and randomized buffered extraction. -/
theorem matched :
    optimalCost oracle toy 1 2 (3 / 4) ≤
      expectedCost oracle (retainingPolicy oracle toy 1 (fun _ => Distribution.pure ())) 2 ∧
    expectedCost oracle (retainingPolicy oracle toy 1 (fun _ => Distribution.pure ())) 2 ≤
      (4 / 3 : ℝ) * optimalCost oracle toy 1 2 (3 / 4) := by
  have hi := bernoulliExpectation_eq_integral ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
    (fun k => if 1 ≤ k then (1 : ℝ) else 0) 2 0
  norm_num [bernoulliExpectation] at hi
  have h := matching_envelope_ratio oracle toy 1 2 (3 / 4)
    (fun _ => Distribution.pure ()) 1 1 2 (by norm_num [toy])
    (by intro k hk; simp [toy]; omega) ⟨1 / 2, by norm_num, by norm_num⟩ (by norm_num)
    1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [← hi]) upper universal
  norm_num at h
  exact h

/-- Lower physical latency restricts the deadline to one completed call, although
the policy has a two-turn budget. Paths issuing two calls cannot succeed by D=1. -/
theorem early_deadline : successProbability oracle early toy 1 1 2 = (1 / 8 : ℝ) ∧
    successProbability oracle early toy 1 1 2 ≤ (1 / 2 : ℝ) := by
  constructor
  · norm_num [successProbability, historyExpectation, law, early, oracle,
      Distribution.mean_bind, Distribution.mean_map, Function.comp_def, pair_mean,
      Distribution.mean_pure, success, available, SelectionPolicy.proposals, Instance.covered,
      Instance.cost, toy, accruedBill, bill, latency]
  · have h := deadline_probability_le oracle early toy early_admissible 1 1 2
      (by intro k hk; simp [toy]; omega) ⟨1 / 2, by norm_num, by norm_num⟩
      1 1 1 1 (by norm_num) (universal early early_admissible)
    have hv : min 2 ⌊(1 : ℝ) / 1⌋₊ = 1 := by norm_num
    rw [hv] at h
    have hi := bernoulliExpectation_eq_integral ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
      (fun k => if 1 ≤ k then (1 : ℝ) else 0) 1 0
    simp only [Nat.zero_add] at hi
    rw [← hi] at h
    norm_num [bernoulliExpectation] at h
    exact h

/-- Locally uncertified response bundles may be buffered and filtered by a valid
selection-only policy; the final cheap singleton is nevertheless certified. -/
@[expose] def bufferedInstance : Instance Unit Bool where
  ground := {()}
  sets _ := {()}
  sets_subset := by simp
  weight b := if b then 1 else 10
  weight_nonneg := by intro b; cases b <;> norm_num
  dual _ := 1
  dual_nonneg := by norm_num
  dual_feasible := by intro b; cases b <;> norm_num

@[expose] def bufferedOracle : Oracle Unit Unit Bool where
  respond _ _ := Distribution.pure ()
  proposed _ _ _ := [{true, false}]
  charge _ _ _ := 1
  duration _ _ _ := 1
  charge_nonneg := by intros; norm_num
  duration_nonneg := by intros; norm_num

@[expose] def buffered : Policy Unit Unit Bool where
  choose _ := Distribution.pure (some ())
  output h := Distribution.pure ({true} ∩ available bufferedOracle h)

theorem buffered_admissible : Admissible bufferedOracle buffered := by
  intro h _ C hC
  have he : C = {true} ∩ available bufferedOracle h := by
    by_contra he
    simp [buffered, Distribution.pure, he] at hC
  subst C
  exact Finset.inter_subset_right

/-- This admissible policy succeeds with probability one even though the
constructive local-retention policy rejects the complete proposed bundle. -/
theorem buffered_actual : successProbability bufferedOracle buffered bufferedInstance 1 1 1 = 1 ∧
    selected bufferedInstance 1 (SelectionPolicy.proposals bufferedOracle) [some ((), ())] = ∅ := by
  norm_num [successProbability, historyExpectation, law, buffered, bufferedOracle,
    Distribution.mean_bind, Distribution.mean_map, Function.comp_def, Distribution.mean_pure,
    success, available, SelectionPolicy.proposals, Instance.covered, Instance.cost,
    bufferedInstance, accruedBill, bill, latency, selected, Instance.retain, Instance.Certified]

/-- Final extraction may itself be randomized, without changing the oracle law. -/
@[expose] def randomizedOutput : Policy Unit Bool Unit where
  choose := early.choose
  output h := pair (available oracle h) ∅ (1 / 2) (by norm_num) (by norm_num)

theorem randomizedOutput_admissible : Admissible oracle randomizedOutput := by
  intro h _ C hC
  by_cases he : C = available oracle h
  · subst C; exact fun _ hj => hj
  · by_cases hz : C = ∅
    · subst C; exact Finset.empty_subset _
    · simp [randomizedOutput, pair, he, hz] at hC

/-- Randomized output halves actual one-turn success, while issued-call cost is
unchanged; the lower theorem still applies to this admissible policy. -/
theorem randomizedOutput_actual : successProbability oracle randomizedOutput toy 1 2 1 =
    (1 / 8 : ℝ) := by
  norm_num [successProbability, historyExpectation, law, randomizedOutput, early, oracle,
    Distribution.mean_bind, Distribution.mean_map, Function.comp_def, pair_mean,
    Distribution.mean_pure, success, available, SelectionPolicy.proposals, Instance.covered,
    Instance.cost, toy, accruedBill, bill, latency]

/-- The non-retaining buffered example also satisfies universal local limitations. -/
theorem buffered_limits : UniversalBounds bufferedOracle bufferedInstance 1 1 1 1 := by
  intro π _
  constructor
  · intro h _ _ b _
    change (Distribution.pure () : Distribution Unit ℝ).mean
      (fun x => if reveals bufferedInstance (SelectionPolicy.proposals bufferedOracle)
        h (some (b, x)) then 1 else 0) ≤ 1
    rw [Distribution.mean_pure]
    split_ifs <;> norm_num
  · intro h _ _ b _ x _
    have hsub : revealed bufferedInstance (SelectionPolicy.proposals bufferedOracle)
        (some (b, x) :: h) \ revealed bufferedInstance
          (SelectionPolicy.proposals bufferedOracle) h ⊆ bufferedInstance.ground := by
      apply sdiff_subset.trans
      rw [← covered_available bufferedOracle bufferedInstance]
      exact bufferedInstance.covered_subset _
    simpa only [bufferedInstance, card_singleton] using card_le_card hsub
  · intro h _ _ b _
    simp [bufferedOracle, Distribution.mean_const]
  · intro h _ _ b _ x _
    norm_num [bufferedOracle]

theorem buffered_lower : (1 : ℝ) ≤ expectedCost bufferedOracle buffered 1 := by
  have h := universal_lower_cost bufferedOracle bufferedInstance 1 1 1
    (by intro k hk; simp [bufferedInstance]; omega) 1 1 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) buffered_limits buffered buffered_admissible
    (by rw [buffered_actual.1])
  norm_num at h
  exact h

end StochasticOracleSelectionPolicyTests
