/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveReachable
public import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stopping and physical deadlines for adaptive retained covers

For [Wang2027], Theorem 5(1) (PDF p. 12), Appendix A.5 (p. 16), stopping
means first retained completion, capped by the issued-turn budget. The process
is the actual full-history response law, with finite response alphabet.

## Main definitions

* `completionTime`: first completion, with infinity for a nonterminating path.
* `cappedTime`: first completion or the turn budget.
* `stoppedOutput`: the retained family at the capped stopping index.
* `physicalDuration`: sum of actual durations before that index.

## Main results

* `completionTime_mean`: measurable a.s. finite stopping with exact survival mean and `r/p` bound.
* `binomial_le_jointSuccess`: joint physical deadline, completion and dual certification.
* `expected_cost_at_capped`: the same execution has the finite binomial token-cost bound.

These give the finite-alphabet upper-policy probabilistic/physical composition;
universal selection-only lower bounds and encoded machine resources remain separate.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open MeasureTheory PartialCover Finset
open scoped ENNReal

variable {Ω E J : Type*} [DecidableEq E] [DecidableEq J]

/-- The number of uncovered elements after `n` actual responses. -/
@[expose] def residualProcess (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (n : ℕ) (ω : ℕ → Ω) : ℕ :=
  residual I ρ proposal (responseHistory ω n)

/-- First actual retained completion; infinity is preserved for divergent paths. -/
@[expose] def completionTime (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) : (ℕ → Ω) → WithTop ℕ :=
  @hittingAfter (ℕ → Ω) ℕ ℕ
    (inferInstance : ConditionallyCompleteLinearOrder ℕ).toPreorder
    (inferInstance : ConditionallyCompleteLinearOrder ℕ).toInfSet
    (residualProcess I ρ proposal) {0} 0

/-- Actual execution stops at completion or when it has used its turn budget. -/
@[expose] def cappedTime (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) : (ℕ → Ω) → ℕ :=
  @hittingBtwn (ℕ → Ω) ℕ ℕ
    (inferInstance : ConditionallyCompleteLinearOrder ℕ).toPreorder
    (inferInstance : ConditionallyCompleteLinearOrder ℕ).toInfSet
    (residualProcess I ρ proposal) {0} 0 u

/-- The actual retained result at the capped stopping index. -/
@[expose] def stoppedOutput (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω) : Finset J :=
  selected I ρ proposal (responseHistory ω (cappedTime I ρ proposal u ω))

/-- Zero residual is exactly full retained coverage, without a progress premise. -/
theorem residual_eq_zero_iff (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (h : List Ω) :
    residual I ρ proposal h = 0 ↔ I.covered (selected I ρ proposal h) = I.ground := by
  rw [residual, card_eq_zero, sdiff_eq_empty_iff_subset]
  exact ⟨fun h => Subset.antisymm (I.covered_subset _) h, fun h => h ▸ Subset.rfl⟩

/-- Residuals are nonincreasing along every response path. -/
theorem residualProcess_antitone (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (ω : ℕ → Ω) :
    Antitone (fun n => residualProcess I ρ proposal n ω) := by
  apply antitone_nat_of_succ_le
  intro n
  simpa only [residualProcess, responseHistory_succ] using
    residual_mono I ρ proposal (responseHistory ω n) (ω n)

/-- The first-completion event is exactly the finite completion cylinder. -/
theorem completionTime_le_iff (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (ω : ℕ → Ω) (n : ℕ) :
    completionTime I ρ proposal ω ≤ n ↔
      I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground := by
  rw [completionTime]
  have ht := hittingAfter_le_iff (u := residualProcess I ρ proposal)
    (s := {0}) (n := 0) (i := n) (ω := ω)
  apply Iff.trans (b := ∃ j ∈ Set.Icc 0 n, residualProcess I ρ proposal j ω ∈ ({0} : Set ℕ)) ?_ ?_
  · with_reducible_and_instances exact ht
  constructor
  · rintro ⟨k, hk, hzero⟩
    apply (residual_eq_zero_iff I ρ proposal _).mp
    have hm := residualProcess_antitone I ρ proposal ω hk.2
    dsimp only at hm
    change residualProcess I ρ proposal k ω = 0 at hzero
    change residualProcess I ρ proposal n ω = 0
    omega
  · intro hc
    exact ⟨n, ⟨Nat.zero_le _, le_rfl⟩, (residual_eq_zero_iff I ρ proposal _).mpr hc⟩

/-- The capped index never exceeds the issued-turn budget. -/
theorem cappedTime_le (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω) :
    cappedTime I ρ proposal u ω ≤ u := hittingBtwn_le ω

/-- Completion within the budget yields a complete actual stopped output. -/
theorem stoppedOutput_complete (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω)
    (hc : I.covered (selected I ρ proposal (responseHistory ω u)) = I.ground) :
    I.covered (stoppedOutput I ρ proposal u ω) = I.ground := by
  apply (residual_eq_zero_iff I ρ proposal _).mp
  have hc' : residualProcess I ρ proposal u ω ∈ ({0} : Set ℕ) :=
    (residual_eq_zero_iff I ρ proposal _).mpr hc
  exact hittingBtwn_mem_set (u := residualProcess I ρ proposal)
    (s := {0}) (n := 0) (m := u) (ω := ω) ⟨u, ⟨Nat.zero_le _, le_rfl⟩, hc'⟩

/-- On a path whose first completion is `k`, issued-turn indicators are exactly
ones before `k` and zero from `k` onward. -/
theorem issued_indicator_eq (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (ω : ℕ → Ω) (k : ℕ)
    (hk : completionTime I ρ proposal ω = k) (n : ℕ) :
    (if I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground
      then (0 : ℝ) else 1) = if n < k then 1 else 0 := by
  have hc := completionTime_le_iff I ρ proposal ω n
  rw [hk] at hc
  have hn : ((k : WithTop ℕ) ≤ n) ↔ k ≤ n := by norm_cast
  rw [hn] at hc
  by_cases hnk : n < k
  · have hnot : I.covered (selected I ρ proposal (responseHistory ω n)) ≠ I.ground :=
      fun h => (Nat.not_le_of_lt hnk) (hc.mpr h)
    simp [hnk, hnot]
  · simp [hnk, hc.mp (Nat.le_of_not_gt hnk)]

/-- The unit stopped bill is the actual number of issued turns, on every
terminating trajectory. This is derived from first-completion semantics. -/
theorem total_unitBill_eq (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (ω : ℕ → Ω) (k : ℕ)
    (hk : completionTime I ρ proposal ω = k) :
    totalBill (stoppedBill I ρ proposal (fun _ _ => 1)) ω = k := by
  rw [totalBill_eq_tsum _ (by intro h x; simp only [stoppedBill]; split_ifs <;> norm_num)]
  have he (n : ℕ) := issued_indicator_eq I ρ proposal ω k hk n
  simp only [stoppedBill, he]
  rw [tsum_eq_sum (s := range k)]
  · calc
      _ = ∑ _n ∈ range k, (1 : ℝ≥0∞) := by
        apply sum_congr rfl
        intro n hn
        rw [ite_eq_left (mem_range.mp hn)]
        exact ENNReal.ofReal_one
      _ = k := by simp
  · intro n hn
    simp only [mem_range, not_lt] at hn
    simp [Nat.not_lt.mpr hn]

/-- The corresponding real survival series is the same actual issued-turn count. -/
theorem tsum_issued_eq (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (ω : ℕ → Ω) (k : ℕ)
    (hk : completionTime I ρ proposal ω = k) :
    (∑' n, if I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground
      then (0 : ℝ) else 1) = k := by
  simp only [issued_indicator_eq I ρ proposal ω k hk]
  rw [tsum_eq_sum (s := range k)]
  · simp only [sum_ite_of_true (fun n hn => mem_range.mp hn)]
    simp
  · intro n hn
    simp only [mem_range, not_lt] at hn
    simp [Nat.not_lt.mpr hn]

/-- Every turn before the capped index is genuinely issued. -/
theorem incomplete_before_capped (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω) (t : ℕ)
    (ht : t < cappedTime I ρ proposal u ω) :
    I.covered (selected I ρ proposal (responseHistory ω t)) ≠ I.ground := by
  intro hc
  have hnot := notMem_of_lt_hittingBtwn (u := residualProcess I ρ proposal)
    (s := {0}) (n := 0) (m := u) (ω := ω) ht (Nat.zero_le t)
  exact hnot ((residual_eq_zero_iff I ρ proposal _).mpr hc)

/-- If the capped index is before a later budgeted turn, completion has already
occurred. This proves the stopping mask, rather than assuming it. -/
theorem complete_after_capped (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω) (t : ℕ)
    (hkt : cappedTime I ρ proposal u ω ≤ t) (htu : t < u) :
    I.covered (selected I ρ proposal (responseHistory ω t)) = I.ground := by
  have hz := hittingBtwn_mem_set_of_hittingBtwn_lt (u := residualProcess I ρ proposal)
    (s := {0}) (n := 0) (m := u) (ω := ω) (hkt.trans_lt htu)
  have hm := residualProcess_antitone I ρ proposal ω hkt
  change residualProcess I ρ proposal (cappedTime I ρ proposal u ω) ω = 0 at hz
  dsimp only at hm
  apply (residual_eq_zero_iff I ρ proposal _).mp
  change residualProcess I ρ proposal t ω = 0
  omega

/-- Actual charges up to the capped stopping index equal the finite stopped-bill
observable at the original budget. This links physical execution to accounting. -/
theorem accruedBill_at_capped (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (charge : List Ω → Ω → ℝ)
    (u : ℕ) (ω : ℕ → Ω) :
    accruedBill charge (responseHistory ω (cappedTime I ρ proposal u ω)) =
      accruedBill (stoppedBill I ρ proposal charge) (responseHistory ω u) := by
  simp only [accruedBill_responseHistory]
  calc
    _ = ∑ t ∈ range (cappedTime I ρ proposal u ω),
        stoppedBill I ρ proposal charge (responseHistory ω t) (ω t) := by
      apply sum_congr rfl
      intro t ht
      simp only [stoppedBill, incomplete_before_capped I ρ proposal u ω t (mem_range.mp ht),
        ite_false]
    _ = _ := by
      apply sum_subset (range_mono (cappedTime_le I ρ proposal u ω))
      intro t htu htk
      simp only [mem_range, not_lt] at htu htk
      simp only [stoppedBill, complete_after_capped I ρ proposal u ω t htk htu, ite_true]

/-- Physical duration adds the actual per-turn durations only until execution stops. -/
@[expose] def physicalDuration (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (duration : List Ω → Ω → ℝ)
    (u : ℕ) (ω : ℕ → Ω) : ℝ :=
  accruedBill duration (responseHistory ω (cappedTime I ρ proposal u ω))

variable [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [Fintype Ω] in
/-- Measurability of the actual first-completion index. -/
theorem measurable_completionTime [Finite Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) : Measurable (completionTime I ρ proposal) := by
  apply measurable_of_Iic
  intro t
  rcases eq_or_ne t ⊤ with rfl | ht
  · simp
  · lift t to ℕ using ht with n
    have hm := measurable_responseHistory n
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then (1 : ℝ) else 0)
    have he : (completionTime I ρ proposal) ⁻¹' Set.Iic (n : WithTop ℕ) =
        (fun ω => (if I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground
          then (1 : ℝ) else 0)) ⁻¹' {1} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, completionTime_le_iff,
        Set.mem_singleton_iff]
      split_ifs <;> simp_all
    have hs := hm (measurableSet_singleton 1)
    rw [← he] at hs
    with_reducible_and_instances exact hs

omit [Fintype Ω] in
/-- The capped index is measurable; it is a Mathlib hitting time of the natural
residual filtration. No probabilistic termination premise is needed. -/
theorem measurable_cappedTime [Finite Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) :
    Measurable (cappedTime I ρ proposal u) := by
  have hm (n : ℕ) : Measurable (residualProcess I ρ proposal n) := by
    exact (measurable_of_finite (fun x : Fin n → Ω =>
      residual I ρ proposal (List.ofFn x).reverse)).comp (by fun_prop)
  have ha := (Filtration.stronglyAdapted_natural
    (fun n => (hm n).stronglyMeasurable)).adapted
  have ht := ha.isStoppingTime_hittingBtwn (n := 0) (n' := u) (measurableSet_singleton 0)
  have htm := (ht.measurable.mono ht.measurableSpace_le le_rfl).untopD 0
  with_reducible_and_instances
    simpa only [cappedTime, WithTop.untopD_coe] using htm

omit [Fintype Ω] in
/-- Arbitrary real history observables evaluated at the actual capped index are
measurable, including the returned certificate and accumulated duration. -/
theorem measurable_at_cappedTime [Finite Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (f : List Ω → ℝ) :
    Measurable (fun ω => f (responseHistory ω (cappedTime I ρ proposal u ω))) := by
  have hm : Measurable (fun z : ℕ × (ℕ → Ω) => f (responseHistory z.2 z.1)) :=
    measurable_from_prod_countable_right (fun n => measurable_responseHistory n f)
  exact hm.comp ((measurable_cappedTime I ρ proposal u).prodMk measurable_id)

/-- Actual stopping-time survival probability is exactly the noncompletion
cylinder expectation. This identifies the series in the mean formula. -/
theorem completionTime_survival (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    (responseMeasure law).real {ω | (n : WithTop ℕ) < completionTime I ρ proposal ω} =
      historyExpectation law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n [] := by
  have hs : MeasurableSet {ω | (n : WithTop ℕ) < completionTime I ρ proposal ω} :=
    measurableSet_lt measurable_const (measurable_completionTime I ρ proposal)
  have he : {ω | (n : WithTop ℕ) < completionTime I ρ proposal ω}.indicator
      (1 : (ℕ → Ω) → ℝ) = (fun ω =>
        if I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground
          then (0 : ℝ) else 1) := by
    funext ω
    have hc := completionTime_le_iff I ρ proposal ω n
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    by_cases ht : completionTime I ρ proposal ω ≤ n
    · simp [not_lt.mpr ht, hc.mp ht]
    · have hnot : I.covered (selected I ρ proposal (responseHistory ω n)) ≠ I.ground :=
        fun h => ht (hc.mpr h)
      simp [lt_of_not_ge ht, hnot]
  have hi := integral_indicator_one (μ := responseMeasure law) hs
  rw [he] at hi
  rw [integral_responseHistory law
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n] at hi
  exact hi.symm

/-- The actual capped stopping index has the finite survival-sum expectation,
including zero budget and paths that never complete. No productivity premise is needed. -/
theorem cappedTime_mean {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (u : ℕ) :
    (∫ ω, (cappedTime I ρ proposal u ω : ℝ) ∂responseMeasure law) =
      ∑ n ∈ range u, (responseMeasure law).real
        {ω | (n : WithTop ℕ) < completionTime I ρ proposal ω} := by
  have he (ω : ℕ → Ω) : accruedBill (fun _ _ => (1 : ℝ))
      (responseHistory ω (cappedTime I ρ proposal u ω)) = cappedTime I ρ proposal u ω := by
    simp [accruedBill_responseHistory]
  have hm (h : List Ω) :
      (law h).mean (stoppedBill I ρ proposal (fun _ _ => 1) h) =
        if I.covered (selected I ρ proposal h) = I.ground then (0 : ℝ) else 1 := by
    change (law h).mean (fun _ => if I.covered (selected I ρ proposal h) = I.ground
      then (0 : ℝ) else 1) = _
    exact Cslib.Optimization.OneConstraint.Distribution.mean_const (law h) _
  calc
    _ = ∫ ω, accruedBill (fun _ _ => (1 : ℝ))
        (responseHistory ω (cappedTime I ρ proposal u ω)) ∂responseMeasure law := by
      congr 1
      funext ω
      exact (he ω).symm
    _ = historyExpectation law (accruedBill (stoppedBill I ρ proposal (fun _ _ => 1)))
        u [] := by
      simp_rw [accruedBill_at_capped]
      exact integral_responseHistory law _ u
    _ = ∑ n ∈ range u, historyExpectation law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n [] := by
      rw [historyExpectation_accruedBill, accruedBill, zero_add, executionCost_eq_sum]
      simp only [hm]
    _ = _ := sum_congr rfl (fun n _ => (completionTime_survival I ρ proposal law n).symm)

/-- Actual first-completion mean: the survival series identity, integrability and
`r/p` upper bound follow from supported issued-history productivity. Infinity is
excluded almost surely; `untopD 0` is only a total real-valued representative. -/
theorem completionTime_mean {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (p : ℝ) ≤ (law h).mean (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    (∀ᵐ ω ∂responseMeasure law, completionTime I ρ proposal ω ≠ ⊤) ∧
    Integrable (fun ω => (((completionTime I ρ proposal ω).untopD 0 : ℕ) : ℝ))
      (responseMeasure law) ∧
    (∫ ω, (((completionTime I ρ proposal ω).untopD 0 : ℕ) : ℝ) ∂responseMeasure law) =
      ∑' n : ℕ, (responseMeasure law).real
        {ω | (n : WithTop ℕ) < completionTime I ρ proposal ω} ∧
    (∫ ω, (((completionTime I ρ proposal ω).untopD 0 : ℕ) : ℝ) ∂responseMeasure law) ≤
      (r : ℝ) / p := by
  have hfinite : ∀ᵐ ω ∂responseMeasure law, completionTime I ρ proposal ω ≠ ⊤ := by
    filter_upwards [ae_eventually_complete_reachable I ρ proposal law a r hr p hp0 hp]
      with ω hω
    obtain ⟨n, hn⟩ := hω.exists
    have ht := (completionTime_le_iff I ρ proposal ω n).mpr hn
    exact ne_top_of_le_ne_top (by simp) ht
  let bill := stoppedBill I ρ proposal (fun _ _ => 1)
  have hb := totalStoppedBill_integrable_le_reachable I ρ proposal law a r hr p hp0 hp
    (fun _ _ => 1) 1 (by norm_num) (by intros; norm_num) (by
      intro h _ _
      simp [Cslib.Optimization.OneConstraint.Distribution.mean_const])
  have heq : (fun ω => (totalBill bill ω).toReal) =ᵐ[responseMeasure law]
      (fun ω => (((completionTime I ρ proposal ω).untopD 0 : ℕ) : ℝ)) := by
    filter_upwards [hfinite] with ω hω
    lift completionTime I ρ proposal ω to ℕ using hω with k hk
    simp only [bill, total_unitBill_eq I ρ proposal ω k hk.symm,
      WithTop.untopD_coe, ENNReal.toReal_natCast]
  have hi := hb.2.1.congr heq
  refine ⟨hfinite, hi, ?_, ?_⟩
  · refine Eq.trans ?_ (tsum_congr (fun n => completionTime_survival I ρ proposal law n)).symm
    let f : ℕ → (ℕ → Ω) → ℝ := fun n ω =>
      if I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground then 0 else 1
    have hfi (n : ℕ) : Integrable (f n) (responseMeasure law) :=
      Integrable.of_bound (measurable_responseHistory n
        (fun h => if I.covered (selected I ρ proposal h) = I.ground
          then 0 else 1)).aestronglyMeasurable
        1 (Filter.Eventually.of_forall fun ω => by dsimp only [f]; split_ifs <;> norm_num)
    have hn (n : ℕ) : (∫ ω, ‖f n ω‖ ∂responseMeasure law) =
        historyExpectation law
          (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n [] := by
      have he : (fun ω => ‖f n ω‖) = f n := by funext ω; dsimp only [f]; split_ifs <;> norm_num
      rw [he]
      exact integral_responseHistory law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n
    have hs : Summable (fun n => ∫ ω, ‖f n ω‖ ∂responseMeasure law) := by
      simp only [hn]
      exact summable_noncompletion_reachable I ρ proposal law a r hr p hp0 hp
    have hpath : (fun ω => (((completionTime I ρ proposal ω).untopD 0 : ℕ) : ℝ))
        =ᵐ[responseMeasure law]
        (fun ω => ∑' n, f n ω) := by
      filter_upwards [hfinite] with ω hω
      lift completionTime I ρ proposal ω to ℕ using hω with k hk
      simpa only [WithTop.untopD_coe, WithTop.untopD_natCast, Nat.cast_id]
        using (tsum_issued_eq I ρ proposal ω k hk.symm).symm
    rw [integral_congr_ae hpath, ← integral_tsum_of_summable_integral_norm hfi hs]
    congr 1
    funext n
    exact integral_responseHistory law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n
  · rw [← integral_congr_ae heq]
    simpa only [one_mul] using hb.2.2

/-- Supported issued-turn latency contracts imply the actual physical deadline
bound almost surely, without any independence assumption on responses. -/
theorem physicalDuration_le {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (duration : List Ω → Ω → ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hl : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      ∀ x, 0 < (law h).weight x → 0 ≤ duration h x ∧ duration h x ≤ ℓ) (u : ℕ) :
    ∀ᵐ ω ∂responseMeasure law, 0 ≤ physicalDuration I ρ proposal duration u ω ∧
      physicalDuration I ρ proposal duration u ω ≤ (u : ℝ) * ℓ := by
  filter_upwards [ae_responseHistory_reachable law] with ω hω
  have hb (t : ℕ) (ht : t < cappedTime I ρ proposal u ω) :
      0 ≤ duration (responseHistory ω t) (ω t) ∧
        duration (responseHistory ω t) (ω t) ≤ ℓ := by
    have hh := hω (t + 1)
    rw [responseHistory_succ] at hh
    cases hh with
    | cons hh hx => exact hl _ hh (incomplete_before_capped I ρ proposal u ω t ht) _ hx
  simp only [physicalDuration, accruedBill_responseHistory]
  refine ⟨sum_nonneg (fun t ht => (hb t (mem_range.mp ht)).1), ?_⟩
  calc
    _ ≤ ∑ _t ∈ range (cappedTime I ρ proposal u ω), ℓ :=
      sum_le_sum (fun t ht => (hb t (mem_range.mp ht)).2)
    _ = (cappedTime I ρ proposal u ω : ℝ) * ℓ := by simp
    _ ≤ (u : ℝ) * ℓ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast cappedTime_le I ρ proposal u ω) hℓ

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The pathwise local dual certificate holds for the actual stopped output. -/
theorem stoppedOutput_certificate (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω)
    (hc : I.covered (stoppedOutput I ρ proposal u ω) = I.ground) :
    I.cost (stoppedOutput I ρ proposal u ω) ≤ ρ * ∑ e ∈ I.ground, I.dual e := by
  have hb := selected_bound I ρ proposal (responseHistory ω (cappedTime I ρ proposal u ω))
  change I.cost (stoppedOutput I ρ proposal u ω) ≤
    ρ * ∑ e ∈ I.covered (stoppedOutput I ρ proposal u ω), I.dual e at hb
  rwa [hc] at hb

/-- Joint success means that the actual stopped returned family is complete,
dual-certified, and physically available by the deadline. -/
@[expose] def jointSuccess (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (duration : List Ω → Ω → ℝ)
    (u : ℕ) (D : ℝ) : Set (ℕ → Ω) :=
  {ω | I.covered (stoppedOutput I ρ proposal u ω) = I.ground ∧
    I.cost (stoppedOutput I ρ proposal u ω) ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
    physicalDuration I ρ proposal duration u ω ≤ D}

omit [Fintype Ω] in
/-- The joint success event is measurable, including the actual stopped output. -/
theorem measurableSet_jointSuccess [Finite Ω] (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (duration : List Ω → Ω → ℝ)
    (u : ℕ) (D : ℝ) : MeasurableSet (jointSuccess I ρ proposal duration u D) := by
  have hc := measurable_at_cappedTime I ρ proposal u
    (fun h => if I.covered (selected I ρ proposal h) = I.ground ∧
      I.cost (selected I ρ proposal h) ≤ ρ * ∑ e ∈ I.ground, I.dual e then (1 : ℝ) else 0)
  have hd := measurable_at_cappedTime I ρ proposal u (accruedBill duration)
  have he : jointSuccess I ρ proposal duration u D =
      (fun ω => if I.covered (stoppedOutput I ρ proposal u ω) = I.ground ∧
        I.cost (stoppedOutput I ρ proposal u ω) ≤ ρ * ∑ e ∈ I.ground, I.dual e
        then (1 : ℝ) else 0) ⁻¹' {1} ∩
      (physicalDuration I ρ proposal duration u) ⁻¹' Set.Iic D := by
    ext ω
    simp only [jointSuccess, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_Iic]
    split_ifs <;> simp_all
  rw [he]
  exact (hc (measurableSet_singleton 1)).inter (hd measurableSet_Iic)

/-- The source's finite upper-policy joint guarantee for the actual capped output:
completion, dual certification and physical deadline hold on one event, whose
probability is at least the binomial tail. Per-turn latency is bounded only on
supported issued responses. No deadline or certification conclusion is a premise. -/
theorem binomial_le_jointSuccess {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r u : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (p : ℝ) ≤ (law h).mean (fun x => if productive I ρ proposal a h x then 1 else 0))
    (duration : List Ω → Ω → ℝ) (ℓ D : ℝ) (hℓ : 0 ≤ ℓ)
    (hl : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      ∀ x, 0 < (law h).weight x → 0 ≤ duration h x ∧ duration h x ≤ ℓ)
    (hD : (u : ℝ) * ℓ ≤ D) :
    (∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial u p) ≤
      (responseMeasure law).real (jointSuccess I ρ proposal duration u D) := by
  let event := jointSuccess I ρ proposal duration u D
  have hme := measurableSet_jointSuccess I ρ proposal duration u D
  have hiej : Integrable (event.indicator (fun _ => (1 : ℝ))) (responseMeasure law) :=
    (integrable_const 1).indicator hme
  have hiec : Integrable (fun ω => if I.covered (selected I ρ proposal
      (responseHistory ω u)) = I.ground then (1 : ℝ) else 0) (responseMeasure law) :=
    Integrable.of_bound (measurable_responseHistory u
      (fun h => if I.covered (selected I ρ proposal h) = I.ground
        then 1 else 0)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)
  have hae : (fun ω => if I.covered (selected I ρ proposal (responseHistory ω u)) = I.ground
      then (1 : ℝ) else 0) ≤ᵐ[responseMeasure law] event.indicator (fun _ => 1) := by
    filter_upwards [physicalDuration_le I ρ proposal law duration ℓ hℓ hl u] with ω hω
    by_cases hc : I.covered (selected I ρ proposal (responseHistory ω u)) = I.ground
    · have hs := stoppedOutput_complete I ρ proposal u ω hc
      have he : ω ∈ event := ⟨hs, stoppedOutput_certificate I ρ proposal u ω hs,
        hω.2.trans hD⟩
      simp [hc, Set.indicator_of_mem he]
    · simp only [hc, ite_false]
      exact Set.indicator_nonneg (fun _ _ => by norm_num) _
  have hb := binomial_le_completion_reachable I ρ proposal law a r u hr p hp
  rw [← integral_responseHistory law
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) u] at hb
  have hi := integral_mono_ae hiec hiej hae
  have hevent := integral_indicator_one (μ := responseMeasure law) (s := event) hme
  exact (hb.trans hi).trans_eq hevent

/-- The cost in the same capped physical execution is the source's finite stopped
bill, with its binomial survival bound, from supported issued-history means. -/
theorem expected_cost_at_capped {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r u : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (p : ℝ) ≤ (law h).mean (fun x => if productive I ρ proposal a h x then 1 else 0))
    (charge : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (law h).mean (charge h) ≤ c) :
    (∫ ω, accruedBill charge (responseHistory ω (cappedTime I ρ proposal u ω))
      ∂responseMeasure law) ≤
      ∑ t ∈ range u, c * binomialFailure p r t := by
  simp_rw [accruedBill_at_capped]
  rw [integral_responseHistory]
  have h := accruedBill_le_binomial_sum_reachable I ρ proposal law a r u hr p hp
    (stoppedBill I ρ proposal charge) c hc (by
      intro h hh
      by_cases hd : I.covered (selected I ρ proposal h) = I.ground
      · simp [Cslib.Optimization.OneConstraint.Distribution.mean, stoppedBill, hd]
      · simpa only [Cslib.Optimization.OneConstraint.Distribution.mean,
          stoppedBill, hd, ite_false, mul_one] using hb h hh hd)
  simpa only [binomialFailure_eq_complement] using h

/-- The actual finite stopped cost is integrable, independently of a cost envelope. -/
theorem integrable_cost_at_capped (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (charge : List Ω → Ω → ℝ) (u : ℕ) :
    Integrable (fun ω => accruedBill charge
      (responseHistory ω (cappedTime I ρ proposal u ω))) (responseMeasure law) :=
  (integrable_accruedBill law (stoppedBill I ρ proposal charge) u).congr
    (Filter.Eventually.of_forall fun ω => (accruedBill_at_capped I ρ proposal charge u ω).symm)

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Dual certification of the stopped cover implies approximation against every
integral cover, using feasibility rather than an optimum oracle. -/
theorem stoppedOutput_approx (I : Instance E J) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (proposal : List Ω → Ω → List (Finset J)) (u : ℕ) (ω : ℕ → Ω)
    (hc : I.covered (stoppedOutput I ρ proposal u ω) = I.ground)
    (C : Finset J) (hC : I.covered C = I.ground) :
    I.cost (stoppedOutput I ρ proposal u ω) ≤ ρ * I.cost C := by
  apply (stoppedOutput_certificate I ρ proposal u ω hc).trans
  apply mul_le_mul_of_nonneg_left _ hρ
  rw [← hC]
  exact I.dual_le_cost C

/-- A supported joint batch/response has a positive-probability selected batch
and a supported conditional response. Thus source per-selected-batch physical
contracts imply the joint-law contract used in `binomial_le_jointSuccess`. -/
theorem selectedBatch_duration_bound {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Cslib.Optimization.OneConstraint.Distribution B ℝ)
    (respond : List (B × R) → B → Cslib.Optimization.OneConstraint.Distribution R ℝ)
    (h : List (B × R)) (duration : List (B × R) → B × R → ℝ) (ℓ : ℝ)
    (hl : ∀ b, 0 < (select h).weight b → ∀ x, 0 < (respond h b).weight x →
      0 ≤ duration h (b, x) ∧ duration h (b, x) ≤ ℓ)
    (x : B × R) (hx : 0 < (selectedBatchLaw select respond h).weight x) :
    0 ≤ duration h x ∧ duration h x ≤ ℓ := by
  rcases x with ⟨b, x⟩
  rw [selectedBatchLaw_weight] at hx
  exact hl b (pos_of_mul_pos_left hx ((respond h b).nonneg x)) x
    (pos_of_mul_pos_right hx ((select h).nonneg b))

end Cslib.Probability.StochasticOracle.AdaptiveSelection
