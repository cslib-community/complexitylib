/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum
import CslibFrontier.Computability.Probabilistic.NativeBatch.InitialEpoch
import Mathlib.Tactic

/-!
# Positive-deadline, nontrivial native necessary success bound

Two concurrent responses and their invoices share one fair bit. Every issued
batch takes exactly one unit of oracle time. On a satisfiable positive-dual
singleton instance, the named native controller succeeds with probability exactly
one half. The necessary success-target bound is one half for every admitted
competitor on this same oracle, not a zero-deadline or zero-turn edge.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface
open StochasticOracle NativeRetention ConcurrentBatch NativeBatch Trace Quantitative PartialCover
open scoped NNReal ENNReal
open MeasureTheory

private abbrev data : GuardedStartup.Input := ⟨⟨⟨[[0]], [1], [1], 1, []⟩, 1, 2, []⟩, 1⟩
private theorem valid : Valid data.startup.system := by
  constructor
  · intro j; cases j <;> norm_num
  · intro e; cases e <;> norm_num
  · intro j; cases j <;> norm_num [elements, ground, List.range_succ]
private def limits : Limits 2 := ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩
private def path (b : Bool) : CallTrace :=
  ⟨some (1, [b]), fun _ => if b then 2 else 1, by intro _ _ _; rfl⟩
private def sample : Sampler 2 Unit := fun _ _ =>
  (PMF.uniformOfFintype Bool).map fun b => (fun _ => path b, ())
private def batchReceipt (batch : Batch 2) (b : Bool) : Exchange 2 :=
  ConcurrentBatch.observe limits 1 batch (fun _ => path b)
private def nativeStart {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit) :
    World k Control Unit (ServerState 2 Unit) (GuardedStartup.encoding data) :=
  ⟨machine.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial (), []⟩⟩

private structure ReceiptFacts (batch : Batch 2) (b : Bool) : Prop where
  duration : (batchReceipt batch b).duration = 1
  lower : 1 ≤ (batchReceipt batch b).tokens
  upper : (batchReceipt batch b).tokens ≤ 4
  productive : AdaptiveSelection.productive (instanceOf data.startup.system valid) 1
    (BatchReceipts.proposal data.startup.system) 1 [] (some (batchReceipt batch b)) = b
  revealed : AdaptiveSelection.reveals (BatchOptimum.finiteInstance data.startup.system valid)
    (Coverage.proposal 1) [] (some (batchReceipt batch b)) = b

private theorem receipt_facts (batch : Batch 2) (b : Bool) : ReceiptFacts batch b := by
  cases h0 : batch.slots 0 <;> cases h1 : batch.slots 1
  all_goals
    try
      obtain ⟨i, hi⟩ := batch.nonempty
      fin_cases i <;> simp [active, h0, h1] at hi
  all_goals cases b <;> constructor <;>
    norm_num [batchReceipt, ConcurrentBatch.observe, Exchange.duration, Exchange.tokens, limits,
      path, CallTrace.stop, CallTrace.report, CallTrace.response, active,
      List.ofFn_succ, Finset.univ_fin2, h0, h1, AdaptiveSelection.productive,
      AdaptiveSelection.reveals,
      AdaptiveSelection.revealed, AdaptiveSelection.residual, AdaptiveSelection.selected,
      BatchOptimum.finiteInstance, instanceOf, BatchReceipts.proposal_eq, Coverage.proposal,
      BatchStopping.proposal, Packets.families_report, proposals, decodeFamily,
      Instance.covered, Instance.cost, Instance.retain, Instance.Certified,
      elements, ground, List.range_succ]
  all_goals simp_all [Finset.filter_insert, List.filterMap_nil,
    Finset.filter_singleton, Instance.retain, Instance.Certified, Instance.covered,
    Instance.cost, elements, ground,
    Finset.sum_insert, Finset.sup_insert]

private theorem first {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Unit)
    (o : Observation 2)
    (ho : o ∈ ((select limits sample machine
      (law limits sample machine 0 (nativeStart machine))).map
      (Quantitative.observe limits)).support) (hi : o.issued = true) :
    ∃ batch : Batch 2,
      (conditional limits sample machine (law limits sample machine 0 (nativeStart machine)) o).map
        State.records = (PMF.uniformOfFintype Bool).map fun b => [some (batchReceipt batch b)] := by
  obtain ⟨batch, _, _, h⟩ := InitialEpoch.conditional_records limits sample machine
    (nativeStart machine) o ho hi
  exact ⟨batch, by simpa only [sample, PMF.map_comp, Function.comp_def, nativeStart,
    ConcurrentBatch.initial, limits, law, ObservedProcess.stateLaw, batchReceipt,
    tsub_zero] using h⟩

private theorem mean_first {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (o : Observation 2)
    (ho : o ∈ ((select limits sample machine
      (law limits sample machine 0 (nativeStart machine))).map
      (Quantitative.observe limits)).support) (hi : o.issued = true)
    (f : List (Record 2) → ℝ≥0∞) :
    ∃ batch : Batch 2, mean (conditional limits sample machine
      (law limits sample machine 0 (nativeStart machine)) o) (fun state => f state.records) =
      ∑' b, (PMF.uniformOfFintype Bool) b * f [some (batchReceipt batch b)] := by
  obtain ⟨batch, h⟩ := first machine o ho hi
  refine ⟨batch, ?_⟩
  rw [mean, ← PMF.tsum_map_mul _ State.records f, h, PMF.tsum_map_mul]

private theorem cost_first {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (o : Observation 2)
    (ho : o ∈ ((select limits sample machine
      (law limits sample machine 0 (nativeStart machine))).map
      (Quantitative.observe limits)).support) (hi : o.issued = true) :
    1 ≤ Quantitative.conditionalMean limits sample machine
      (law limits sample machine 0 (nativeStart machine)) o charge ∧
    Quantitative.conditionalMean limits sample machine
      (law limits sample machine 0 (nativeStart machine)) o charge ≤ 4 := by
  obtain ⟨batch, h⟩ := mean_first machine o ho hi
    (fun h => (h.headD none).elim 0 (fun r => (r.tokens : ℝ≥0∞)))
  unfold Quantitative.conditionalMean Quantitative.newest charge
  rw [h]
  simp only [List.headD_cons, Option.elim_some]
  have hlo := tsum_le_tsum (fun b : Bool => mul_le_mul' (le_refl ((PMF.uniformOfFintype Bool) b))
    (show (1 : ℝ≥0∞) ≤ (batchReceipt batch b).tokens from by
      exact_mod_cast (receipt_facts batch b).lower))
  have hhi := tsum_le_tsum (fun b : Bool => mul_le_mul' (le_refl ((PMF.uniformOfFintype Bool) b))
    (show ((batchReceipt batch b).tokens : ℝ≥0∞) ≤ 4 from by
      exact_mod_cast (receipt_facts batch b).upper))
  constructor
  · simpa only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, mul_one] using hlo
  · simpa only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, mul_one] using hhi

private theorem late_not_issued {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (o : Observation 2)
    (ho : o ∈ ((select limits sample machine
      (law limits sample machine 1 (nativeStart machine))).map
      (Quantitative.observe limits)).support) : o.issued = false :=
  History.final_not_issued limits sample machine (nativeStart machine)
    (NativeBatch.initial_invariant limits ()) o ho

private theorem lower_envelopes : BatchOptimum.LowerEnvelopes limits sample data () valid 1
    (ENNReal.ofReal (1 / 2 : ℝ)) 1 := by
  constructor
  intro k Control _ machine
  dsimp only
  intro _ t ht o ho
  constructor
  · intro next _
    have hs : AdaptiveSelection.revealed (BatchOptimum.finiteInstance data.startup.system valid)
        (Coverage.proposal 1) next.records ⊆
        (BatchOptimum.finiteInstance data.startup.system valid).ground := by
      change AdaptiveSelection.revealed _
        (Coverage.proposal data.startup.system.rows.length) _ ⊆ _
      rw [Coverage.revealed_source]
      exact Instance.covered_subset _ _
    calc
      _ ≤ (BatchOptimum.finiteInstance data.startup.system valid).ground.card :=
        Finset.card_le_card (Finset.sdiff_subset.trans hs)
      _ = 1 := by norm_num [BatchOptimum.finiteInstance, instanceOf, ground, List.range_succ]
  constructor
  · intro hi
    have ht' : t = 0 ∨ t = 1 := by change t < 2 at ht; omega
    rcases ht' with rfl | rfl
    · obtain ⟨batch, h⟩ := mean_first machine o ho hi (fun h =>
        if AdaptiveSelection.reveals (BatchOptimum.finiteInstance data.startup.system valid)
          (Coverage.proposal 1) h.tail (h.headD none) then 1 else 0)
      unfold History.conditionalMean History.newest
      change mean _ (fun state => if AdaptiveSelection.reveals _ (Coverage.proposal 1)
        state.records.tail (state.records.headD none) then 1 else 0) ≤ _
      simp only [nativeStart] at h
      rw [h]
      simp only [List.tail_cons, List.headD_cons, (receipt_facts batch _).revealed]
      norm_num [tsum_bool, PMF.uniformOfFintype_apply, ENNReal.ofReal_div_of_pos]
    · simp [late_not_issued machine o ho] at hi
  · intro hi
    have ht' : t = 0 ∨ t = 1 := by change t < 2 at ht; omega
    rcases ht' with rfl | rfl
    · exact (cost_first machine o ho hi).1
    · simp [late_not_issued machine o ho] at hi

private theorem latency {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) :
    Deadline.LowerLatency limits sample machine (nativeStart machine) 1 := by
  intro t ht o ho hi next hn
  have ht' : t = 0 ∨ t = 1 := by change t < 2 at ht; omega
  rcases ht' with rfl | rfl
  · obtain ⟨batch, h⟩ := first machine o ho hi
    have hs := (PMF.mem_support_map_iff State.records _ _).mpr ⟨next, hn, rfl⟩
    rw [h] at hs
    obtain ⟨b, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    rw [← he, List.headD_cons, Option.elim_some, (receipt_facts batch b).duration]
  · simp [late_not_issued machine o ho] at hi

/-- The same constructed native program meets, and is bounded above by, the
nontrivial positive-deadline tail. Every other admitted competitor has the same
necessary one-half target bound, under these derived source envelopes. -/
example :
    let impl := BatchPlanner.controller 2 2
    let world := nativeStart impl.program
    ((NativeUnboundedExecution.terminal impl.program (environment limits sample) world).map
      (BatchOutput.certified limits data.startup.system valid)) true = 1 / 2 ∧
    ∀ η, (BatchOptimum.costs limits sample data () valid η).Nonempty → η ≤ 1 / 2 := by
  let impl := BatchPlanner.controller 2 2
  let program := impl.program
  have prod (t : ℕ) (ht : t < limits.turns) (o : Observation 2)
      (ho : o ∈ ((select limits sample program
        (law limits sample program t (nativeStart program))).map
        (Quantitative.observe limits)).support) (hi : o.issued = true) :
      ENNReal.ofReal (1 / 2 : ℝ) ≤ History.conditionalMean limits sample program
        (law limits sample program t (nativeStart program)) o
        (fun h x => if AdaptiveSelection.productive (instanceOf data.startup.system valid) 1
          (BatchReceipts.proposal data.startup.system) 1 h x then 1 else 0) := by
    have ht0 : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨batch, h⟩ := mean_first program o ho hi (fun h =>
      if AdaptiveSelection.productive (instanceOf data.startup.system valid) 1
        (BatchReceipts.proposal data.startup.system) 1 h.tail (h.headD none) then 1 else 0)
    unfold History.conditionalMean History.newest
    rw [h]
    simp only [List.tail_cons, List.headD_cons, (receipt_facts batch _).productive]
    norm_num [tsum_bool, PMF.uniformOfFintype_apply, ENNReal.ofReal_div_of_pos]
  have hu := BatchOutput.upper_controller (n := 2) 2 Unit limits sample data () 1 rfl
    (by decide) (by decide) (by norm_num) (by intro _; norm_num [limits])
    (by norm_num [limits]) rfl (by decide) valid 1 1
    (by norm_num [instanceOf, ground, List.range_succ]) ⟨1 / 2, by norm_num⟩ (by norm_num) 4
    (by simpa only [program, impl, nativeStart,
      (show (data.startup.system.rho : ℝ) = 1 from by norm_num)] using prod)
    (by intro t ht o ho hi; have ht0 : t = 0 := by change t < 1 at ht; omega
        subst t; exact (cost_first program o ho hi).2)
  have hs := BatchAdmission.selectionOnly_controller (n := 2) 2 Unit limits sample data () 1
    rfl (by decide) (by decide) (by decide) (by norm_num)
    (by intro _; norm_num [limits]) (by norm_num [limits]) valid
  have hsel : NativeUnboundedExecution.SelectionOnly program (environment limits sample)
      (candidateParser (n := 2) 1) (decodeFamily 1) (BatchOutput.accept data.startup.system valid)
      (nativeStart program) := by intro fuel next hn C hC _; exact hs fuel next hn C hC rfl
  have hb := BatchOptimum.success_le impl.finite limits sample data () valid program 1 1
    (by intro q hq; have hq0 : q = 0 := by omega
        subst q; norm_num [instanceOf, ground, List.range_succ])
    ⟨1 / 2, by norm_num⟩ 1 1 (by norm_num) lower_envelopes hsel (latency program)
  have hnum : ENNReal.ofReal (∫ j, (if 1 ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 1 ⟨1 / 2, by norm_num⟩) = 1 / 2 := by
    rw [ProbabilityTheory.integral_binomial]
    norm_num [ENNReal.ofReal_div_of_pos,
      show Finset.Iic (1 : ℕ) = {0, 1} from by decide]
  constructor
  · apply le_antisymm
    · simpa only [show Deadline.effectiveTurns limits 1 = 1 from by
        norm_num [Deadline.effectiveTurns, limits], hnum, nativeStart] using hb
    · simpa only [show limits.turns = 1 from rfl, hnum, nativeStart] using hu.1
  · intro η hη
    have h := BatchOptimum.feasible_success_le limits sample data () valid η 1 1
      (by intro q hq; have hq0 : q = 0 := by omega
          subst q; norm_num [instanceOf, ground, List.range_succ])
      ⟨1 / 2, by norm_num⟩ 1 1 (by norm_num) lower_envelopes
      (by intro k Control _ machine; dsimp only; intro _; exact latency machine) hη
    simpa only [show Deadline.effectiveTurns limits 1 = 1 from by
      norm_num [Deadline.effectiveTurns, limits], hnum] using h
