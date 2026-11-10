/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper
import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum
import Mathlib.Tactic

/-!
# Correlated concurrent native upper-policy numerical client

The same constructed controller is run on one positive-dual set-cover input.
Both simultaneous calls return the covering singleton. Their invoices share
one random bit: both bill one or both bill two. Actual selected
conditional laws supply productivity one and batch invoice at most four; neither
condition is assumed. This supplements the empty-ground boundary client.
-/

noncomputable section
open Cslib Cslib.Probability StochasticOracle NativeRetention ConcurrentBatch NativeBatch
open NativeOpenExecution NativeInterface Turing Trace Quantitative
open scoped NNReal ENNReal
open MeasureTheory
private def lim : Limits 2 := ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩
private def invoice (b : Bool) : ℕ := if b then 2 else 1
private def path (b : Bool) : CallTrace := ⟨some (0, [true]), fun _ => invoice b,
  by intro _ _ _; rfl⟩
private def sampler : Sampler 2 Unit := fun _ _ =>
  (PMF.uniformOfFintype Bool).map fun b => (fun _ => path b, ())
/-- The two actual potential call invoices are perfectly coupled, with both
values occurring. In particular this joint law is not two independent invoices. -/
example (state : ServerState 2 Unit) (batch : Batch 2) :
    ((sampler state batch).map (fun draw =>
      decide (((draw.1 0).report 1).2 = 1 ∧ ((draw.1 1).report 1).2 = 1))) true = 1 / 2 := by
  simp [sampler, PMF.map_comp, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, path, CallTrace.report, invoice]

example (state : ServerState 2 Unit) (batch : Batch 2) :
    ((sampler state batch).map (fun draw =>
      decide (((draw.1 0).report 1).2 = 1))) true = 1 / 2 := by
  simp [sampler, PMF.map_comp, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, path, CallTrace.report, invoice]

example (state : ServerState 2 Unit) (batch : Batch 2) :
    ((sampler state batch).map (fun draw =>
      decide (((draw.1 0).report 1).2 = 1 ∧ ((draw.1 1).report 1).2 = 1))) true ≠
    ((sampler state batch).map (fun draw =>
      decide (((draw.1 0).report 1).2 = 1))) true *
    ((sampler state batch).map (fun draw =>
      decide (((draw.1 1).report 1).2 = 1))) true := by
  norm_num [sampler, PMF.map_comp, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, path, CallTrace.report, invoice]
  intro heq
  have hreal := congrArg ENNReal.toReal heq
  norm_num at hreal

private def both : Batch 2 := ⟨fun _ => some [], ⟨0, by simp [active]⟩⟩

/-- The correlation is visible in the actual selected concurrent report, not
merely in latent or unselected trajectories. -/
example (state : ServerState 2 Unit) :
    ((sampler state both).map (fun draw =>
      let r := (ConcurrentBatch.observe lim 1 both draw.1).report
      decide (((r 0).getD (none, 0)).2 = 1) &&
        decide (((r 1).getD (none, 0)).2 = 1))) true = 1 / 2 := by
  simp [sampler, PMF.map_comp, PMF.map_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, both, ConcurrentBatch.observe, path,
    CallTrace.report, CallTrace.response, invoice]

private theorem response {k : ℕ} {R : Type} {input : List Bool}
    (machine : MultiTapePTM k Bool R Unit)
    (prior : PMF (Trace.State 2 k Unit R input)) (o : Observation 2)
    (ho : o ∈ ((select lim sampler machine prior).map (Quantitative.observe lim)).support)
    (hi : o.issued = true) (next : Trace.State 2 k Unit R input)
    (hn : next ∈
          (conditional lim sampler machine prior o).support) :
    ∃ receipt b, next.records = some receipt :: o.history ∧
      receipt.report = fun i => (receipt.batch.slots i).map
        (fun _ => (some [true], invoice b)) := by
  have h := History.conditional_issued_property lim sampler machine
    (fun receipt => ∃ b, receipt.report = fun i => (receipt.batch.slots i).map
      (fun _ => (some [true], invoice b))) prior o ho hi next hn
    (by
      intro world batch _ paths privateState hs
      obtain ⟨b, _, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      cases hpair
      refine ⟨b, ?_⟩
      funext i
      simp [ConcurrentBatch.observe, path, CallTrace.report, CallTrace.response])
  obtain ⟨receipt, hr, b, hreport⟩ := h
  exact ⟨receipt, b, hr, hreport⟩

private def data : GuardedStartup.Input := ⟨⟨⟨[[0]], [1], [1], 1, []⟩, 1, 2, []⟩, 1⟩
private theorem valid : Valid data.startup.system := by
  constructor
  · intro j; cases j <;> norm_num [data]
  · intro e; cases e <;> norm_num [data]
  · intro j; cases j <;> norm_num [data, elements, ground, List.range_succ]

/-- One positive lower invoice envelope holds for every admitted competitor,
not only the block controller; the source sampler and hidden seed are fixed. -/
private theorem lower_envelopes : BatchOptimum.LowerEnvelopes lim sampler data () valid 1 1 1 := by
  constructor
  intro k R _ machine
  dsimp only
  intro _ t _ o ho
  constructor
  · intro next _
    have hs : AdaptiveSelection.revealed (BatchOptimum.finiteInstance data.startup.system valid)
        (Coverage.proposal data.startup.system.rows.length) next.records ⊆
        (BatchOptimum.finiteInstance data.startup.system valid).ground := by
      rw [Coverage.revealed_source]
      exact PartialCover.Instance.covered_subset _ _
    calc
      _ ≤ (BatchOptimum.finiteInstance data.startup.system valid).ground.card :=
        Finset.card_le_card (Finset.sdiff_subset.trans hs)
      _ = 1 := by norm_num [BatchOptimum.finiteInstance, instanceOf, ground, data,
        List.range_succ]
  constructor
  · intro _
    unfold History.conditionalMean mean History.newest
    rw [DiscreteComparison.indicator_mean]
    exact PMF.coe_le_one _ _
  · intro hi
    unfold Quantitative.conditionalMean mean
    calc
      1 = ∑' next, conditional lim sampler machine (law lim sampler machine t
          ⟨machine.initialConfig (GuardedStartup.encoding data),
            ⟨ConcurrentBatch.initial (), []⟩⟩) o next * 1 := by simp [PMF.tsum_coe]
      _ ≤ _ := by
        apply tsum_le_tsum
        intro next
        by_cases hn : next ∈ (conditional lim sampler machine (law lim sampler machine t
            ⟨machine.initialConfig (GuardedStartup.encoding data),
              ⟨ConcurrentBatch.initial (), []⟩⟩) o).support
        · obtain ⟨receipt, b, hr, hreport⟩ := response machine _ o ho hi next hn
          apply mul_le_mul' le_rfl
          simp only [Quantitative.newest, hr, List.headD_cons, charge, Option.elim_some]
          obtain ⟨i, hi⟩ := receipt.batch.nonempty
          have hval : 1 ≤ ((receipt.report i).getD (none, 0)).2 := by
            rw [hreport]
            have hactive : (receipt.batch.slots i).isSome := by simpa [active] using hi
            cases he : receipt.batch.slots i with
            | none => simp [he] at hactive
            | some word => cases b <;> simp [he, invoice]
          have hb : 1 ≤ receipt.tokens := by
            unfold Exchange.tokens
            exact hval.trans (Finset.single_le_sum (f := fun j =>
              ((receipt.report j).getD (none, 0)).2) (fun _ _ => Nat.zero_le _) hi)
          exact_mod_cast hb
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]

example : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit),
    Quantitative.expected lim sampler program charge 2
      ⟨program.initialConfig (GuardedStartup.encoding data),
        ⟨ConcurrentBatch.initial (), []⟩⟩ ≤ 4 ∧
    1 ≤
      (NativeUnboundedExecution.terminal program (environment lim sampler)
        ⟨program.initialConfig (GuardedStartup.encoding data),
          ⟨ConcurrentBatch.initial (), []⟩⟩).map
        (BatchOutput.certified lim data.startup.system valid) true ∧
    1 ≤ BatchOptimum.optimum lim sampler data () valid 1 ∧
    BatchOptimum.optimum lim sampler data () valid 1 ≤ 4 := by
  let impl := BatchPlanner.controller 2 2
  let tapes := impl.tapes
  let R := impl.Controls
  have hR := impl.finite
  let program := impl.program
  have hp := BatchOutput.upper_controller (n := 2) 2
  refine ⟨tapes, R, hR, program, ?_⟩
  let world : World tapes R Unit (ServerState 2 Unit) (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial (), []⟩⟩
  let I := instanceOf data.startup.system valid
  let parse := BatchReceipts.proposal (n := 2) data.startup.system
  have history (o : Observation 2)
      (ho : o ∈ ((select lim sampler program (law lim sampler program 0 world)).map
        (Quantitative.observe lim)).support) : o.history = [] := by
    obtain ⟨picked, hp, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    simp only [select, law, ObservedProcess.stateLaw, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hp
    obtain ⟨state, rfl, hit, _, rfl⟩ := hp
    rfl
  have Hprod : ∀ t < lim.turns, ∀ o ∈ ((select lim sampler program
      (law lim sampler program t world)).map (Quantitative.observe lim)).support,
      o.issued = true → ENNReal.ofReal (1 : ℝ) ≤ History.conditionalMean lim sampler program
        (law lim sampler program t world) o
        (fun h x => if AdaptiveSelection.productive I 1 parse 1 h x then 1 else 0) := by
    intro t ht o ho hi
    have ht0 : t = 0 := by change t < 1 at ht; omega
    subst t
    have hh := history o ho
    unfold History.conditionalMean mean
    have he (next : Trace.State 2 tapes Unit R (GuardedStartup.encoding data))
        (hn : next ∈
          (conditional lim sampler program (law lim sampler program 0 world) o).support) :
        History.newest (fun h x => if AdaptiveSelection.productive I 1 parse 1 h x
          then (1 : ℝ≥0∞) else 0) next = 1 := by
      obtain ⟨receipt, b, hr, hreport⟩ := response program _ o ho hi next hn
      simp only [History.newest, hr, List.tail_cons, List.headD_cons, hh]
      have hparse : parse [] (some receipt) = [{0}] ∨
          parse [] (some receipt) = [{0}, {0}] := by
        dsimp only [parse]
        rw [BatchReceipts.proposal_eq]
        simp only [Option.elim_some, hreport]
        have hn := receipt.batch.nonempty
        cases h0 : receipt.batch.slots 0 <;> cases h1 : receipt.batch.slots 1
        · obtain ⟨i, hi⟩ := hn
          fin_cases i <;> simp [active, h0, h1] at hi
        all_goals norm_num [proposals, List.ofFn_succ, h0, h1, data, decodeFamily,
          List.filterMap_cons, invoice]
        all_goals decide
      rcases hparse with hparse | hparse
      all_goals
        norm_num [AdaptiveSelection.productive, AdaptiveSelection.residual,
          AdaptiveSelection.selected, hparse, I, instanceOf, elements, ground,
          data, PartialCover.Instance.retain, PartialCover.Instance.Certified,
          PartialCover.Instance.covered, PartialCover.Instance.cost, List.range_succ]
    apply le_of_eq
    symm
    calc
      _ = ∑' next,
          conditional lim sampler program (law lim sampler program 0 world) o next * 1 := by
        apply tsum_congr; intro next
        by_cases hn : next ∈
            (conditional lim sampler program (law lim sampler program 0 world) o).support
        · rw [he next hn]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
      _ = _ := by simp [PMF.tsum_coe]
  have Hcost : ∀ t < lim.turns, ∀ o ∈ ((select lim sampler program
      (law lim sampler program t world)).map (Quantitative.observe lim)).support,
      o.issued = true → Quantitative.conditionalMean lim sampler program
        (law lim sampler program t world) o charge ≤ 4 := by
    intro t ht o ho hi
    unfold Quantitative.conditionalMean mean
    calc
      _ ≤ ∑' next,
          conditional lim sampler program (law lim sampler program t world) o next * 4 := by
        apply tsum_le_tsum; intro next
        by_cases hn : next ∈
            (conditional lim sampler program (law lim sampler program t world) o).support
        · obtain ⟨receipt, b, hr, hreport⟩ := response program _ o ho hi next hn
          apply mul_le_mul_right
          simp only [Quantitative.newest, hr, List.headD_cons, charge, Option.elim_some]
          have hb : receipt.tokens ≤ 4 := by
            unfold Exchange.tokens
            apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (by intros; omega))
            have hi (i : Fin 2) : ((receipt.report i).getD (none, 0)).2 ≤ 2 := by
              rw [hreport]
              cases hs : receipt.batch.slots i <;> cases b <;> simp [hs, invoice]
            calc
              _ ≤ ∑ _ : Fin 2, 2 := Finset.sum_le_sum (fun i _ => hi i)
              _ = 4 := by norm_num
          exact_mod_cast hb
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
      _ = 4 := by simp [PMF.tsum_coe, ENNReal.tsum_mul_right]
  have hrho : (data.startup.system.rho : ℝ) = 1 := by norm_num [data]
  dsimp only [I, parse] at Hprod
  have h := hp Unit lim sampler data () 1 rfl (by decide) (by decide)
    (by norm_num) (by intro _; norm_num [lim]) (by norm_num [data, lim]) rfl (by decide)
    valid 1 1 (by norm_num [I, instanceOf, ground, data, List.range_succ])
    ⟨1, by norm_num⟩ (by norm_num) 4
    (by simpa only [hrho] using Hprod) Hcost
  obtain ⟨hprogress, _, _, hbudget, _⟩ := h
  have hbin : (1 : ℝ≥0∞) ≤ ENNReal.ofReal
      (∫ j, (if 1 ≤ j then (1 : ℝ) else 0)
        ∂ProbabilityTheory.binomial lim.turns ⟨1, by norm_num⟩) := by
    norm_num [lim, ProbabilityTheory.integral_binomial,
      show Finset.Iic (1 : ℕ) = {0, 1} from by decide]
  have hopt := BatchOptimum.upper (n := 2) 2 Unit lim sampler data () 1 rfl
    (by decide) (by decide) (by norm_num) (by intro _; norm_num [lim])
    (by norm_num [data, lim]) rfl (by decide) valid 1 1
    (by norm_num [I, instanceOf, ground, data, List.range_succ])
    ⟨1, by norm_num⟩ (by norm_num) 4 (by simpa only [hrho] using Hprod) Hcost 1 hbin
  obtain ⟨_, _, hoptbudget, _⟩ := hopt
  have hlo := BatchOptimum.lower lim sampler data () valid 1 1 1 1 1
    (by intro q hq; have hq0 : q = 0 := by omega
        subst q; norm_num [instanceOf, ground, data, List.range_succ])
    (by norm_num) (by norm_num) lower_envelopes
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [lim] using hbudget
  · simpa [hrho, lim, ProbabilityTheory.integral_binomial,
      show Finset.Iic (1 : ℕ) = {0, 1} from by decide] using hprogress
  · simpa using hlo
  · simpa [lim] using hoptbudget

/-- Divergent terminal mass is never counted as receipt or tape success. -/
example (tapes : ℕ) (R : Type) :
    BatchOutput.retained data.startup.system valid
      (none : Option (World tapes R Unit (ServerState 2 Unit) [])) = false ∧
    BatchOutput.certified lim data.startup.system valid
      (none : Option (World tapes R Unit (ServerState 2 Unit) [])) = false := by
  exact ⟨rfl, rfl⟩
