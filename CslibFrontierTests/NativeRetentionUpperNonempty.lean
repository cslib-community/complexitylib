/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper
import Mathlib.Tactic
/-!
# Nonempty native upper-policy numerical client

The same constructed controller is run on one positive-dual set-cover input.
Every call returns the covering singleton and bills one token. Actual selected
conditional laws supply productivity one and mean invoice at most one; neither
condition is assumed. This supplements the empty-ground boundary client.
-/

noncomputable section
open Cslib Cslib.Probability StochasticOracle NativeRetention ConcurrentBatch NativeBatch
open NativeOpenExecution NativeInterface Turing Trace Quantitative
open scoped NNReal ENNReal
open MeasureTheory
private def lim : Limits 1 := ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩
private def path : CallTrace := ⟨some (0, [true]), fun _ => 1, by intro _ _ _; rfl⟩
private def sampler : Sampler 1 Unit := fun _ _ => PMF.pure (fun _ => path, ())
private theorem response {k : ℕ} {R : Type} {input : List Bool}
    (machine : MultiTapePTM k Bool R Unit)
    (prior : PMF (Trace.State 1 k Unit R input)) (o : Observation 1)
    (ho : o ∈ ((select lim sampler machine prior).map (Quantitative.observe lim)).support)
    (hi : o.issued = true) (next : Trace.State 1 k Unit R input)
    (hn : next ∈
          (conditional lim sampler machine prior o).support) :
    ∃ receipt, next.records = some receipt :: o.history ∧
      receipt.report 0 = some (some [true], 1) := by
  simp only [conditional, PMF.mem_support_bind_iff] at hn
  obtain ⟨picked, hp, hn⟩ := hn
  obtain ⟨hp, he⟩ := PMF.mem_support_of_posterior _ _ _ ho _ hp
  have his := congrArg Observation.issued he
  change batchIssued lim picked.checkpoint = o.issued at his
  rw [hi] at his
  have hh := congrArg Observation.history he
  change picked.before.records = o.history at hh
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨phase, hr, rfl⟩ := hn
  cases hc : picked.checkpoint with
  | none => simp [hc, batchIssued, sourceSignal] at his
  | some hit =>
    cases hit with
    | ready w => simp [hc, batchIssued, sourceSignal] at his
    | pending chosen =>
      cases chosen with
      | halted w => simp [hc, batchIssued, sourceSignal] at his
      | «local» w => simp [hc, batchIssued, sourceSignal] at his
      | query w op control =>
        cases op
        cases ha : admit lim w.memory.privateState (w.config.channels ()).queryBuffer with
        | none => simp [hc, batchIssued, sourceSignal, ha] at his
        | some batch =>
          simp only [hc, respondSource, phaseStep, dispatch, environment,
            serve_accepted _ _ _ _ _ ha, sampler, PMF.pure_map,
            PMF.mem_support_pure_iff] at hr
          subst phase
          refine ⟨_, by rw [hh]; rfl, ?_⟩
          have hslot : (batch.slots 0).isSome = true := by
            obtain ⟨i, hi⟩ := batch.nonempty
            have he : i = 0 := Subsingleton.elim _ _
            simpa [active, he] using hi
          cases hvalue : batch.slots 0 with
          | none => simp [hvalue] at hslot
          | some word => simp [ConcurrentBatch.observe, hvalue, path,
              CallTrace.report, CallTrace.response]

private def data : GuardedStartup.Input := ⟨⟨⟨[[0]], [1], [1], 1, []⟩, 1, 1, []⟩, 1⟩
private theorem valid : Valid data.startup.system := by
  constructor
  · intro j; cases j <;> norm_num [data]
  · intro e; cases e <;> norm_num [data]
  · intro j; cases j <;> norm_num [data, elements, ground, List.range_succ]

example : ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
    (program : MultiTapePTM tapes Bool R Unit),
    Quantitative.expected lim sampler program charge 2
      ⟨program.initialConfig (GuardedStartup.encoding data),
        ⟨ConcurrentBatch.initial (), []⟩⟩ ≤ 1 ∧
    ENNReal.ofReal (∫ j, (if 1 ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 1 ⟨1, by norm_num⟩) ≤
      (law lim sampler program 1
        ⟨program.initialConfig (GuardedStartup.encoding data),
          ⟨ConcurrentBatch.initial (), []⟩⟩).map
        (fun state => Retained.complete (instanceOf data.startup.system valid) 1
          (BatchReceipts.proposal data.startup.system) state.records) true := by
  obtain ⟨tapes, R, hR, program, hp⟩ := BatchUpper.exists_native_upper_controller (n := 1) 1
  refine ⟨tapes, R, hR, program, ?_⟩
  let world : World tapes R Unit (ServerState 1 Unit) (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial (), []⟩⟩
  let I := instanceOf data.startup.system valid
  let parse := BatchReceipts.proposal (n := 1) data.startup.system
  have history (o : Observation 1)
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
    have he (next : Trace.State 1 tapes Unit R (GuardedStartup.encoding data))
        (hn : next ∈
          (conditional lim sampler program (law lim sampler program 0 world) o).support) :
        History.newest (fun h x => if AdaptiveSelection.productive I 1 parse 1 h x
          then (1 : ℝ≥0∞) else 0) next = 1 := by
      obtain ⟨receipt, hr, hreport⟩ := response program _ o ho hi next hn
      have hre : receipt.report = fun _ => some (some [true], 1) := by
        funext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; exact hreport
      simp only [History.newest, hr, List.tail_cons, List.headD_cons, hh]
      have hparse : parse [] (some receipt) = [{0}] := by
        dsimp only [parse]
        rw [BatchReceipts.proposal_eq]
        simp only [Option.elim_some, hre]
        change [(Finset.univ : Finset (Fin 1)).image Fin.val] = [{0}]
        decide
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
        (law lim sampler program t world) o charge ≤ 1 := by
    intro t ht o ho hi
    unfold Quantitative.conditionalMean mean
    calc
      _ ≤ ∑' next,
          conditional lim sampler program (law lim sampler program t world) o next * 1 := by
        apply tsum_le_tsum; intro next
        by_cases hn : next ∈
            (conditional lim sampler program (law lim sampler program t world) o).support
        · obtain ⟨receipt, hr, hreport⟩ := response program _ o ho hi next hn
          apply mul_le_mul_right
          simp only [Quantitative.newest, hr, List.headD_cons, charge, Option.elim_some]
          have hb : receipt.tokens ≤ 1 := by
            unfold Exchange.tokens
            apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (by intros; omega))
            simp [hreport]
          exact_mod_cast hb
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hn]
      _ = 1 := by simp [PMF.tsum_coe]
  have hrho : (data.startup.system.rho : ℝ) = 1 := by norm_num [data]
  dsimp only [I, parse] at Hprod
  have h := hp Unit lim sampler data () 1 rfl (by decide) (by decide)
    (by norm_num) (by intro _; norm_num [lim]) (by norm_num [data, lim]) rfl (by decide)
    valid 1 1 (by norm_num [I, instanceOf, ground, data, List.range_succ])
    ⟨1, by norm_num⟩ (by norm_num) 1
    (by simpa only [hrho] using Hprod) Hcost
  obtain ⟨hprogress, _, _, hbudget, _⟩ := h
  refine ⟨?_, ?_⟩
  · simpa only [lim, ENNReal.coe_one, Nat.cast_one, mul_one] using hbudget
  · simpa only [hrho, lim] using hprogress
