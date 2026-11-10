/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchReceipts
import Mathlib.Tactic

/-!
# Selected-epoch stopping of the constructed native batch controller

[Wang2027], Theorem 5(1), PDF p. 12, Appendix A.5 p. 16. The actual native
program's derived joint terminal law authenticates every accepted receipt prefix.
Its executed guard makes each such prefix incomplete before another batch is
issued. Backward propagation through the actual native trace then establishes
this fact at positive-probability selected epochs, without a representation or
stopping-law premise. Hidden metadata and response correlations remain unrestricted.

This is a stopping bridge for the concrete finite labeled block scheduler.
Reached-only productivity gives the binomial lower bound on actual retained
completion and the survival-sum/`c*r/p`/`c*u` bounds on the complete actual accrued bill.
A finite conditional invoice envelope implies finite total expectation as a
conclusion. Complete certified-output success/deadline transfer and the
common-oracle optimum comparison for that same code remain open.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchUpper
open Turing NativeOpenExecution NativeInterface ConcurrentBatch NativeBatch
open Trace Quantitative BatchReceipts
open scoped NNReal ENNReal
open MeasureTheory
variable {n : ℕ}

/-- One constructed native program satisfies the actual pre-response stopping
conditions needed by the native survival-sum cost theorem. Both issued and
no-call decisions are connected to actual retained completion. The only hypotheses
are original source budgets/cutoffs and ordinary WSC validity. In particular its
history/representation/stopping law is derived rather than supplied. -/
theorem exists_native_stopping_controller (width : ℕ) :
    ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
      (program : MultiTapePTM tapes Bool R Unit),
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system)
        (t : ℕ) (_ : t < limits.turns)
        (o : Observation n)
        (_ : o ∈ ((select limits sample program (law limits sample program t
          ⟨program.initialConfig (GuardedStartup.encoding data),
            ⟨ConcurrentBatch.initial seed, []⟩⟩)).map (Quantitative.observe limits)).support),
        (o.issued = true → Retained.complete (instanceOf data.startup.system hx)
          data.startup.system.rho (BatchReceipts.proposal data.startup.system) o.history = false) ∧
        (o.issued = false → Retained.complete (instanceOf data.startup.system hx)
          data.startup.system.rho (BatchReceipts.proposal data.startup.system)
            o.history = true) := by
  obtain ⟨tapes, R, hR, program, context, hlaw⟩ := BatchPlanner.exists_native_controller n width
  refine ⟨tapes, R, hR, program, ?_⟩
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
  have ht : data.startup.turns ≤ limits.turns := hbudget.le
  let world : World tapes R Unit (ServerState n Private) (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  have hi : Invariant limits world.memory := NativeBatch.initial_invariant limits seed
  have Hfinal (state : Trace.State n tapes Private R (GuardedStartup.encoding data))
      (hs : state ∈ (law limits sample program (limits.turns + 1) world).support) :
      Safe data.startup.system (state.records.filterMap id) ∧
        ((Packets.decision ⟨data.startup.system, n,
          (state.records.filterMap id).map (fun r => (replyOf r).word)⟩).1 = true ∨
          (state.records.filterMap id).length = limits.turns) := by
    have hv := Trace.law_valid limits sample program _ world hi state hs
    have hnat : state.hidden.map worldOf ∈
        (NativeUnboundedExecution.terminal program (environment limits sample) world).support := by
      rw [← Trace.law_native_terminal limits sample program world hi]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨state, hs, rfl⟩
    have hobs := (PMF.mem_support_map_iff
      (Option.map (NativeReplyContext.observe context)) _ _).mpr
      ⟨state.hidden.map worldOf, hnat, rfl⟩
    change _ ∈ ((NativeUnboundedExecution.terminal program (environment limits sample)
      ⟨program.initialConfig (GuardedStartup.encoding data),
        ⟨ConcurrentBatch.initial seed, []⟩⟩).map _).support at hobs
    rw [hlaw] at hobs
    obtain ⟨outcome, ho, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hobs
    have hsafe := run_safe limits sample width data.startup.turns ell hw hc ht he hcut hd
      _ _ _ _ (BatchAdmission.initial_aligned limits width ell data seed hn) (by trivial) outcome ho
    change Safe data.startup.system outcome.memory.privateState.history at hsafe
    have ha := BatchAdmission.run_aligned limits sample width data.startup.turns ell hw hc ht
      he hcut hd _ _ _ _ (BatchAdmission.initial_aligned limits width ell data seed hn) outcome ho
    have hopps : (GuardedStartup.state data).turns ≤ (GuardedStartup.state data).opportunities := by
      change data.startup.turns ≤ data.startup.opportunities
      rw [hn]
      have hm := Nat.mul_le_mul_left data.startup.turns hw
      omega
    have hend := run_end (environment limits sample) _ (GuardedStartup.state data)
      (fun _ => ⟨[], [], 0⟩) ⟨ConcurrentBatch.initial seed, []⟩ (BatchPlanner.request n width)
      le_rfl hopps hallot outcome ho
    have hsys := Feedback.run_original_system _ _ _ _ _ _ outcome ho
    change outcome.state.work.system = data.startup.system at hsys
    have hend' : (Packets.decision ⟨data.startup.system, n,
        outcome.memory.privateState.history.map (fun r => (replyOf r).word)⟩).1 = true ∨
        outcome.memory.privateState.history.length = limits.turns := by
      rcases hend with hdone | hlength
      · left
        have hguard := aligned_decision limits width data.startup.turns ell
          outcome.state outcome.memory ha
        rw [hsys] at hguard
        rw [hguard] at hdone
        exact hdone
      · right
        rw [ha.events] at hlength
        simpa only [GuardedStartup.state, RuntimeControl.initial, List.length_nil,
          Nat.add_zero, hbudget] using hlength
    cases hh : state.hidden with
    | none =>
      simp only [hh, Option.map_none] at heq
      cases heq
    | some phase =>
      cases phase with
      | pending chosen => simp only [Trace.Valid, hh] at hv
      | ready next =>
        have hm := congrArg (Option.map NativeReplyContext.Observation.memory) heq
        simp only [hh, Option.map_some, worldOf, NativeReplyContext.observe,
          Option.some.injEq] at hm
        have hhistory := hv
        simp only [Trace.Valid, hh] at hhistory
        have hevents := hhistory.2
        change next.memory.privateState.history = state.records.filterMap id ++ [] at hevents
        rw [← hm, List.append_nil] at hevents
        exact ⟨hevents ▸ hsafe, hevents ▸ hend'⟩
  have Hprefix (turns : ℕ) (hb : turns ≤ limits.turns + 1)
      (state : Trace.State n tapes Private R (GuardedStartup.encoding data))
      (hs : state ∈ (law limits sample program turns world).support) :
      Safe data.startup.system (state.records.filterMap id) := by
    apply History.law_prefix_property limits sample program
      (fun h => Safe data.startup.system (h.filterMap id)) ?_ _ world
      (fun final hf => (Hfinal final hf).1) turns hb state hs
    intro record history hsafe
    cases record with
    | none => exact hsafe
    | some receipt => exact hsafe.1
  intro t hlt o ho
  constructor
  · intro hissued
    obtain ⟨next, hnext⟩ := (conditional limits sample program
      (law limits sample program t world) o).support_nonempty
    have hs := conditional_support limits sample program _ o ho next hnext
    have hsafe := Hprefix (t + 1) (by omega) next hs
    obtain ⟨record, hrecords⟩ := History.conditional_records limits sample program _ o ho next hnext
    have hsome := conditional_record_isSome limits sample program _ o ho next hnext
    rw [hrecords, List.headD_cons, hissued] at hsome
    cases record with
    | none => simp at hsome
    | some receipt =>
      rw [hrecords] at hsafe
      have hdone := hsafe.2
      have hcomplete := BatchReceipts.completion_eq data.startup.system hx o.history
      rw [← hcomplete]
      exact hdone
  · intro hzero
    obtain ⟨next, hnext⟩ := (conditional limits sample program
      (law limits sample program t world) o).support_nonempty
    have hs := conditional_support limits sample program _ o ho next hnext
    have hdone := History.conditional_no_call_done limits sample program _ o ho hzero next hnext
    have hsome := conditional_record_isSome limits sample program _ o ho next hnext
    obtain ⟨record, hrecords⟩ := History.conditional_records limits sample program _ o ho next hnext
    rw [hrecords, List.headD_cons, hzero] at hsome
    have heq : record = none := by
      cases record with
      | none => rfl
      | some receipt => simp at hsome
    subst record
    obtain ⟨final, hf, heq⟩ := History.done_continuation limits sample program world
      (t + 1) (limits.turns - t) next hs hdone
    have htotal : t + 1 + (limits.turns - t) = limits.turns + 1 := by omega
    rw [htotal] at hf
    have hend := (Hfinal final hf).2
    rw [heq, hrecords] at hend
    simp only [List.filterMap_cons, id_eq] at hend
    have hlength := Trace.law_length limits sample program (t + 1) world next hs
    rw [hrecords, List.length_cons] at hlength
    have hle := List.length_filterMap_le (f := id) (l := o.history)
    have hc : (Packets.decision ⟨data.startup.system, n, words o.history⟩).1 = true := by
      rcases hend with hdone | hlen
      · exact hdone
      · change (o.history.filterMap id).length = limits.turns at hlen
        omega
    rw [← BatchReceipts.completion_eq data.startup.system hx o.history]
    exact hc

/-- Numerical upper progress and stopped-bill bounds for the same constructed
native selector. Productivity is required only on reached, issued batches; the
extension after completion and issued-before-completion law are proved above.
All charges are actual nonnegative accrued receipts. Finiteness is concluded
from the finite conditional source envelope, not assumed for the total bill. -/
theorem exists_native_upper_controller (width : ℕ) :
    ∃ (tapes : ℕ) (R : Type) (_ : Finite R)
      (program : MultiTapePTM tapes Bool R Unit),
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system),
      let world : World tapes R Unit (ServerState n Private) (GuardedStartup.encoding data) :=
        ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
      let I := instanceOf data.startup.system hx
      let parse := BatchReceipts.proposal data.startup.system
      ∀ (a r : ℕ) (_ : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (_ : 0 < (p : ℝ))
        (c : ℝ≥0)
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → ENNReal.ofReal p ≤ History.conditionalMean limits sample program
            (law limits sample program t world) o
            (fun h x => if AdaptiveSelection.productive I data.startup.system.rho parse a h x
              then 1 else 0))
        (_ : ∀ t < limits.turns, ∀ o ∈ ((select limits sample program
          (law limits sample program t world)).map (Quantitative.observe limits)).support,
          o.issued = true → Quantitative.conditionalMean limits sample program
            (law limits sample program t world) o charge ≤ c),
        ENNReal.ofReal (∫ j, (if r ≤ j then (1 : ℝ) else 0)
          ∂ProbabilityTheory.binomial limits.turns p) ≤
          (law limits sample program limits.turns world).map
            (fun state => Retained.complete I data.startup.system.rho parse state.records) true ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * ENNReal.ofReal
            (∑ t ∈ Finset.range limits.turns, binomialFailure p r t) ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * ENNReal.ofReal (r / p) ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * limits.turns ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≠ ∞ := by
  obtain ⟨tapes, R, hR, program, hstop⟩ := exists_native_stopping_controller (n := n) width
  refine ⟨tapes, R, hR, program, ?_⟩
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
  have ht : data.startup.turns ≤ limits.turns := hbudget.le
  dsimp only
  intro a r hr p hp c Hprod Hcost
  let world : World tapes R Unit (ServerState n Private) (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  let I := instanceOf data.startup.system hx
  let parse := BatchReceipts.proposal (n := n) data.startup.system
  have hguard := hstop Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
  have Hfull (t : ℕ) (hlt : t < limits.turns) (o : Observation n)
      (ho : o ∈ ((select limits sample program
        (law limits sample program t world)).map (Quantitative.observe limits)).support) :
      ENNReal.ofReal p ≤ History.conditionalMean limits sample program
        (law limits sample program t world) o
        (fun h x => if AdaptiveSelection.productive I data.startup.system.rho parse a h x
          then 1 else 0) := by
    cases hi : o.issued with
    | true => exact Hprod t hlt o ho hi
    | false =>
      have hdone := (hguard t hlt o ho).2 hi
      rw [Retained.conditional_productive_of_complete limits sample program I
        data.startup.system.rho parse a _ o ho hdone]
      exact ENNReal.ofReal_le_one.mpr p.2.2
  have Hbefore (t : ℕ) (hlt : t < limits.turns) (o : Observation n)
      (ho : o ∈ ((select limits sample program
        (law limits sample program t world)).map (Quantitative.observe limits)).support) :
      o.issued = true → Retained.complete I data.startup.system.rho parse o.history = false :=
    (hguard t hlt o ho).1
  have hi : Invariant limits world.memory := NativeBatch.initial_invariant limits seed
  have hprogress := Retained.completion limits sample program I data.startup.system.rho
    parse a r limits.turns hr p world Hfull
  have htail := Retained.cost_tail_sum limits sample program I data.startup.system.rho
    parse a r limits.turns hr p c world Hfull Hbefore Hcost
  have hmean := Retained.cost_mean limits sample program I data.startup.system.rho
    parse a r limits.turns hr p hp c world Hfull Hbefore Hcost
  rw [← History.final_expected_static limits sample program world hi charge rfl] at htail hmean
  have hbudgetCost := (Quantitative.cost_upper_budget limits sample program c limits.turns
    world hi Hcost).1
  rw [← History.final_expected_static limits sample program world hi charge rfl] at hbudgetCost
  exact ⟨hprogress, htail, hmean, hbudgetCost, ne_top_of_le_ne_top (by finiteness) hmean⟩

end Cslib.Probability.StochasticOracle.NativeRetention.BatchUpper
