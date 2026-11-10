/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Compiled native output and oracle-deadline certification

[Wang2027], Theorem 5(1), PDF p. 12, Appendix A.5 p. 16. The model on PDF
p. 5 explicitly excludes local computation time from deadline D. Here elapsed
means the actual oracle ledger: sums of concurrent batch maxima, with cutoffs
and cancellation. No wall-clock bound on local instructions is claimed; arbitrary
finite response words need response-dependent local processing time.

`output_controller` is a property of the explicitly named `BatchPlanner.controller`,
which also carries the proved feedback law and admission/stopping/bill properties.
`terminal_completion` identifies its final native receipts with epoch completion.
`upper_controller` consequently proves the binomial lower bound on actual certified
halted tape output together with all three stopped-bill bounds for that same code.
No representation, success, halting, integrability or resource conclusion is a
hypothesis. `BatchOptimum` compares this code with the common-oracle native optimum.
The fixed block scheduler, original input codec and discrete interface are material
model restrictions; unrestricted source Theorems 5/6 remain separate obligations.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
open Turing NativeOpenExecution NativeInterface ConcurrentBatch NativeBatch
open Trace Quantitative
open scoped NNReal ENNReal
open MeasureTheory
variable {n k : ℕ} {R Private : Type} {input : List Bool}

/-- Completion read from actual native terminal source receipts. Divergence is
not success; this event does not redefine the accrued bill on divergent paths. -/
@[expose] def retained (x : Input) (hx : Valid x)
    (outcome : Option (World k R Unit (ServerState n Private) input)) : Bool :=
  outcome.any fun world => Retained.complete (instanceOf x hx) x.rho
    (BatchReceipts.proposal x) (world.memory.privateState.history.map some)

open scoped Classical in
/-- The fixed original-input cover/dual certificate used to count successful
outputs. Failed decoded families need not have source provenance. -/
@[expose] def accept (x : Input) (hx : Valid x) (C : Finset (Fin x.rows.length)) : Bool :=
  decide ((instanceOf x hx).covered (C.image Fin.val) = (instanceOf x hx).ground ∧
    (instanceOf x hx).cost (C.image Fin.val) ≤
      (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e)

open scoped Classical in
/-- Successful native output means a halted, decoded original family with full
coverage, its derived dual bound, and the source's oracle-only deadline. -/
@[expose] def certified (limits : Limits n) (x : Input) (hx : Valid x)
    (outcome : Option (World k R Unit (ServerState n Private) input)) : Bool :=
  outcome.any fun world =>
    (NativeOpenSelection.result (decodeFamily x.rows.length) world).any fun C =>
      accept x hx C && decide (world.memory.privateState.elapsed ≤ limits.deadline)

/-- The actual constructed native program transports receipt completion to
certified halted tape output under one fixed sampler and seed. This is a lower
comparison of genuine terminal event probabilities, not an assumed success law. -/
theorem output_controller (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n) (_ : data.startup.turns ≤ limits.turns)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (hx : Valid data.startup.system),
        let μ := NativeUnboundedExecution.terminal program (environment limits sample)
          ⟨program.initialConfig (GuardedStartup.encoding data),
            ⟨ConcurrentBatch.initial seed, []⟩⟩
        (μ.map (retained data.startup.system hx)) true ≤
          (μ.map (certified limits data.startup.system hx)) true := by
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let context := impl.context
  have hp := BatchAdmission.admitted_controller (n := n) width
  dsimp only
  intro Private limits sample data seed ell hn hw hc ht he hcut hd hx
  apply PMF.map_true_mono
  intro outcome ho hcomplete
  cases outcome with
  | none => simp [retained] at hcomplete
  | some next =>
    have hhalt := ((NativeUnboundedExecution.terminal_support program
      (environment limits sample) _ next).mp ho).1
    have hobs := (PMF.mem_support_map_iff
      (Option.map (NativeReplyContext.observe context)) _ _).mpr ⟨some next, ho, rfl⟩
    obtain ⟨state, memory, hread, ha, hsystem⟩ := hp Private limits sample data seed ell
      hn hw hc ht he hcut hd _ hobs
    have hout := congrArg (Option.map NativeReplyContext.Observation.output) hread
    have hmem := congrArg (Option.map NativeReplyContext.Observation.memory) hread
    simp only [Option.map_some, Option.some.injEq, NativeReplyContext.observe] at hout hmem
    have hv : Valid state.work.system := by simpa only [hsystem] using hx
    have hreceipt : Retained.complete (instanceOf state.work.system hv) state.work.system.rho
        (BatchReceipts.proposal state.work.system)
          (memory.privateState.history.map some) = true := by
      simpa only [retained, Option.any_some, hsystem, hmem] using hcomplete
    obtain ⟨hdecode, hcover, hcost, hdeadline⟩ :=
      BatchReceipts.aligned_completed_result limits width data.startup.turns ell
        state memory ha hv hreceipt
    have hsuccess : NativeOpenSelection.result (decodeFamily state.work.system.rows.length)
        next = some (outputFamily (Packets.assemble state.work)) := by
      rw [NativeOpenSelection.result, show next.config.tapes.state = none from hhalt]
      simpa only [Option.isNone_none, ↓reduceIte, hout] using hdecode
    have hcert : certified limits state.work.system hv (some next) = true := by
      simp only [certified, Option.any_some, hsuccess]
      change (_ && decide _) = true
      apply Bool.and_eq_true_iff.mpr
      exact ⟨decide_eq_true ⟨hcover, hcost⟩, decide_eq_true (hmem ▸ hdeadline)⟩
    simpa only [hsystem] using hcert

/-- On this fixed compiled controller, the issued-horizon retained-completion
probability is exactly completion read from actual terminal receipts. The final
silent epoch and the deletion of no-call records change no retained proposal. -/
theorem terminal_completion (width : ℕ) (limits : Limits n) (sample : Sampler n Private)
    (data : GuardedStartup.Input) (seed : Private) (hx : Valid data.startup.system) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
    let world := (⟨program.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial seed, []⟩⟩ :
        World impl.tapes impl.Controls Unit (ServerState n Private) (GuardedStartup.encoding data))
    (Trace.law limits sample program limits.turns world).map
      (fun state => Retained.complete (instanceOf data.startup.system hx)
        data.startup.system.rho (BatchReceipts.proposal data.startup.system) state.records) true =
    ((NativeUnboundedExecution.terminal program (environment limits sample) world).map
      (retained data.startup.system hx)) true := by
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let world : World impl.tapes impl.Controls Unit (ServerState n Private)
      (GuardedStartup.encoding data) :=
    ⟨program.initialConfig (GuardedStartup.encoding data), ⟨ConcurrentBatch.initial seed, []⟩⟩
  let complete := fun (records : List (Trace.Record n)) =>
    Retained.complete (instanceOf data.startup.system hx)
    data.startup.system.rho (BatchReceipts.proposal data.startup.system) records
  have hi : Invariant limits world.memory := NativeBatch.initial_invariant limits seed
  have hskip (records : List (Trace.Record n)) : complete (none :: records) = complete records := by
    dsimp only [complete]
    rw [← BatchReceipts.completion_eq data.startup.system hx,
      ← BatchReceipts.completion_eq data.startup.system hx]
    rfl
  have hfinal := History.final_records_mean limits sample program world hi
    (fun records => if complete records then 1 else 0)
  simp only [hskip] at hfinal
  change (∑' s, _ * _) = ∑' s, _ * _ at hfinal
  rw [DiscreteComparison.indicator_mean, DiscreteComparison.indicator_mean] at hfinal
  dsimp only
  rw [← hfinal, ← Trace.law_native_terminal limits sample program world hi, PMF.map_comp]
  have heq := PMF.map_congr_on_support (Trace.law limits sample program (limits.turns + 1) world)
    (fun state => complete state.records)
    (fun state => retained data.startup.system hx (state.hidden.map worldOf)) ?_
  · exact congrArg (fun μ : PMF Bool => μ true) heq
  intro state hs
  have hv := Trace.law_valid limits sample program _ world hi state hs
  cases hh : state.hidden with
  | none =>
    have hn : none ∈ (NativeUnboundedExecution.terminal program
        (environment limits sample) world).support := by
      rw [← Trace.law_native_terminal limits sample program world hi]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨state, hs, by simp [hh]⟩
    have ho := (PMF.mem_support_map_iff
      (Option.map (NativeReplyContext.observe impl.context)) _ _).mpr ⟨none, hn, rfl⟩
    rw [impl.law] at ho
    obtain ⟨outcome, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    cases he
  | some phase =>
    cases phase with
    | pending chosen => simp only [Trace.Valid, hh] at hv
    | ready next =>
      have hhisto := hv
      simp only [Trace.Valid, hh] at hhisto
      have hm := hhisto.2
      change next.memory.privateState.history = state.records.filterMap id ++ [] at hm
      simp only [List.append_nil] at hm
      simp only [retained, Option.map_some, Option.any_some, worldOf, hm]
      change complete state.records = complete ((state.records.filterMap id).map some)
      dsimp only [complete]
      rw [← BatchReceipts.completion_eq data.startup.system hx,
        ← BatchReceipts.completion_eq data.startup.system hx]
      simp [BatchReceipts.words]

/-- Source Theorem 5(1) numerical assembly for the fixed compiled block scheduler:
binomial certified-tape success by the oracle deadline and all three stopped-bill
bounds hold for one named native program and one correlated source oracle.
Only reached issued productivity/invoice envelopes are premises; integrability,
output correctness, stopping and representation are conclusions or derived laws. -/
theorem upper_controller (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : data.startup.turns = limits.turns) (_ : data.startup.turns ≤ data.allotments)
        (hx : Valid data.startup.system),
      let world : World impl.tapes impl.Controls Unit (ServerState n Private)
          (GuardedStartup.encoding data) :=
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
          (NativeUnboundedExecution.terminal program (environment limits sample) world).map
            (certified limits data.startup.system hx) true ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * ENNReal.ofReal
            (∑ t ∈ Finset.range limits.turns, binomialFailure p r t) ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * ENNReal.ofReal (r / p) ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≤
          (c : ℝ≥0∞) * limits.turns ∧
        Quantitative.expected limits sample program charge (limits.turns + 1) world ≠ ∞ := by
  dsimp only
  intro Private limits sample data seed ell hn hw hc he hcut hd hbudget hallot hx
    a r hr p hp c Hprod Hcost
  have hnum := BatchUpper.upper_controller (n := n) width Private limits sample data seed ell
    hn hw hc he hcut hd hbudget hallot hx a r hr p hp c Hprod Hcost
  refine ⟨?_, hnum.2⟩
  apply hnum.1.trans
  rw [terminal_completion width limits sample data seed hx]
  exact output_controller width Private limits sample data seed ell hn hw hc hbudget.le
    he hcut hd hx

end Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
