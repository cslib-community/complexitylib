/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchReceipts
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Compiled native output and oracle-deadline certification

[Wang2027], Theorem 5(1), PDF p. 12, Appendix A.5 p. 16. The model on PDF
p. 5 explicitly excludes local computation time from deadline D. Here elapsed
means the actual oracle ledger: sums of concurrent batch maxima, with cutoffs
and cancellation. No wall-clock bound on local instructions is claimed; arbitrary
finite response words need response-dependent local processing time.

`exists_native_output_controller` connects actual compiled tape readback to
retained completion and the dual certificate, then compares the corresponding
events on the original native terminal law. No tape-output, halting, execution-law
or deadline conclusion is supplied as a hypothesis. The remaining numerical
assembly must identify this final receipt event with the epoch completion bound
for the same witness before asserting the source success lower bound or optimum.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
open Turing NativeOpenExecution ConcurrentBatch NativeBatch
open scoped NNReal ENNReal
variable {n k : ℕ} {R Private : Type} {input : List Bool}

/-- Completion read from actual native terminal source receipts. Divergence is
not success; this event does not redefine the accrued bill on divergent paths. -/
@[expose] def retained (x : Input) (hx : Valid x)
    (outcome : Option (World k R Unit (ServerState n Private) input)) : Bool :=
  outcome.any fun world => Retained.complete (instanceOf x hx) x.rho
    (BatchReceipts.proposal x) (world.memory.privateState.history.map some)

open scoped Classical in
/-- Successful native output means a halted, decoded original family with full
coverage, its derived dual bound, and the source's oracle-only deadline. -/
@[expose] def certified (limits : Limits n) (x : Input) (hx : Valid x)
    (outcome : Option (World k R Unit (ServerState n Private) input)) : Bool :=
  outcome.any fun world =>
    (NativeOpenSelection.result (decodeFamily x.rows.length) world).any fun C =>
      decide ((instanceOf x hx).covered (C.image Fin.val) = (instanceOf x hx).ground ∧
        (instanceOf x hx).cost (C.image Fin.val) ≤
          (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e ∧
        world.memory.privateState.elapsed ≤ limits.deadline)

/-- The actual constructed native program transports receipt completion to
certified halted tape output under one fixed sampler and seed. This is a lower
comparison of genuine terminal event probabilities, not an assumed success law. -/
theorem exists_native_output_controller (width : ℕ) :
    ∃ (tapes : ℕ) (Controls : Type) (_ : Finite Controls)
      (program : MultiTapePTM tapes Bool Controls Unit),
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
  obtain ⟨tapes, Controls, hR, program, context, hp⟩ :=
    BatchAdmission.exists_native_admitted_controller (n := n) width
  refine ⟨tapes, Controls, hR, program, ?_⟩
  intro Private limits sample data seed ell hn hw hc ht he hcut hd hx
  dsimp only
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
      change decide (_ ∧ _ ∧ _) = true
      exact decide_eq_true ⟨hcover, hcost, hmem ▸ hdeadline⟩
    simpa only [hsystem] using hcert

end Cslib.Probability.StochasticOracle.NativeRetention.BatchOutput
