/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.History
import CslibFrontier.Probability.PMF.Disintegration.Support
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Selected first-batch response law of an actual native machine

The first selected batch is chosen before its responses. Silent native computation,
including rejected raw requests, preserves the original source state. Conditioning
on a positive-probability issued observation therefore leaves exactly the original
sampler at that selected batch. No finite hidden-state approximation, independence
between simultaneous calls, or supplied representation equality is used.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.InitialEpoch
open NativeOpenExecution NativeInterface StochasticOracle ConcurrentBatch Turing Trace Quantitative
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- The actual initial selected-epoch posterior has the original joint response
law at its preformed batch, with exact complete receipts and cutoff resources. -/
theorem conditional_records (limits : Limits n) (sample : Sampler n Private)
    (machine : MultiTapePTM k Bool Control Unit)
    (world : World k Control Unit (ServerState n Private) input) (o : Observation n)
    (ho : o ∈ ((select limits sample machine (PMF.pure (Trace.initial world))).map
      (Quantitative.observe limits)).support) (hi : o.issued = true) :
    ∃ batch : Batch n, o.history = [] ∧
      o.signal = some (world.memory.privateState.history, some batch) ∧
      (conditional limits sample machine (PMF.pure (Trace.initial world)) o).map State.records =
        (sample world.memory.privateState batch).map fun draw =>
          [some (ConcurrentBatch.observe limits
            (limits.deadline - world.memory.privateState.elapsed) batch draw.1)] := by
  let prior := PMF.pure (Trace.initial world)
  let posterior := PMF.posterior (select limits sample machine prior)
    (Quantitative.observe limits) o
  have H (picked : Selected n k Private Control input) (hp : picked ∈ posterior.support) :
      ∃ batch : Batch n, o.history = [] ∧
        o.signal = some (world.memory.privateState.history, some batch) ∧
        (respond limits sample machine picked.before picked.checkpoint).map State.records =
          (sample world.memory.privateState batch).map fun draw =>
            [some (ConcurrentBatch.observe limits
              (limits.deadline - world.memory.privateState.elapsed) batch draw.1)] := by
    obtain ⟨hs, he⟩ := PMF.mem_support_of_posterior _ _ _ ho picked hp
    simp only [select, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.pure_bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hs
    obtain ⟨hit, hh, rfl⟩ := hs
    have hiss := congrArg Observation.issued he
    change batchIssued limits hit = o.issued at hiss
    rw [hi] at hiss
    cases hit with
    | none => simp [batchIssued, sourceSignal] at hiss
    | some phase =>
      cases phase with
      | ready next => simp [batchIssued, sourceSignal] at hiss
      | pending chosen =>
        cases chosen with
        | halted next => simp [batchIssued, sourceSignal] at hiss
        | «local» next => simp [batchIssued, sourceSignal] at hiss
        | query next op control =>
          cases op
          have hstate := Trace.seek_state limits sample machine (.ready world)
            (.pending (.query next () control)) hh
          change next.memory.privateState = world.memory.privateState at hstate
          cases ha : admit limits next.memory.privateState
              (next.config.channels ()).queryBuffer with
          | none => simp [batchIssued, sourceSignal, ha] at hiss
          | some batch =>
            refine ⟨batch, ?_, ?_, ?_⟩
            · exact (congrArg Observation.history he).symm
            · have hsignal := congrArg Observation.signal he
              have ha' := ha
              rw [hstate] at ha'
              simpa only [Quantitative.observe, sourceSignal, hstate, ha', Option.map_some]
                using hsignal.symm
            · simp only [respond, respondSource, phaseStep, dispatch, environment,
                serve_accepted _ _ _ _ _ ha, PMF.map_comp, Function.comp_def,
                receipt, Trace.initial, Memory.record, commit, List.head?_cons]
              rw [hstate]
  obtain ⟨picked, hp⟩ := posterior.support_nonempty
  obtain ⟨batch, hhistory, hsignal, _⟩ := H picked hp
  refine ⟨batch, hhistory, hsignal, ?_⟩
  change (posterior.bind (fun picked => respond limits sample machine picked.before
    picked.checkpoint)).map State.records = _
  rw [PMF.map_bind]
  calc
    _ = posterior.bind (fun _ => (sample world.memory.privateState batch).map fun draw =>
        [some (ConcurrentBatch.observe limits
          (limits.deadline - world.memory.privateState.elapsed) batch draw.1)]) := by
      apply PMF.bind_congr_on_support
      intro next hn
      obtain ⟨other, _, hother, hlaw⟩ := H next hn
      have hb : other = batch := by simpa only [hsignal, Option.some.injEq,
        Prod.mk.injEq, true_and] using hother.symm
      simpa only [hb] using hlaw
    _ = _ := PMF.bind_const _ _

end Cslib.Probability.NativeBatch.InitialEpoch
