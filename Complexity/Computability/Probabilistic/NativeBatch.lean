/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeEpoch
public import Complexity.Probability.StochasticOracle.ConcurrentBatch.Protocol
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# General guarded concurrent batches in actual open native execution

[Wang2027], model PDF pp. 4--6. The actual handler decodes whole preformed batch
packets, checks opportunity reuse/turn/deadline guards before sampling, and draws
all call trajectories jointly. Invalid native transactions are deterministic
local rejections, not issued source batches. Physical batch duration is a maximum
and invoices sum charges accrued through actual return/cancellation.

Theorems quantify over arbitrary native machines and private oracle state, without
assuming source validity or a machine-to-policy representation identity. Source
batch epochs hold only accepted queries; malformed/reused/exhausted transactions
are executed silently. These are distributional typed-PTM interface results,
not a compiler/resource theorem for external PTM encodings or real-valued clocks.

## Main results

* `execute_invariant`: actual native execution preserves source feasibility and joint meters.
* `terminal_invariant`: every actual terminal world has the same source guarantees.
* `source_restart`: actual selected-before-response source-batch stopping/resume law.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open scoped NNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)

/-- Actual valid candidate families parsed from native response packets. -/
@[expose] def nativeAvailable (m : ℕ) : List (Event Unit) → Finset (Fin m)
  | [] => ∅
  | event :: h => (parseProposals n m event.reply.word).foldr (· ∪ ·) ∅ ∪ nativeAvailable m h

/-- The same candidate provenance read from accepted source batch receipts. -/
@[expose] def sourceAvailable (m : ℕ) : List (Exchange n) → Finset (Fin m)
  | [] => ∅
  | x :: h => (proposals m x.report).foldr (· ∪ ·) ∅ ∪ sourceAvailable m h

/-- Source and native histories have the same resource meters. Rejected raw
transactions are retained natively with zero charge and no accepted source turn. -/
@[expose] def Invariant (memory : Memory Unit (ServerState n Private)) : Prop :=
  WellFormed limits memory.privateState ∧
    tokenBill memory.events = (memory.privateState.history.map Exchange.tokens).sum ∧
      elapsed memory.events = memory.privateState.elapsed ∧
        ∀ m, nativeAvailable (n := n) m memory.events =
          sourceAvailable m memory.privateState.history

/-- An actual initial oracle memory is feasible and has empty source/native histories. -/
theorem initial_invariant (state : Private) :
    Invariant limits (⟨initial state, []⟩ : Memory Unit (ServerState n Private)) := by
  exact ⟨initial_wellFormed limits state, by simp [initial, tokenBill],
    by simp [initial, elapsed], by intro m; simp [nativeAvailable, sourceAvailable, initial]⟩

private theorem serve_invariant (memory : Memory Unit (ServerState n Private))
    (h : Invariant limits memory) (word : Word) (reply : Reply) (next : ServerState n Private)
    (hr : (reply, next) ∈ (serve limits sample word memory.privateState).support) :
    Invariant limits (memory.record ((), word) reply next) := by
  obtain ⟨hw, ht, hd, hp⟩ := h
  cases ha : admit limits memory.privateState word with
  | none =>
    rw [serve_rejected _ _ _ _ ha, PMF.mem_support_pure_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hw, by simpa [Memory.record, tokenBill, rejection] using ht,
      by simpa [Memory.record, elapsed, rejection] using hd, by
        intro m
        simpa [Memory.record, nativeAvailable, parseProposals, rejection, decodeReport] using hp m⟩
  | some b =>
    rw [serve_accepted _ _ _ _ _ ha, PMF.mem_support_map_iff] at hr
    obtain ⟨⟨paths, state⟩, _, he⟩ := hr
    cases he
    refine ⟨commit_wellFormed limits memory.privateState hw word b ha paths state, ?_, ?_, ?_⟩
    · simp only [Memory.record, tokenBill, List.map_cons, List.sum_cons, replyOf, commit]
      change ((observe limits _ b paths).tokens : ℝ≥0) + tokenBill memory.events = _
      rw [ht]
      simp
    · simp only [Memory.record, elapsed, List.map_cons, List.sum_cons, replyOf, commit]
      change _ + elapsed memory.events = _
      rw [hd, add_comm]
    · intro m
      simp only [Memory.record, nativeAvailable, replyOf, parseProposals_report,
        commit, sourceAvailable]
      rw [hp m]

variable (machine : MultiTapePTM k Bool Control Unit)

private theorem step_invariant (world next : World k Control Unit (ServerState n Private) input)
    (h : Invariant limits world.memory)
    (hn : next ∈ (step machine (environment limits sample) world).support) :
    Invariant limits next.memory := by
  cases hs : world.config.tapes.state with
  | none =>
    simp only [step, hs, PMF.mem_support_pure_iff] at hn
    subst next
    exact h
  | some control =>
    simp only [step, hs, PMF.mem_support_bind_iff] at hn
    obtain ⟨bit, _, hn⟩ := hn
    cases ht : machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
        world.config.answerSymbols bit with
    | step action symbol move =>
      simp only [ht, PMF.mem_support_pure_iff] at hn
      subst next
      exact h
    | query op state =>
      simp only [ht, PMF.mem_support_map_iff] at hn
      obtain ⟨⟨reply, privateState⟩, hr, he⟩ := hn
      subst next
      cases op
      exact serve_invariant limits sample world.memory h _ reply privateState hr

/-- All accepted source batches of arbitrary actual native executions are
nonempty/preformed, single-use and deadline/turn feasible, with exact joint meters. -/
theorem execute_invariant (fuel : ℕ)
    (world next : World k Control Unit (ServerState n Private) input)
    (h : Invariant limits world.memory)
    (hn : next ∈ (execute machine (environment limits sample) fuel world).support) :
    Invariant limits next.memory := by
  rw [execute_eq_stateLaw] at hn
  induction fuel generalizing next with
  | zero =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hn
    subst next
    exact h
  | succ fuel ih =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hn
    obtain ⟨mid, hm, hn⟩ := hn
    exact step_invariant limits sample machine mid next (ih mid hm) hn

/-- Missing terminal mass remains divergence; every supported terminal world
retains source feasibility and the exact actually accrued batch bill/duration. -/
theorem terminal_invariant (world next : World k Control Unit (ServerState n Private) input)
    (h : Invariant limits world.memory)
    (hn : some next ∈ (NativeUnboundedExecution.terminal machine (environment limits sample)
      world).support) : Invariant limits next.memory := by
  obtain ⟨_, fuel, hf⟩ := (NativeUnboundedExecution.terminal_support _ _ _ _).mp hn
  exact execute_invariant limits sample machine fuel world next h hf

/-- The concrete source candidate codec, independent of a native semantic parser. -/
@[expose] def candidateParser (m : ℕ) (_ : Unit) (_request response : Word) : Finset (Fin m) :=
  (parseProposals n m response).foldr (· ∪ ·) ∅

/-- Native proposal accounting agrees with the actual batch response codec. -/
theorem candidateParser_proposals (m : ℕ) (events : List (Event Unit)) :
    NativeOpenSelection.proposals (candidateParser (n := n) m) events =
      nativeAvailable (n := n) m events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    simp only [NativeOpenSelection.proposals, List.foldr_cons, candidateParser,
      nativeAvailable] at *
    rw [ih]

/-- Accepted outputs of actual admitted selection-only machines come from
completed valid candidate packets in accepted source batches. Failure-only
outputs have no provenance requirement. No representation identity is assumed. -/
theorem terminal_provenance (m : ℕ) (accept : Finset (Fin m) → Bool)
    (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (hs : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (hn : some next ∈ (NativeUnboundedExecution.terminal machine (environment limits sample)
      world).support) (C : Finset (Fin m))
    (hc : NativeOpenSelection.result (decodeFamily m) next = some C) (ha : accept C = true) :
    C ⊆ sourceAvailable m next.memory.privateState.history := by
  have hp := NativeUnboundedExecution.terminal_provenance machine (environment limits sample)
    (candidateParser (n := n) m) (decodeFamily m) accept world next hs hn C hc ha
  rw [candidateParser_proposals,
    (terminal_invariant limits sample machine world next hi hn).2.2.2 m] at hp
  exact hp

/-- A source boundary is a native halt or a concretely accepted preformed batch.
Rejected transactions are silent and cannot count as source turns. -/
@[expose] def sourceBoundary : Phase k Control Unit (ServerState n Private) input → Prop
  | .ready world => NativeUnboundedExecution.halted world
  | .pending (.query world _ _) =>
      (admit limits world.memory.privateState (world.config.channels ()).queryBuffer).isSome
  | .pending _ => False

open Classical in
instance : DecidablePred (sourceBoundary (k := k) (Control := Control) (Private := Private)
    (input := input) limits) := fun _ => inferInstance

/-- Actual native execution through silent local code and rejected transactions,
holding at its next accepted source batch before sampling that batch's response. -/
@[expose] def sourceSilent : Phase k Control Unit (ServerState n Private) input →
    PMF (Phase k Control Unit (ServerState n Private) input) :=
  StoppedProcess.beforeBoundary (phaseStep machine (environment limits sample))
    (sourceBoundary limits)

/-- Silent execution, including rejected transactions, is independent of the
joint oracle sampler. Accepted source batches are held before sampling. -/
theorem sourceSilent_independent (other : Sampler n Private) :
    sourceSilent (input := input) limits sample machine = sourceSilent limits other machine := by
  funext phase
  cases phase with
  | ready world => rfl
  | pending chosen =>
    cases chosen with
    | halted world => rfl
    | «local» next => rfl
    | query world op next =>
      cases op
      cases ha : admit limits world.memory.privateState (world.config.channels ()).queryBuffer <;>
        simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep,
          dispatch, environment, serve, ha]

private theorem prepared_memory
    (world : World k Control Unit (ServerState n Private) input) (bit : Bool) :
    (worldOf (.pending (instruction machine world bit))).memory = world.memory := by
  unfold instruction
  split
  · rfl
  · split <;> rfl

/-- Actual selected/dispatch interface ticks preserve source feasibility and joint meters. -/
theorem phase_invariant
    (phase next : Phase k Control Unit (ServerState n Private) input)
    (hi : Invariant limits (worldOf phase).memory)
    (hn : next ∈ (phaseStep machine (environment limits sample) phase).support) :
    Invariant limits (worldOf next).memory := by
  cases phase with
  | ready world =>
    simp only [phaseStep] at hn
    split at hn
    · rw [PMF.mem_support_pure_iff] at hn
      subst next
      exact hi
    · rw [prepare, PMF.map_comp, PMF.mem_support_map_iff] at hn
      obtain ⟨bit, _, rfl⟩ := hn
      change Invariant limits (worldOf (.pending (instruction machine world bit))).memory
      rw [prepared_memory]
      exact hi
  | pending chosen =>
    simp only [phaseStep, PMF.mem_support_map_iff] at hn
    obtain ⟨nextWorld, hn, rfl⟩ := hn
    cases chosen with
    | halted world =>
      rw [dispatch, PMF.mem_support_pure_iff] at hn
      subst nextWorld
      exact hi
    | «local» world =>
      rw [dispatch, PMF.mem_support_pure_iff] at hn
      subst nextWorld
      exact hi
    | query world op state =>
      cases op
      rw [dispatch, PMF.mem_support_map_iff] at hn
      obtain ⟨⟨reply, privateState⟩, hr, rfl⟩ := hn
      exact serve_invariant limits sample world.memory hi _ reply privateState hr

private theorem silent_invariant
    (phase next : Phase k Control Unit (ServerState n Private) input)
    (hi : Invariant limits (worldOf phase).memory)
    (hn : next ∈ (sourceSilent limits sample machine phase).support) :
    Invariant limits (worldOf next).memory := by
  simp only [sourceSilent, StoppedProcess.beforeBoundary] at hn
  split at hn
  · rw [PMF.mem_support_pure_iff] at hn
    subst next
    exact hi
  · exact phase_invariant limits sample machine phase next hi hn

/-- Actual next source-batch/halting epoch, retaining silent divergence. -/
@[expose] def seekSource (world : World k Control Unit (ServerState n Private) input) :
    PMF (Option (Phase k Control Unit (ServerState n Private) input)) :=
  StoppedProcess.terminal (sourceSilent limits sample machine) (sourceBoundary limits)
    (StoppedProcess.beforeBoundary_absorbs _ _) (.ready world)

/-- Every actually reached source boundary is source feasible and retains
exact native/source joint resources and provenance, even before its response. -/
theorem seekSource_invariant
    (world : World k Control Unit (ServerState n Private) input)
    (phase : Phase k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (hn : some phase ∈ (seekSource limits sample machine world).support) :
    Invariant limits (worldOf phase).memory := by
  obtain ⟨_, fuel, hf⟩ := (StoppedProcess.terminal_support _ _ _ _ _).mp hn
  have hpres (fuel : ℕ) (next : Phase k Control Unit (ServerState n Private) input)
      (h : next ∈ (ObservedProcess.stateLaw (sourceSilent limits sample machine)
        fuel (.ready world)).support) : Invariant limits (worldOf next).memory := by
    induction fuel generalizing next with
    | zero =>
      rw [ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at h
      subst next
      exact hi
    | succ fuel ih =>
      rw [ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at h
      obtain ⟨mid, hm, hn⟩ := h
      exact silent_invariant limits sample machine mid next (ih mid hm) hn
  exact hpres fuel phase hf

/-- Every reached source query is actually accepted by the concrete byte/guard
checks. The epoch cannot expose a rejected native transaction as a source batch. -/
theorem source_query_valid (world queryWorld : World k Control Unit (ServerState n Private) input)
    (next : Control) (h : some (.pending (.query queryWorld () next)) ∈
      (seekSource limits sample machine world).support) :
    ∃ b, admit limits queryWorld.memory.privateState (queryWorld.config.channels ()).queryBuffer =
      some b := by
  have hb := ((StoppedProcess.terminal_support _ _ _ _ _).mp h).1
  change (admit limits queryWorld.memory.privateState
    (queryWorld.config.channels ()).queryBuffer).isSome = true at hb
  cases ha : admit limits queryWorld.memory.privateState
      (queryWorld.config.channels ()).queryBuffer with
  | none => simp [ha] at hb
  | some b => exact ⟨b, rfl⟩

private theorem halt_source (phase : Phase k Control Unit (ServerState n Private) input)
    (h : phaseHalted phase) : sourceBoundary limits phase := by
  cases phase with
  | ready world => exact h
  | pending chosen => exact h.elim

/-- Full actual native terminal law factors at the next accepted source batch,
including deterministic rejected transactions and divergent silent computation. -/
theorem source_restart (world : World k Control Unit (ServerState n Private) input) :
    NativeInterface.terminal machine (environment limits sample) world =
      (seekSource limits sample machine world).bind (fun hit => hit.elim (PMF.pure none)
        (StoppedProcess.terminal (phaseStep machine (environment limits sample)) phaseHalted
          (phase_absorbs machine (environment limits sample)))) :=
  StoppedProcess.terminal_restart _ _ _ _ (halt_source limits) (.ready world)

/-- Seek a genuine source boundary from an arbitrary retained interface phase. -/
@[expose] def seekSourceFrom : Option (Phase k Control Unit (ServerState n Private) input) →
    PMF (Option (Phase k Control Unit (ServerState n Private) input))
  | none => PMF.pure none
  | some phase => StoppedProcess.terminal (sourceSilent limits sample machine)
      (sourceBoundary limits) (StoppedProcess.beforeBoundary_absorbs _ _) phase

/-- Respond only after a source boundary has been selected. The complete hidden
native configuration and oracle state are retained. Divergence stays divergent. -/
@[expose] def respondSource : Option (Phase k Control Unit (ServerState n Private) input) →
    PMF (Option (Phase k Control Unit (ServerState n Private) input))
  | none => PMF.pure none
  | some phase => (phaseStep machine (environment limits sample) phase).map some

/-- Public selected-before-response signal: accepted source history plus the
whole preformed batch, or a halt flag. Rejected raw transactions are not signals. -/
@[expose] def sourceSignal : Option (Phase k Control Unit (ServerState n Private) input) →
    Option (List (Exchange n) × Option (Batch n))
  | none => none
  | some (.ready world) => some (world.memory.privateState.history, none)
  | some (.pending (.query world _ _)) =>
      (admit limits world.memory.privateState (world.config.channels ()).queryBuffer).map
        (fun b => (world.memory.privateState.history, some b))
  | some (.pending _) => none

/-- Actual retained hidden source-epoch transition. Silent rejection/computation
is followed by one accepted batch response, unless halt or divergence intervenes. -/
@[expose] def sourceStep (state : Option (Phase k Control Unit (ServerState n Private) input)) :
    PMF (Option (Phase k Control Unit (ServerState n Private) input)) :=
  (seekSourceFrom limits sample machine state).bind (respondSource limits sample machine)

/-- Derived source response kernel conditioned jointly on selection and the
actual history. Null signals use posterior completion without changing the law. -/
@[expose] def sourceResponse
    (prior : PMF (Option (Phase k Control Unit (ServerState n Private) input)))
    (selected : Option (List (Exchange n) × Option (Batch n))) :
    PMF (Option (Phase k Control Unit (ServerState n Private) input)) :=
  (PMF.posterior (prior.bind (seekSourceFrom limits sample machine))
    (sourceSignal limits) selected).bind (respondSource limits sample machine)

/-- Concrete stopping-epoch law factors after the entire batch has been
selected, before any call response. Private history and correlations survive. -/
theorem source_factor
    (prior : PMF (Option (Phase k Control Unit (ServerState n Private) input))) :
    ((prior.bind (seekSourceFrom limits sample machine)).map (sourceSignal limits)).bind
      (sourceResponse limits sample machine prior) =
        prior.bind (sourceStep limits sample machine) := by
  have he := PMF.posterior_bind (prior.bind (seekSourceFrom limits sample machine))
    (sourceSignal limits) (fun hit _ => respondSource limits sample machine hit)
  unfold sourceResponse
  rw [he, PMF.bind_bind]
  rfl

/-- Complete joint source selection/response law, preserving all hidden fields. -/
@[expose] def sourceJoint
    (prior : PMF (Option (Phase k Control Unit (ServerState n Private) input))) :
    PMF (Option (List (Exchange n) × Option (Batch n)) ×
      Option (Phase k Control Unit (ServerState n Private) input)) := do
  let hit ← prior.bind (seekSourceFrom limits sample machine)
  let next ← respondSource limits sample machine hit
  pure (sourceSignal limits hit, next)

/-- The selected-before-response conditional kernel preserves the full joint law,
including oracle resources and hidden memory, rather than just response marginals. -/
theorem source_disintegration
    (prior : PMF (Option (Phase k Control Unit (ServerState n Private) input))) :
    ((prior.bind (seekSourceFrom limits sample machine)).map (sourceSignal limits)).bind
      (fun selected => (sourceResponse limits sample machine prior selected).map
        (fun next => (selected, next))) = sourceJoint limits sample machine prior := by
  have he := PMF.posterior_bind (prior.bind (seekSourceFrom limits sample machine))
    (sourceSignal limits) (fun hit selected =>
      (respondSource limits sample machine hit).map (fun next => (selected, next)))
  simpa only [sourceResponse, sourceJoint, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.map, PMF.bind_bind, Function.comp_def] using he

/-- Resume actual instruction-level execution from the retained source epoch. -/
@[expose] def finishSource : Option (Phase k Control Unit (ServerState n Private) input) →
    PMF (Option (Phase k Control Unit (ServerState n Private) input))
  | none => PMF.pure none
  | some phase => StoppedProcess.terminal (phaseStep machine (environment limits sample))
      phaseHalted (phase_absorbs machine (environment limits sample)) phase

/-- One actual source epoch followed by resumption preserves the entire terminal
law, even if silent computation diverges or the next boundary is a halt. -/
theorem source_resume (state : Option (Phase k Control Unit (ServerState n Private) input)) :
    finishSource limits sample machine state =
      (sourceStep limits sample machine state).bind (finishSource limits sample machine) := by
  cases state with
  | none => simp [finishSource, sourceStep, seekSourceFrom, respondSource]
  | some phase =>
    change StoppedProcess.terminal (phaseStep machine (environment limits sample))
      phaseHalted (phase_absorbs machine (environment limits sample)) phase = _
    rw [StoppedProcess.terminal_restart _ _ _ _ (halt_source limits) phase]
    simp only [sourceStep, seekSourceFrom, PMF.bind_bind]
    congr 1
    funext hit
    cases hit with
    | none => simp [respondSource, finishSource]
    | some selected =>
      simp only [Option.elim_some, respondSource, PMF.bind_map, Function.comp_def]
      exact StoppedProcess.terminal_step _ _ _ selected

/-- Every finite prefix of actual accepted source epochs can be resumed without
changing success, divergence, the complete path receipts or either resource meter.
This does not equate arbitrary solutions of an infinite epoch fixed-point equation. -/
theorem resume_source_prefix (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    (ObservedProcess.stateLaw (sourceStep limits sample machine) turns
      (some (.ready world))).bind (finishSource limits sample machine) =
        NativeInterface.terminal machine (environment limits sample) world := by
  have hf := source_resume (input := input) limits sample machine
  induction turns with
  | zero => simp [ObservedProcess.stateLaw, finishSource, NativeInterface.terminal]
  | succ turns ih =>
    simp only [ObservedProcess.stateLaw, PMF.bind_bind, ← hf]
    exact ih

/-- Full-history posterior of the actual retained source-epoch process. -/
@[expose] def sourceHistoryPrior {H : Type}
    (observe : Option (Phase k Control Unit (ServerState n Private) input) → H)
    (turns : ℕ) (world : World k Control Unit (ServerState n Private) input) (history : List H) :
    PMF (Option (Phase k Control Unit (ServerState n Private) input)) :=
  (PMF.posterior (ObservedProcess.privateLaw (sourceStep limits sample machine)
    observe turns (some (.ready world))) ObservedProcess.Path.observations history).map
      ObservedProcess.Path.hidden

/-- The existing behavioral full-history API instantiated by accepted concurrent
source-batch epochs. This derives conditioning; no epoch-kernel identity is a premise. -/
theorem source_history_kernel {H : Type}
    (observe : Option (Phase k Control Unit (ServerState n Private) input) → H)
    (turns : ℕ) (world : World k Control Unit (ServerState n Private) input) (history : List H) :
    ObservedProcess.nextHistory (sourceStep limits sample machine) observe turns
      (some (.ready world)) history =
      (((sourceHistoryPrior limits sample machine observe turns world history).bind
        (seekSourceFrom limits sample machine)).map (sourceSignal limits)).bind (fun selected =>
          (sourceResponse limits sample machine
            (sourceHistoryPrior limits sample machine observe turns world history) selected).map
              (fun next => observe next :: history)) := by
  rw [← PMF.map_bind, source_factor]
  simp only [sourceHistoryPrior, PMF.bind_map, PMF.map_bind, ObservedProcess.nextHistory,
    Function.comp_def]

end Cslib.Probability.NativeBatch
