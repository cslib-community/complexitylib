/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeInterface
public import CslibFrontier.Probability.PMF.StoppedProcess.Boundary
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual next-query and halting epochs of an open native PTM

[Wang2027], model PDF pp. 4--6, Theorems 5/6 pp. 12--13 and Appendix A.5 p. 16.
Silent native computation is executed until an actual selected query or actual
halting. The environment has not yet supplied the selected query's response.
Silent divergence retains its missing mass. Pausing and resuming is proved to
preserve the entire actual terminal law, not assumed as a representation contract.

Raw queries are not automatically valid source batches. Source opportunity,
concurrency/cancellation/codec contracts and general measurable laws remain
separate obligations. An epoch decision may halt without a query; issued native
queries are counted by newly appended response records.

## Main results

* `seek_independent`: selecting the next query cannot sample its response.
* `seek_restart`: actual stopped-law decomposition through the next query/halting epoch.
* `native_epoch_equation`: dispatching exactly that query and resuming preserves native execution.
* `nextEpoch_resources`: actual epoch records preserve issued-call counts and joint resources.
* `resume_after_epochs`: finite actual epoch prefixes preserve the resumed terminal law.
* `history_kernel`: full-history behavioral kernels factor at actual selected query epochs.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeEpoch
open NativeOpenExecution NativeOpenSelection NativeInterface Turing
open scoped ENNReal
variable {Operation Private Control J : Type} {k : ℕ} {input : List Bool}
variable [DecidableEq Operation]
variable (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)

/-- A committed halt or an actual query selected before its response. Local
instructions, including prospective halted configurations, are not boundaries. -/
@[expose] def boundary : Phase k Control Operation Private input → Prop
  | .ready world => NativeUnboundedExecution.halted world
  | .pending (.query _ _ _) => True
  | .pending _ => False

instance : DecidablePred (boundary (k := k) (Control := Control) (Operation := Operation)
    (Private := Private) (input := input)) := fun phase =>
  match phase with
  | .ready world => inferInstanceAs (Decidable (NativeUnboundedExecution.halted world))
  | .pending (.query _ _ _) => inferInstanceAs (Decidable True)
  | .pending (.halted _) => inferInstanceAs (Decidable False)
  | .pending (.local _) => inferInstanceAs (Decidable False)

/-- Actual silent execution, holding at the first query or halt instead of
crossing it. No selected query can be dispatched by this kernel. -/
@[expose] def silentStep : Phase k Control Operation Private input →
    PMF (Phase k Control Operation Private input) :=
  StoppedProcess.beforeBoundary (phaseStep machine env) boundary

omit [DecidableEq Operation] in
/-- Every stopped native state is an epoch boundary. -/
theorem halt_boundary (phase : Phase k Control Operation Private input)
    (h : phaseHalted phase) : boundary phase := by
  cases phase with
  | ready world => exact h
  | pending chosen => exact h.elim

/-- The actual silent kernel is independent of the response handler, including
on paths with unbounded local computation. -/
theorem silentStep_independent (other : Environment Operation Private) :
    silentStep (input := input) machine env = silentStep machine other := by
  funext phase
  cases phase with
  | ready world => rfl
  | pending chosen => cases chosen <;> rfl

/-- The held native boundary is absorbing in silent execution. -/
theorem silent_absorbs (phase : Phase k Control Operation Private input)
    (h : boundary phase) : silentStep machine env phase = PMF.pure phase :=
  StoppedProcess.beforeBoundary_absorbs _ _ _ h

/-- Actual next-query/halting law. `none` means silent divergence before reaching
a boundary; `some` retains the complete hidden checkpoint before any response. -/
@[expose] def seek (world : World k Control Operation Private input) :
    PMF (Option (Phase k Control Operation Private input)) :=
  StoppedProcess.terminal (silentStep machine env) boundary
    (silent_absorbs machine env) (.ready world)

/-- The selected epoch law never samples the current or any future response. -/
theorem seek_independent (other : Environment Operation Private)
    (world : World k Control Operation Private input) :
    seek machine env world = seek machine other world := by
  unfold seek
  congr 1
  exact silentStep_independent machine env other

/-- Every supported checkpoint is an actual first-query/halting boundary of a
finite stopped silent execution, not an arbitrarily supplied policy action. -/
theorem seek_support (world : World k Control Operation Private input)
    (phase : Phase k Control Operation Private input) :
    some phase ∈ (seek machine env world).support ↔ boundary phase ∧
      ∃ fuel, phase ∈
        (ObservedProcess.stateLaw (silentStep machine env) fuel (.ready world)).support :=
  StoppedProcess.terminal_support _ _ _ _ _

/-- An already halted native world is a zero-query stopping epoch. -/
theorem seek_halted (world : World k Control Operation Private input)
    (h : NativeUnboundedExecution.halted world) :
    seek machine env world = PMF.pure (some (.ready world)) :=
  StoppedProcess.terminal_halted _ _ _ _ h

/-- A concrete next instruction known from the actual transition table to be a
query reaches its pre-response checkpoint without dispatching that query. -/
theorem seek_query (world : World k Control Operation Private input)
    (op : Operation) (next : Control)
    (hn : ¬ NativeUnboundedExecution.halted world)
    (h : ∀ bit, instruction machine world bit = .query world op next) :
    seek machine env world = PMF.pure (some (.pending (.query world op next))) := by
  have hk : silentStep machine env (.ready world) = PMF.pure (.pending (.query world op next)) := by
    cases hs : world.config.tapes.state with
    | none => exact False.elim (hn hs)
    | some control =>
      simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
        NativeUnboundedExecution.halted, hs, reduceCtorEq, ite_false, phaseStep, Option.isNone_some,
        Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def, h]
      exact PMF.map_const _ _
  unfold seek
  rw [StoppedProcess.terminal_step (silentStep machine env) boundary
    (silent_absorbs machine env), hk, PMF.pure_bind]
  exact StoppedProcess.terminal_halted _ _ _ _ trivial

/-- Oracle private state and receipts at a checkpoint; local work tapes remain
inside the checkpoint and may change during silent computation. -/
@[expose] def checkpointMemory (phase : Phase k Control Operation Private input) :
    Memory Operation Private := (worldOf phase).memory

omit [DecidableEq Operation] in
private theorem instruction_memory (world : World k Control Operation Private input) (bit : Bool) :
    checkpointMemory (.pending (instruction machine world bit)) = world.memory := by
  cases hs : world.config.tapes.state with
  | none => simp [instruction, hs, checkpointMemory, worldOf]
  | some control =>
    simp only [instruction, hs]
    cases machine.tr control world.config.tapes.inputSymbol world.config.tapes.workTapeSymbols
      world.config.answerSymbols bit <;> rfl

/-- Silent execution cannot obtain a response, change oracle private state or
add a resource receipt, even while its actual native work tapes change. -/
theorem silent_memory (phase : Phase k Control Operation Private input) :
    (silentStep machine env phase).map checkpointMemory = PMF.pure (checkpointMemory phase) := by
  cases phase with
  | ready world =>
    cases hs : world.config.tapes.state with
    | none => simp [silentStep, StoppedProcess.beforeBoundary, boundary,
        NativeUnboundedExecution.halted, hs]
    | some control =>
      simp only [silentStep, StoppedProcess.beforeBoundary, boundary,
        NativeUnboundedExecution.halted, hs, reduceCtorEq, ite_false, phaseStep, Option.isNone_some,
        Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def]
      change (PMF.uniformOfFintype Bool).map (fun bit =>
        checkpointMemory (.pending (instruction machine world bit))) = PMF.pure world.memory
      simp only [instruction_memory]
      exact PMF.map_const _ _
  | pending chosen =>
    cases chosen <;>
      simp [silentStep, StoppedProcess.beforeBoundary, boundary, phaseStep, dispatch,
        checkpointMemory, worldOf]

private theorem silent_clock_memory (fuel : ℕ) (phase : Phase k Control Operation Private input) :
    (ObservedProcess.stateLaw (silentStep machine env) fuel phase).map checkpointMemory =
      PMF.pure (checkpointMemory phase) := by
  induction fuel with
  | zero => simp [ObservedProcess.stateLaw]
  | succ fuel ih =>
    simp only [ObservedProcess.stateLaw, PMF.map_bind, silent_memory]
    exact ih

/-- Every actual reached next-query/halting checkpoint retains exactly the
previous oracle state and bill/duration history. -/
theorem seek_memory (world : World k Control Operation Private input)
    (phase : Phase k Control Operation Private input)
    (h : some phase ∈ (seek machine env world).support) :
    checkpointMemory phase = world.memory := by
  obtain ⟨_, fuel, hf⟩ := (seek_support machine env world phase).mp h
  have hm := (PMF.mem_support_map_iff checkpointMemory _ _).mpr ⟨phase, hf, rfl⟩
  rw [silent_clock_memory, PMF.mem_support_pure_iff] at hm
  exact hm

/-- Actual terminal-law disintegration through the first query or halt.
Divergent silent computation is propagated rather than conditioned away. -/
theorem seek_restart (world : World k Control Operation Private input) :
    NativeInterface.terminal machine env world = (seek machine env world).bind (fun hit =>
      hit.elim (PMF.pure none)
        (StoppedProcess.terminal (phaseStep machine env) phaseHalted
          (phase_absorbs machine env))) :=
  StoppedProcess.terminal_restart (phaseStep machine env) phaseHalted boundary
    (phase_absorbs machine env) halt_boundary (.ready world)

/-- Dispatch exactly one selected query, or retain a halted boundary. Unsupported
local checkpoints have a harmless completion; `seek_support` excludes them. -/
@[expose] def respond : Option (Phase k Control Operation Private input) →
    PMF (Option (World k Control Operation Private input))
  | none => PMF.pure none
  | some (.ready world) => PMF.pure (some world)
  | some (.pending chosen) => (dispatch env chosen).map some

/-- Actual next-query epoch: run silent code, expose its selected request, then
sample only that response, or preserve halt/divergence. -/
@[expose] def nextEpoch (world : World k Control Operation Private input) :
    PMF (Option (World k Control Operation Private input)) :=
  (seek machine env world).bind (respond env)

private theorem ready_readback (world : World k Control Operation Private input) :
    (NativeInterface.terminal machine env world).map (Option.map worldOf) =
      NativeUnboundedExecution.terminal machine env world := by
  rw [NativeInterface.terminal_native, PMF.map_comp]
  have he : Option.map worldOf ∘ Option.map Phase.ready =
      (id : Option (World k Control Operation Private input) → _) := by
    funext next
    cases next <;> rfl
  rw [he, PMF.map_id]

private theorem phase_readback (phase : Phase k Control Operation Private input) :
    (StoppedProcess.terminal (phaseStep machine env) phaseHalted (phase_absorbs machine env)
      phase).map (Option.map worldOf) =
      match phase with
      | .ready world => NativeUnboundedExecution.terminal machine env world
      | .pending chosen =>
        (dispatch env chosen).bind (NativeUnboundedExecution.terminal machine env) := by
  cases phase with
  | ready world => exact ready_readback machine env world
  | pending chosen =>
    rw [StoppedProcess.terminal_step, PMF.map_bind]
    simp only [phaseStep, PMF.bind_map]
    change ((dispatch env chosen).bind fun world =>
      (NativeInterface.terminal machine env world).map (Option.map worldOf)) = _
    simp only [ready_readback]

/-- The original actual native stopped law obeys the derived query-epoch
composition equation. No epoch law/representation/termination conclusion is a premise. -/
theorem native_epoch_equation (world : World k Control Operation Private input) :
    NativeUnboundedExecution.terminal machine env world =
      (nextEpoch machine env world).bind (fun next =>
        next.elim (PMF.pure none) (NativeUnboundedExecution.terminal machine env)) := by
  have he := congrArg (PMF.map (Option.map worldOf)) (seek_restart machine env world)
  rw [ready_readback] at he
  simp only [PMF.map_bind] at he
  rw [he, nextEpoch, PMF.bind_bind]
  apply congrArg
  funext hit
  cases hit with
  | none => simp [respond]
  | some phase =>
    simp only [Option.elim_some, phase_readback]
    cases phase <;> simp [respond, PMF.bind_map, Function.comp_def]

/-- Divergence is absorbing in the actual epoch process. A halted world is
retained by `nextEpoch`; only a supported query dispatch adds a call. -/
@[expose] def epochStep : Option (World k Control Operation Private input) →
    PMF (Option (World k Control Operation Private input))
  | none => PMF.pure none
  | some world => nextEpoch machine env world

/-- Every supported epoch either halts without a call or appends exactly one
actual response record. No silent instruction can count as an issued query. -/
theorem nextEpoch_trace (world next : World k Control Operation Private input)
    (h : some next ∈ (nextEpoch machine env world).support) :
    ∃ fresh, fresh.length ≤ 1 ∧ next.memory.events = fresh ++ world.memory.events ∧
      (fresh = [] → NativeUnboundedExecution.halted next) := by
  simp only [nextEpoch, PMF.mem_support_bind_iff] at h
  obtain ⟨hit, hh, hn⟩ := h
  cases hit with
  | none => simp [respond] at hn
  | some phase =>
    have hb := ((seek_support machine env world phase).mp hh).1
    have hm := seek_memory machine env world phase hh
    cases phase with
    | ready stoppedWorld =>
      simp only [respond, PMF.mem_support_pure_iff, Option.some.injEq] at hn
      subst next
      exact ⟨[], by simp, by simpa [checkpointMemory, worldOf] using congrArg Memory.events hm,
        fun _ => hb⟩
    | pending chosen =>
      cases chosen with
      | halted stoppedWorld => exact hb.elim
      | «local» localWorld => exact hb.elim
      | query queryWorld op control =>
        simp only [respond, dispatch, PMF.map_comp, PMF.mem_support_map_iff] at hn
        obtain ⟨⟨reply, privateState⟩, _, he⟩ := hn
        cases he
        refine ⟨[⟨op, (queryWorld.config.channels op).queryBuffer, reply⟩], by simp, ?_, by simp⟩
        change _ :: queryWorld.memory.events = _ :: world.memory.events
        congr 1
        exact congrArg Memory.events hm

/-- The actual next-epoch joint resources use precisely the newly recorded
response charges and external durations, with no integrability or independence premise. -/
theorem nextEpoch_resources (world next : World k Control Operation Private input)
    (h : some next ∈ (nextEpoch machine env world).support) :
    ∃ fresh, fresh.length ≤ 1 ∧ next.memory.events = fresh ++ world.memory.events ∧
      tokenBill next.memory.events = tokenBill fresh + tokenBill world.memory.events ∧
      elapsed next.memory.events = elapsed fresh + elapsed world.memory.events := by
  obtain ⟨fresh, hf, he, _⟩ := nextEpoch_trace machine env world next h
  exact ⟨fresh, hf, he, by rw [he, tokenBill_append], by rw [he, elapsed_append]⟩

/-- At most one actual query record per epoch decision, with original history
retained. A halt decision adds zero; silent divergence has no terminal resource value. -/
theorem epochs_trace (u : ℕ) (world next : World k Control Operation Private input)
    (h : some next ∈ (ObservedProcess.stateLaw (epochStep machine env) u (some world)).support) :
    ∃ fresh, fresh.length ≤ u ∧ next.memory.events = fresh ++ world.memory.events := by
  induction u generalizing next with
  | zero =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_pure_iff, Option.some.injEq] at h
    subst next
    exact ⟨[], by simp, rfl⟩
  | succ u ih =>
    simp only [ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at h
    obtain ⟨state, hs, hn⟩ := h
    cases state with
    | none => simp [epochStep] at hn
    | some state =>
      obtain ⟨a, ha, he⟩ := ih state hs
      obtain ⟨b, hb, hf, _⟩ := nextEpoch_trace machine env state next hn
      refine ⟨b ++ a, ?_, ?_⟩
      · simp only [List.length_append]
        omega
      · rw [hf, he, List.append_assoc]

/-- Resume original native execution after a finite epoch prefix. -/
@[expose] def finish : Option (World k Control Operation Private input) →
    PMF (Option (World k Control Operation Private input))
  | none => PMF.pure none
  | some world => NativeUnboundedExecution.terminal machine env world

/-- Finite true epoch prefixes followed by original native continuation preserve
the entire terminal law. The index counts decisions, including a zero-call halt;
issued turns are counted by the actual newly appended response records. -/
theorem resume_after_epochs (u : ℕ) (world : World k Control Operation Private input) :
    (ObservedProcess.stateLaw (epochStep machine env) u (some world)).bind (finish machine env) =
      NativeUnboundedExecution.terminal machine env world := by
  have hf (state : Option (World k Control Operation Private input)) :
      (epochStep machine env state).bind (finish machine env) = finish machine env state := by
    cases state with
    | none => simp [epochStep, finish]
    | some state =>
      change (nextEpoch machine env state).bind (finish machine env) =
        NativeUnboundedExecution.terminal machine env state
      convert (native_epoch_equation machine env state).symm using 1
      congr 1
      funext next
      cases next <;> rfl
  induction u with
  | zero => simp [ObservedProcess.stateLaw, finish]
  | succ u ih =>
    simp only [ObservedProcess.stateLaw, PMF.bind_bind, hf]
    exact ih

/-- Seek from the actual optional hidden state at an epoch. -/
@[expose] def seekFrom : Option (World k Control Operation Private input) →
    PMF (Option (Phase k Control Operation Private input))
  | none => PMF.pure none
  | some world => seek machine env world

/-- Public epoch action, read only after silent computation has actually
reached the selected query or halt. `none` denotes silent divergence. -/
@[expose] def selectedSignal : Option (Phase k Control Operation Private input) →
    Option (Signal Operation)
  | none => none
  | some (.ready world) => some (.halted world.memory.events)
  | some (.pending chosen) => some (signal chosen)

/-- Derived conditional response law at an actual epoch, not at a native
instruction. Hidden local/oracle memory is conditioned jointly on the selected
raw query and prior receipts. Null signals use prior completion. -/
@[expose] def epochResponse
    (prior : PMF (Option (World k Control Operation Private input)))
    (selected : Option (Signal Operation)) :
    PMF (Option (World k Control Operation Private input)) :=
  (PMF.posterior (prior.bind (seekFrom machine env)) selectedSignal selected).bind (respond env)

/-- Actual selected-before-response joint law at the next epoch. -/
@[expose] def epochJoint (prior : PMF (Option (World k Control Operation Private input))) :
    PMF (Option (Signal Operation) × Option (World k Control Operation Private input)) := do
  let hit ← prior.bind (seekFrom machine env)
  let next ← respond env hit
  pure (selectedSignal hit, next)

/-- Full-history/selected-query disintegration at genuine stopping epochs.
The query law is derived from actual silent execution; no epoch representation
or conditional-response identity is supplied. -/
theorem epoch_disintegration (prior : PMF (Option (World k Control Operation Private input))) :
    ((prior.bind (seekFrom machine env)).map selectedSignal).bind (fun selected =>
      (epochResponse machine env prior selected).map (fun next => (selected, next))) =
        epochJoint machine env prior := by
  have he := PMF.posterior_bind (prior.bind (seekFrom machine env)) selectedSignal
    (fun hit selected => (respond env hit).map (fun next => (selected, next)))
  simpa only [epochResponse, epochJoint, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.map, PMF.bind_bind, Function.comp_def] using he

/-- Forgetting the epoch action recovers the actual hidden epoch transition. -/
theorem epochJoint_transition (prior : PMF (Option (World k Control Operation Private input))) :
    (epochJoint machine env prior).map Prod.snd = prior.bind (epochStep machine env) := by
  simp only [epochJoint, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.bind_pure, PMF.bind_bind]
  congr 1
  funext state
  cases state with
  | none => simp [seekFrom, epochStep, respond]
  | some world => rfl

/-- Derive the actual hidden epoch transition by selecting a public epoch
signal and then sampling its derived conditional response law. -/
theorem epoch_factor (prior : PMF (Option (World k Control Operation Private input))) :
    ((prior.bind (seekFrom machine env)).map selectedSignal).bind
      (epochResponse machine env prior) = prior.bind (epochStep machine env) := by
  have he := PMF.posterior_bind (prior.bind (seekFrom machine env)) selectedSignal
    (fun hit _ => respond env hit)
  unfold epochResponse
  rw [he, PMF.bind_bind]
  congr 1
  funext state
  cases state with
  | none => simp [seekFrom, epochStep, respond]
  | some world => rfl

/-- Actual hidden-state posterior after a complete observed epoch history.
Private coins and tapes are retained rather than independently resampled. -/
@[expose] def historyPrior {H : Type}
    (observe : Option (World k Control Operation Private input) → H)
    (n : ℕ) (world : World k Control Operation Private input) (history : List H) :
    PMF (Option (World k Control Operation Private input)) :=
  (PMF.posterior (ObservedProcess.privateLaw (epochStep machine env) observe n (some world))
    ObservedProcess.Path.observations history).map ObservedProcess.Path.hidden

/-- The existing full-history behavioral-process API is instantiated by true
next-query/halting epochs, factored after selection and before response. Null
histories use completion without changing the actual public path law. -/
theorem history_kernel {H : Type}
    (observe : Option (World k Control Operation Private input) → H)
    (n : ℕ) (world : World k Control Operation Private input) (history : List H) :
    ObservedProcess.nextHistory (epochStep machine env) observe n (some world) history =
      (((historyPrior machine env observe n world history).bind (seekFrom machine env)).map
        selectedSignal).bind (fun selected =>
          (epochResponse machine env
            (historyPrior machine env observe n world history) selected).map
            (fun next => observe next :: history)) := by
  rw [← PMF.map_bind, epoch_factor]
  simp only [historyPrior, PMF.bind_map, PMF.map_bind, ObservedProcess.nextHistory,
    Function.comp_def]

end Cslib.Probability.NativeEpoch
