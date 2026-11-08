/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeBatch
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Whole native source-epoch traces with retained accrued resources

[Wang2027], model PDF pp. 4--6 and Theorem 5/Appendix A.5 pp. 12,16.
The actual source-epoch execution emits completed concurrent receipts. A later
silent divergence preserves all previously accrued invoices; it is not a halted
failure and does not erase the prefix bill. Hidden native/oracle metadata and the
response alphabet are unrestricted discrete types. One fixed sampler is shared
by all machines; no finite sufficient abstraction or representation contract is
supplied. Real clocks remain external interface semantics.

## Main results

* `seek_state`: silent computation/rejection preserves the accepted source state.
* `law_hidden`: complete epoch traces project to actual native source execution.
* `law_resume`: finite trace prefixes resume to the original native terminal law.
* `law_native_terminal`: complete whole-policy readback, without a local clock bound.
* `law_ledger_bound`: turn/deadline/nonreuse bounds, including divergent retained prefixes.
* `terminal_resources`: exact original native bill and duration on terminating paths.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.Trace
open NativeOpenExecution NativeInterface StochasticOracle.ConcurrentBatch Turing
open scoped NNReal ENNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}
variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- Accepted oracle state carried by an actual interface phase. -/
@[expose] def server (phase : Phase k Control Unit (ServerState n Private) input) :
    ServerState n Private := (worldOf phase).memory.privateState

private theorem prepare_state
    (world : World k Control Unit (ServerState n Private) input) (bit : Bool) :
    server (.pending (instruction machine world bit)) = world.memory.privateState := by
  unfold instruction
  split
  · rfl
  · split <;> rfl

/-- No accepted batch is dispatched during silent execution, including actual
rejected native transactions. All hidden oracle state and accepted receipts persist. -/
theorem silent_state (phase : Phase k Control Unit (ServerState n Private) input) :
    (sourceSilent limits sample machine phase).map server = PMF.pure (server phase) := by
  cases phase with
  | ready world =>
    by_cases hh : world.config.tapes.state = none
    · simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
        NativeUnboundedExecution.halted, hh, server]
    · have he : sourceSilent limits sample machine (.ready world) =
          (prepare machine world).map Phase.pending := by
        simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
          NativeUnboundedExecution.halted, phaseStep, hh]
      rw [he, prepare]
      simp only [PMF.map_comp, Function.comp_def, prepare_state]
      exact PMF.map_const _ _
  | pending chosen =>
    cases chosen with
    | halted world => simp [sourceSilent, sourceBoundary, StoppedProcess.beforeBoundary,
        phaseStep, dispatch, server, worldOf]
    | «local» world => simp [sourceSilent, sourceBoundary, StoppedProcess.beforeBoundary,
        phaseStep, dispatch, server, worldOf]
    | query world op next =>
      cases op
      cases ha : admit limits world.memory.privateState (world.config.channels ()).queryBuffer with
      | none => simp [sourceSilent, sourceBoundary, StoppedProcess.beforeBoundary,
          phaseStep, dispatch, environment, serve, ha, server, worldOf, Memory.record]
      | some b => simp [sourceSilent, sourceBoundary, StoppedProcess.beforeBoundary, ha]

/-- Every actual stopping checkpoint retains the same accepted source state;
local computation may diverge or append rejected zero-resource native transactions. -/
theorem seek_state (phase hit : Phase k Control Unit (ServerState n Private) input)
    (hh : some hit ∈ (seekSourceFrom limits sample machine (some phase)).support) :
    server hit = server phase := by
  simp only [seekSourceFrom] at hh
  obtain ⟨_, fuel, hf⟩ := (StoppedProcess.terminal_support _ _ _ _ _).mp hh
  have he (fuel : ℕ) :
      (ObservedProcess.stateLaw (sourceSilent limits sample machine) fuel phase).map server =
        PMF.pure (server phase) := by
    induction fuel with
    | zero => simp [ObservedProcess.stateLaw]
    | succ fuel ih =>
      rw [ObservedProcess.stateLaw, PMF.map_bind]
      simp only [silent_state]
      exact ih
  have hm : server hit ∈
      ((ObservedProcess.stateLaw (sourceSilent limits sample machine) fuel phase).map
        server).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨hit, hf, rfl⟩
  rw [he fuel, PMF.mem_support_pure_iff] at hm
  exact hm

/-- One accepted concurrent receipt, or a zero-call halt/divergence decision. -/
abbrev Record (n : ℕ) := Option (Exchange n)

/-- Read the actual newly appended receipt only after dispatching a selected batch. -/
@[expose] def receipt : Option (Phase k Control Unit (ServerState n Private) input) →
    Option (Phase k Control Unit (ServerState n Private) input) → Record n
  | some (.pending (.query _ _ _)), some (.ready next) => next.memory.privateState.history.head?
  | _, _ => none

/-- Retained whole-policy trace; divergence keeps its earlier completed receipts. -/
structure State (n k : ℕ) (Private Control : Type) (input : List Bool) where
  /-- Actual optional native phase; `none` is silent divergence. -/
  hidden : Option (Phase k Control Unit (ServerState n Private) input)
  /-- Source-epoch receipts, newest first. Halt/divergence decisions append `none`. -/
  records : List (Record n)

/-- Fresh actual native/oracle start. The oracle seed is fixed before choosing
among competitors; hidden tapes and randomness subsequently evolve by actual execution. -/
@[expose] def startWorld (privateState : Private) :
    World k Control Unit (ServerState n Private) input :=
  ⟨machine.initialConfig input, ⟨StochasticOracle.ConcurrentBatch.initial privateState, []⟩⟩

/-- The actual initial trace, without an imposed native instruction clock. -/
@[expose] def initial (world : World k Control Unit (ServerState n Private) input) :
    State n k Private Control input := ⟨some (.ready world), []⟩

/-- Commit the actual source response and retain its receipt with all earlier bills. -/
@[expose] def respond (state : State n k Private Control input)
    (hit : Option (Phase k Control Unit (ServerState n Private) input)) :
    PMF (State n k Private Control input) :=
  (respondSource limits sample machine hit).map fun next =>
    ⟨next, receipt hit next :: state.records⟩

/-- Actual whole-policy source transition; no fresh hidden state is sampled by abstraction. -/
@[expose] def step (state : State n k Private Control input) :
    PMF (State n k Private Control input) :=
  (seekSourceFrom limits sample machine state.hidden).bind (respond limits sample machine state)

/-- Complete finite source-epoch trace law of the actual native machine. -/
@[expose] def law (turns : ℕ) (world : World k Control Unit (ServerState n Private) input) :
    PMF (State n k Private Control input) :=
  ObservedProcess.stateLaw (step limits sample machine) turns (initial world)

/-- Forgetting receipts gives the actual retained native epoch transition. -/
theorem step_hidden (state : State n k Private Control input) :
    (step limits sample machine state).map State.hidden =
      sourceStep limits sample machine state.hidden := by
  simp only [step, respond, PMF.map_bind, PMF.map_comp, sourceStep, Function.comp_def]
  congr 1
  funext hit
  exact PMF.map_id _

/-- Whole-policy trace laws preserve the entire actual hidden native epoch law,
including correlations and missing termination mass, for every native competitor. -/
theorem law_hidden (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    (law limits sample machine turns world).map State.hidden =
      ObservedProcess.stateLaw (sourceStep limits sample machine) turns (some (.ready world)) := by
  induction turns with
  | zero => simp [law, ObservedProcess.stateLaw, initial]
  | succ turns ih =>
    simp only [law, ObservedProcess.stateLaw, PMF.map_bind]
    simp only [step_hidden]
    have he := congrArg (fun p => p.bind (sourceStep limits sample machine)) ih
    simpa only [PMF.bind_map, Function.comp_def, law] using he

/-- Continuing the actual machine after any whole-policy trace prefix gives its
original complete terminal law. No almost-sure termination or finite alphabet is assumed. -/
theorem law_resume (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    (law limits sample machine turns world).bind
      (fun state => finishSource limits sample machine state.hidden) =
        NativeInterface.terminal machine (environment limits sample) world := by
  have he := resume_source_prefix limits sample machine turns world
  rw [← law_hidden limits sample machine turns world, PMF.bind_map] at he
  exact he

/-- Every epoch appends one decision record; `none` records are not issued batches. -/
theorem law_length (turns : ℕ) (world : World k Control Unit (ServerState n Private) input)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    state.records.length = turns := by
  induction turns generalizing state with
  | zero =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hs
    subst state
    rfl
  | succ turns ih =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hs
    obtain ⟨mid, hm, hs⟩ := hs
    simp only [step, PMF.mem_support_bind_iff] at hs
    obtain ⟨hit, _, hs⟩ := hs
    simp only [respond, PMF.mem_support_map_iff] at hs
    obtain ⟨next, _, rfl⟩ := hs
    exact congrArg (· + 1) (ih mid hm)

/-- Actual returned source epochs append exactly their one accepted receipt.
A halted epoch appends none; impossible non-boundary checkpoints are excluded
by the actual stopping construction. -/
theorem response_history
    (hit next : Phase k Control Unit (ServerState n Private) input)
    (hb : sourceBoundary limits hit)
    (hn : some next ∈ (respondSource limits sample machine (some hit)).support) :
    (server next).history =
      (receipt (some hit) (some next)).toList ++ (server hit).history := by
  cases hit with
  | ready world =>
    change world.config.tapes.state = none at hb
    simp only [respondSource, phaseStep, hb, Option.isNone_none, ite_true,
      PMF.pure_map, PMF.mem_support_pure_iff, Option.some.injEq] at hn
    subst next
    rfl
  | pending chosen =>
    cases chosen with
    | halted world => exact hb.elim
    | «local» world => exact hb.elim
    | query world op state =>
      cases op
      change (admit limits world.memory.privateState
        (world.config.channels ()).queryBuffer).isSome = true at hb
      cases ha : admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer with
      | none => simp [ha] at hb
      | some b =>
        simp only [respondSource, phaseStep, dispatch, environment, serve, ha,
          PMF.map_comp, PMF.mem_support_map_iff] at hn
        obtain ⟨⟨paths, privateState⟩, _, he⟩ := hn
        cases he
        rfl

/-- An actual source response always returns to an instruction boundary. -/
theorem response_ready (hit next : Phase k Control Unit (ServerState n Private) input)
    (hb : sourceBoundary limits hit)
    (hn : next ∈ (phaseStep machine (environment limits sample) hit).support) :
    ∃ world, next = Phase.ready world := by
  cases hit with
  | ready world =>
    change world.config.tapes.state = none at hb
    simp only [phaseStep, hb, Option.isNone_none, ite_true, PMF.mem_support_pure_iff] at hn
    exact ⟨world, hn⟩
  | pending chosen =>
    simp only [phaseStep, PMF.mem_support_map_iff] at hn
    obtain ⟨world, _, hw⟩ := hn
    exact ⟨world, hw.symm⟩

/-- A live world after a source response necessarily issued one accepted batch;
a halt decision cannot be counted as another oracle turn. -/
theorem response_live (hit : Phase k Control Unit (ServerState n Private) input)
    (world : World k Control Unit (ServerState n Private) input)
    (hb : sourceBoundary limits hit)
    (hn : Phase.ready world ∈ (phaseStep machine (environment limits sample) hit).support)
    (hl : ¬NativeUnboundedExecution.halted world) :
    (receipt (some hit) (some (.ready world))).isSome = true := by
  cases hit with
  | ready previous =>
    change previous.config.tapes.state = none at hb
    simp only [phaseStep, hb, Option.isNone_none, ite_true, PMF.mem_support_pure_iff,
      Phase.ready.injEq] at hn
    subst world
    exact (hl hb).elim
  | pending chosen =>
    cases chosen with
    | halted previous => exact hb.elim
    | «local» previous => exact hb.elim
    | query previous op state =>
      cases op
      change (admit limits previous.memory.privateState
        (previous.config.channels ()).queryBuffer).isSome = true at hb
      cases ha : admit limits previous.memory.privateState
          (previous.config.channels ()).queryBuffer with
      | none => simp [ha] at hb
      | some batch =>
        simp only [phaseStep, dispatch, environment, serve, ha, PMF.map_comp,
          PMF.mem_support_map_iff] at hn
        obtain ⟨⟨paths, privateState⟩, _, he⟩ := hn
        cases he
        rfl

/-- The whole preformed source signal denotes an issued batch, rather than halt/divergence. -/
@[expose] def batchIssued
    (hit : Option (Phase k Control Unit (ServerState n Private) input)) : Bool :=
  (sourceSignal limits hit).any fun (_, batch) => batch.isSome

/-- Exactly one receipt is produced by an actually selected source batch;
halt/divergence decisions cannot incur a fictitious issued turn. -/
theorem response_issued
    (hit next : Option (Phase k Control Unit (ServerState n Private) input))
    (hb : ∀ phase, hit = some phase → sourceBoundary limits phase)
    (hn : next ∈ (respondSource limits sample machine hit).support) :
    (receipt hit next).isSome = batchIssued limits hit := by
  cases hit with
  | none =>
    simp only [respondSource, PMF.mem_support_pure_iff] at hn
    subst next
    rfl
  | some phase =>
    have hb := hb phase rfl
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp only [respondSource, phaseStep, hb, Option.isNone_none, ite_true,
        PMF.pure_map, PMF.mem_support_pure_iff] at hn
      subst next
      rfl
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world op state =>
        cases op
        change (admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer).isSome = true at hb
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [ha] at hb
        | some batch =>
          simp only [respondSource, phaseStep, dispatch, environment, serve, ha,
            PMF.map_comp, PMF.mem_support_map_iff] at hn
          obtain ⟨⟨paths, privateState⟩, _, he⟩ := hn
          cases he
          simp [receipt, batchIssued, sourceSignal, ha, commit, Memory.record]

/-- Source state at every actual retained ready world, including native joint
resource/provenance invariants and the complete accepted receipt ledger. -/
@[expose] def Valid (origin : List (Exchange n)) (state : State n k Private Control input) : Prop :=
  match state.hidden with
  | none => True
  | some (.pending _) => False
  | some (.ready world) => Invariant limits world.memory ∧
      world.memory.privateState.history = state.records.filterMap id ++ origin

/-- The actual initial world supplies the original source invariants, not a
machine-to-policy representation assumption. -/
theorem initial_valid (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    Valid limits world.memory.privateState.history (initial world) := by
  exact ⟨hi, rfl⟩

/-- Whole-policy resource ledgers survive every actual source epoch, and silent
divergence keeps its previously charged receipts. -/
theorem step_valid (origin : List (Exchange n)) (state next : State n k Private Control input)
    (hi : Valid limits origin state) (hn : next ∈ (step limits sample machine state).support) :
    Valid limits origin next := by
  simp only [step, PMF.mem_support_bind_iff] at hn
  obtain ⟨hit, hh, hn⟩ := hn
  simp only [respond, PMF.mem_support_map_iff] at hn
  obtain ⟨nextPhase, hr, rfl⟩ := hn
  cases hs : state.hidden with
  | none =>
    simp only [hs, seekSourceFrom, PMF.mem_support_pure_iff] at hh
    subst hit
    simp only [respondSource, PMF.mem_support_pure_iff] at hr
    subst nextPhase
    trivial
  | some phase =>
    cases phase with
    | pending chosen => simp [Valid, hs] at hi
    | ready world =>
      simp only [Valid, hs] at hi
      obtain ⟨hw, hl⟩ := hi
      cases hit with
      | none =>
        simp only [respondSource, PMF.mem_support_pure_iff] at hr
        subst nextPhase
        trivial
      | some hit =>
        rw [hs] at hh
        have hstate := seek_state limits sample machine (.ready world) hit hh
        have hinv := seekSource_invariant limits sample machine world hit hw hh
        have hh' := hh
        simp only [seekSourceFrom] at hh'
        have hb := ((StoppedProcess.terminal_support _ _ _ _ _).mp hh').1
        simp only [respondSource, PMF.mem_support_map_iff] at hr
        obtain ⟨out, ho, rfl⟩ := hr
        have hmem := phase_invariant limits sample machine hit out hinv ho
        have hhist := response_history limits sample machine hit out hb
          ((PMF.mem_support_map_iff _ _ _).mpr ⟨out, ho, rfl⟩)
        have hready := response_ready limits sample machine hit out hb ho
        obtain ⟨w, rfl⟩ := hready
        refine ⟨hmem, ?_⟩
        rw [hstate] at hhist
        simp only [server, worldOf] at hhist
        rw [hhist, hl]
        cases receipt (some hit) (some (.ready w)) <;>
          simp

/-- Every whole-policy prefix comes from actual execution and keeps source
feasibility/resources/provenance, with earlier charges retained on divergence. -/
theorem law_valid (turns : ℕ) (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    Valid limits world.memory.privateState.history state := by
  induction turns generalizing state with
  | zero =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hs
    subst state
    exact initial_valid limits world hi
  | succ turns ih =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hs
    obtain ⟨mid, hm, hn⟩ := hs
    exact step_valid limits sample machine _ mid state (ih mid hm) hn

/-- All accepted receipt prefixes, including prefixes retained on divergence,
remain turn/deadline feasible and never reuse a source opportunity. -/
theorem law_ledger_bound (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support) :
    (state.records.filterMap id ++ world.memory.privateState.history).length ≤ limits.turns ∧
      ((state.records.filterMap id ++ world.memory.privateState.history).map
        Exchange.duration).sum ≤ limits.deadline ∧
      noReuse (state.records.filterMap id ++ world.memory.privateState.history) := by
  induction turns generalizing state with
  | zero =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hs
    subst state
    obtain ⟨_, he, hd, ht, hn⟩ := hi.1
    simpa only [initial, List.filterMap_nil, List.nil_append] using
      (show world.memory.privateState.history.length ≤ limits.turns ∧
        (world.memory.privateState.history.map Exchange.duration).sum ≤ limits.deadline ∧
        noReuse world.memory.privateState.history from ⟨ht, he ▸ hd, hn⟩)
  | succ turns ih =>
    have hv := law_valid limits sample machine _ world hi state hs
    cases he : state.hidden with
    | some phase =>
      cases phase with
      | pending chosen => simp [Valid, he] at hv
      | ready next =>
        simp only [Valid, he] at hv
        obtain ⟨_, hsum, hD, ht, hn⟩ := hv.1.1
        have hd := hsum ▸ hD
        rw [hv.2] at ht hd hn
        exact ⟨ht, hd, hn⟩
    | none =>
      simp only [law, ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hs
      obtain ⟨mid, hm, hs⟩ := hs
      simp only [step, PMF.mem_support_bind_iff] at hs
      obtain ⟨hit, _, hs⟩ := hs
      simp only [respond, PMF.mem_support_map_iff] at hs
      obtain ⟨next, hr, rfl⟩ := hs
      simp only at he
      subst next
      cases hit with
      | none => simpa [receipt] using ih mid hm
      | some phase => simp [respondSource] at hr

private theorem seek_halted (world : World k Control Unit (ServerState n Private) input)
    (hh : NativeUnboundedExecution.halted world) :
    seekSourceFrom limits sample machine (some (.ready world)) =
      PMF.pure (some (.ready world)) := by
  unfold seekSourceFrom
  exact StoppedProcess.terminal_halted _ _ _ _ hh

/-- A still-live epoch world has already issued at least the epoch index's
number of batches. Halt/divergence decisions absorb instead of creating fake turns. -/
theorem law_live_count (turns : ℕ)
    (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine turns world).support)
    (he : state.hidden = some (.ready next)) (hl : ¬NativeUnboundedExecution.halted next) :
    turns ≤ next.memory.privateState.history.length := by
  induction turns generalizing state next with
  | zero => omega
  | succ turns ih =>
    simp only [law, ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hs
    obtain ⟨mid, hm, hs⟩ := hs
    have hv := law_valid limits sample machine turns world hi mid hm
    simp only [step, PMF.mem_support_bind_iff] at hs
    obtain ⟨hit, hh, hs⟩ := hs
    simp only [respond, PMF.mem_support_map_iff] at hs
    obtain ⟨nextPhase, hr, rfl⟩ := hs
    simp only at he
    subst nextPhase
    cases hz : mid.hidden with
    | none =>
      simp only [hz, seekSourceFrom, PMF.mem_support_pure_iff] at hh
      subst hit
      simp [respondSource] at hr
    | some phase =>
      cases phase with
      | pending chosen => simp [Valid, hz] at hv
      | ready previous =>
        rw [hz] at hh
        have hp : ¬NativeUnboundedExecution.halted previous := by
          intro hp
          rw [seek_halted limits sample machine previous hp, PMF.mem_support_pure_iff] at hh
          subst hit
          have hhalt : previous.config.tapes.state = none := hp
          simp only [respondSource, phaseStep, hhalt,
            Option.isNone_none, ite_true, PMF.pure_map, PMF.mem_support_pure_iff,
            Option.some.injEq, Phase.ready.injEq] at hr
          subst next
          exact hl hp
        have hcount := ih previous mid hm hz hp
        cases hit with
        | none => simp [respondSource] at hr
        | some hit =>
          have hstate := seek_state limits sample machine (.ready previous) hit hh
          simp only [seekSourceFrom] at hh
          have hb := ((StoppedProcess.terminal_support _ _ _ _ _).mp hh).1
          simp only [respondSource, PMF.mem_support_map_iff] at hr
          obtain ⟨out, ho, he⟩ := hr
          cases he
          have hn := response_live limits sample machine hit next hb ho hl
          have hx := response_history limits sample machine hit (.ready next) hb
            ((PMF.mem_support_map_iff _ _ _).mpr ⟨_, ho, rfl⟩)
          rw [hstate] at hx
          simp only [server, worldOf] at hx
          have hlen := congrArg List.length hx
          cases hreceipt : receipt (some hit) (some (.ready next)) with
          | none => simp [hreceipt] at hn
          | some x => simp only [hreceipt, Option.toList_some, List.length_append,
              List.length_singleton] at hlen
                      omega

/-- After the finite source turn budget plus one silent halting epoch, every
actual native competitor is halted or has diverged. No uniform local clock is used. -/
theorem law_done (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine (limits.turns + 1) world).support) :
    state.hidden = none ∨ ∃ next, state.hidden = some (.ready next) ∧
      NativeUnboundedExecution.halted next := by
  have hv := law_valid limits sample machine _ world hi state hs
  cases he : state.hidden with
  | none => exact Or.inl rfl
  | some phase =>
    cases phase with
    | pending chosen => simp [Valid, he] at hv
    | ready next =>
      refine Or.inr ⟨next, rfl, ?_⟩
      by_contra hl
      have hc := law_live_count limits sample machine _ world next hi state hs he hl
      simp only [Valid, he] at hv
      have hb := hv.1.1.2.2.2.1
      omega

/-- Completed/divergent whole-policy traces can add only a zero-call decision;
they cannot sample another oracle response or erase their earlier receipts. -/
theorem step_done (state : State n k Private Control input)
    (hd : state.hidden = none ∨ ∃ world, state.hidden = some (.ready world) ∧
      NativeUnboundedExecution.halted world) :
    step limits sample machine state = PMF.pure ⟨state.hidden, none :: state.records⟩ := by
  rcases hd with hn | ⟨world, he, hh⟩
  · simp [step, hn, seekSourceFrom, respond, respondSource, receipt]
  · have hs : world.config.tapes.state = none := hh
    simp only [step, he, seek_halted limits sample machine world hh, PMF.pure_bind,
      respond, respondSource, phaseStep, hs, Option.isNone_none, ite_true, PMF.pure_map,
      receipt]

/-- Whole-policy representation of the complete actual native terminal law,
using finitely many genuine source epochs and arbitrary silent machine execution.
The trace additionally retains accrued prefix resources on divergent outcomes. -/
theorem law_terminal (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    (law limits sample machine (limits.turns + 1) world).map State.hidden =
      NativeInterface.terminal machine (environment limits sample) world := by
  rw [← law_resume limits sample machine (limits.turns + 1) world]
  change ((law limits sample machine (limits.turns + 1) world).bind
    (fun state => PMF.pure state.hidden)) = _
  apply PMF.bind_congr_on_support
  intro state hs
  rcases law_done limits sample machine world hi state hs with hn | ⟨next, he, hh⟩
  · simp [hn, finishSource]
  · simp only [he, finishSource]
    exact (StoppedProcess.terminal_halted _ _ _ (Phase.ready next) hh).symm

/-- Actual nonnegative invoice for one completed/canceled batch. -/
@[expose] def charge (record : Record n) : ℝ≥0∞ := record.elim 0 (fun x => x.tokens)

/-- Actual concurrent batch maximum, with zero for a decision issuing no batch. -/
@[expose] def duration (record : Record n) : ℝ≥0∞ := record.elim 0 (fun x => x.duration)

/-- Source issued-batch count; decisions are not automatically issued batches. -/
@[expose] def issued (record : Record n) : ℝ≥0∞ := if record.isSome then 1 else 0

/-- Accrued nonnegative resource/count from the actual receipts. -/
@[expose] def accrued (score : Record n → ℝ≥0∞) (state : State n k Private Control input) :
    ℝ≥0∞ := (state.records.map score).sum

/-- Issued batches never exceed the actual number of epoch decisions. -/
theorem accrued_issued_le (state : State n k Private Control input) :
    accrued issued state ≤ state.records.length := by
  have he (records : List (Record n)) : (records.map issued).sum ≤ records.length := by
    induction records with
    | nil => simp
    | cons record records ih =>
      have hr : issued record ≤ 1 := by cases record <;> simp [issued]
      calc
        _ ≤ 1 + (records.length : ℝ≥0∞) := add_le_add hr ih
        _ = _ := by simp [Nat.cast_add, add_comm]
  exact he state.records

/-- Whole-policy readback is the actual native terminal-world law, including
its divergent mass, arbitrary private metadata and successful-output conventions. -/
theorem law_native_terminal (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    (law limits sample machine (limits.turns + 1) world).map
      (fun state => state.hidden.map worldOf) =
        NativeUnboundedExecution.terminal machine (environment limits sample) world := by
  have he := congrArg (PMF.map (Option.map worldOf))
    (law_terminal limits sample machine world hi)
  rw [NativeInterface.terminal_native, PMF.map_comp, PMF.map_comp] at he
  simpa only [Option.map_map, Function.comp_def, worldOf, Option.map_id,
    Option.map_id_fun', PMF.map_id] using he

/-- The actual issued count is the accepted receipt count, including on divergence. -/
theorem accrued_issued (state : State n k Private Control input) :
    accrued issued state = (state.records.filterMap id).length := by
  have he (records : List (Record n)) : (records.map issued).sum =
      ((records.filterMap id).length : ℝ≥0∞) := by
    induction records with
    | nil => simp
    | cons record records ih =>
      cases record <;> simp [issued, ih, Nat.cast_add, add_comm]
  exact he state.records

/-- Accrued trace charges are exactly the sum of all accepted receipt invoices. -/
theorem accrued_charge (state : State n k Private Control input) :
    accrued charge state = (((state.records.filterMap id).map Exchange.tokens).sum : ℝ≥0∞) := by
  have he (records : List (Record n)) : (records.map charge).sum =
      (((records.filterMap id).map Exchange.tokens).sum : ℝ≥0∞) := by
    induction records with
    | nil => simp
    | cons record records ih =>
      cases record <;> simp [charge, ih, Nat.cast_add]
  exact he state.records

/-- Accrued physical duration is the sum of actual concurrent batch maxima. -/
theorem accrued_duration (state : State n k Private Control input) :
    accrued duration state =
      (((state.records.filterMap id).map Exchange.duration).sum : ℝ≥0∞) := by
  have he (records : List (Record n)) : (records.map duration).sum =
      (((records.filterMap id).map Exchange.duration).sum : ℝ≥0∞) := by
    induction records with
    | nil => simp
    | cons record records ih =>
      cases record <;> simp [duration, ih]
  exact he state.records

/-- On every terminating path from an empty accepted history, the complete
trace carries exactly the original native bill and physical duration. Divergent
traces keep accrued receipts but are not assigned a native terminal-world bill. -/
theorem terminal_resources (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine (limits.turns + 1) world).support)
    (he : state.hidden = some (.ready next)) :
    accrued charge state = (tokenBill next.memory.events : ℝ≥0∞) ∧
      accrued duration state = (elapsed next.memory.events : ℝ≥0∞) := by
  have hv := law_valid limits sample machine _ world hi state hs
  simp only [Valid, he, hzero, List.append_nil] at hv
  obtain ⟨hmem, hledger⟩ := hv
  obtain ⟨hformed, hcost, htime, _⟩ := hmem
  rw [accrued_charge, accrued_duration, hcost, htime, hledger, hformed.2.1, hledger]
  exact ⟨(ENNReal.coe_natCast _).symm, rfl⟩

/-- Successful-output-only native selection admission transfers to the complete
actual receipt trace. The acceptance and provenance condition is not inferred
for arbitrary non-selection-only machines. -/
theorem terminal_provenance (m : ℕ) (accept : Finset (Fin m) → Bool)
    (world next : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (hselect : NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := n) m) (decodeFamily m) accept world)
    (state : State n k Private Control input)
    (hs : state ∈ (law limits sample machine (limits.turns + 1) world).support)
    (he : state.hidden = some (.ready next)) (C : Finset (Fin m))
    (hc : NativeOpenSelection.result (decodeFamily m) next = some C) (ha : accept C = true) :
    C ⊆ sourceAvailable m (state.records.filterMap id) := by
  have hn : some next ∈ (NativeUnboundedExecution.terminal machine
      (environment limits sample) world).support := by
    rw [← law_native_terminal limits sample machine world hi]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨state, hs, by rw [he]; rfl⟩
  have hp := NativeBatch.terminal_provenance limits sample machine m accept world next
    hi hselect hn C hc ha
  have hv := law_valid limits sample machine _ world hi state hs
  simp only [Valid, he, hzero, List.append_nil] at hv
  rwa [hv.2] at hp

end Cslib.Probability.NativeBatch.Trace
