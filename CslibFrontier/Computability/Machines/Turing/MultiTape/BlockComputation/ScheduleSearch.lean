/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleCounter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Sequential native search over movement schedules

The caller retains a binary schedule counter and one optional decision. Each candidate invokes
a fixed schedule evaluator on the same original input. A candidate with an outcome ends the
search; one without an outcome advances the counter. The streamed range guard constructs
neither a list of schedules nor the exponential range bound. Runtime arguments enter through
`initial`.

The search is generic over its `Evaluator`: a query machine with a state encoding, an entry
state for each schedule number, and an outcome read from a halted state, all with native
component certificates. Williams's initialized concrete evaluator is one instance
(`InitializedEvaluator.scheduleEvaluator`).

## Main definitions

* `ScheduleSearch.Evaluator`: a per-schedule evaluator with native certificates.
* `ScheduleSearch.machine`: the fixed search machine calling an evaluator once per schedule.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Runtime input length, block width and schedule horizon. -/
abbrev Args := ℕ × ℕ × ℕ
/-- Actual arguments, schedule cursor and optional halted-root decision. -/
abbrev CallerState := Args × ℕ × Option Bool
/-- Runtime input length, block width, schedule number and horizon of one candidate. -/
abbrev StartArgs := ℕ × ℕ × ℕ × ℕ

/-- Original input length retained by a search. -/
@[expose] def inputLength : Args → ℕ := fun (N, _, _) => N
/-- Block width retained by a search. -/
@[expose] def blockWidth : Args → ℕ := fun (_, b, _) => b
/-- Number of block intervals retained by a search. -/
@[expose] def horizon : Args → ℕ := fun (_, _, q) => q
/-- Numeric schedule currently retained by a caller. -/
@[expose] def cursor : CallerState → ℕ := fun (_, σ, _) => σ

/-- Binary input length, block width and horizon. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat encNat)
/-- Binary input length, block width, schedule number and horizon. -/
@[expose] noncomputable def encStartArgs : StartArgs ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))
/-- Binary schedule counter and decision beside the actual arguments. -/
@[expose] noncomputable def encCaller : CallerState ↪ List Bool :=
  encPair encArgs (encPair encNat (encOption encBool))

/-- A fixed query machine evaluating one numeric movement schedule on the original input.
`start (N, b, σ, q)` enters schedule `σ`; `outcome ((N, b, q), s)` reads an optional decision
from a returned state `s`. Each component has a native certificate charging only its actual
encoded argument. -/
structure Evaluator where
  /-- Evaluator states. -/
  State : Type
  /-- Physical encoding of evaluator states. -/
  encState : State ↪ List Bool
  /-- The fixed evaluator machine, run on the original read-only input. -/
  machine : QueryMachine State
  /-- Entry state from the input length, block width, schedule number and horizon. -/
  start : StartArgs → State
  /-- Optional decision read from a returned state and the search arguments. -/
  outcome : Args × State → Option Bool
  /-- Native evaluator queries. -/
  machine_query_inSpace : ComputableInSpace machine.query encState encNat
    (fun a => (encState a).length)
  /-- Native evaluator transitions. -/
  machine_next_inSpace : ComputableInSpace machine.next (encPair encState (encOption encBool))
    encState (fun a => (encPair encState (encOption encBool) a).length)
  /-- Native evaluator halting test. -/
  machine_halted_inSpace : ComputableInSpace machine.halted encState encBool
    (fun a => (encState a).length)
  /-- Native entry from the actual binary arguments. -/
  start_inSpace : ComputableInSpace start encStartArgs encState
    (fun a => (encStartArgs a).length)
  /-- Native outcome extraction from the returned state. -/
  outcome_inSpace : ComputableInSpace outcome (encPair encArgs encState) (encOption encBool)
    (fun a => (encPair encArgs encState a).length)

variable (E : Evaluator)

/-- Active search or one suspended search with its evaluator. -/
abbrev State := CallerState ⊕ (CallerState × E.State)

/-- The caller continues only before finding a decision and while its schedule is in range. -/
@[expose] def pending (k : ℕ) : CallerState → Bool :=
  fun ((_, _, q), σ, result) => !result.isSome && ScheduleCounter.valid k (σ, q)

/-- Start the first numeric schedule with no decision. -/
@[expose] def initial (args : Args) : State E := .inl (args, 0, none)

/-- Request one evaluator run for the current schedule. -/
@[expose] def request (k : ℕ) : CallerState → Option E.State :=
  fun ((N, b, q), σ, result) =>
    if pending k ((N, b, q), σ, result) then some (E.start (N, b, σ, q)) else none

/-- Preserve a returned decision or advance to the next schedule after a candidate without one. -/
@[expose] def resume : CallerState → E.State → CallerState := fun (args, σ, _) returned =>
  match E.outcome (args, returned) with
  | some result => (args, σ, some result)
  | none => (args, σ + 1, none)

/-- The fixed caller template is already halted. -/
@[expose] def caller (k : ℕ) : QueryMachine CallerState where
  init := ((0, 0, 0), 0, some false)
  query _ := 0
  next := Prod.fst
  emit _ := []
  halted := fun state => !pending k state
  finish _ := []

/-- One fixed search machine calls the evaluator on the original read-only input. -/
@[expose] def machine (k : ℕ) : QueryMachine (State E) :=
  (caller k).withCalls E.machine (request E k) (resume E)

variable {E} in
/-- Only a returned caller state exposes a decision. -/
@[expose] def answer : State E → Option Bool :=
  Sum.elim (fun (_, _, result) => result) (fun _ => none)

/-- Actual search payloads and suspended evaluator states are charged explicitly. -/
@[expose] noncomputable def encState : State E ↪ List Bool :=
  encSum encCaller (encPair encCaller E.encState)

/-- Native initialization stores only arguments, a zero counter and no decision. -/
theorem initial_inSpace : ComputableInSpace (initial E) encArgs (encState E)
    (fun a => (encArgs a).length) := by
  have hid : ComputableInSpace (fun a : Args => a) encArgs encArgs
      (fun a => (encArgs a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hc := budget_prod hid (budget_prod (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encOption encBool) none (.refl _)))
  exact (budget_comp_linear (of_inO (ComputableInO.inl encCaller
    (encPair encCaller E.encState))) hc).of_enc_eq fun _ => rfl

/-- The native guard tests only actual counters and the stored decision. -/
theorem pending_inSpace (k : ℕ) : ComputableInSpace (pending k) encCaller encBool
    (fun a => (encCaller a).length) := by
  have ha := fst encArgs (encPair encNat (encOption encBool))
  have hr := snd encArgs (encPair encNat (encOption encBool))
  have hvalid := budget_comp_linear (ScheduleCounter.valid_inSpace k)
    (budget_prod hr.fst' ha.snd'.snd')
  have hsome := budget_finite (encC := encBool) (Option.isSome : Option Bool → Bool) hr.snd'
  exact (budget_finite (encC := encBool) (fun q : Bool × Bool => !q.1 && q.2)
    (budget_prod hsome hvalid)).of_enc_eq fun _ => rfl

/-- The request charges the complete actual runtime arguments. -/
theorem request_inSpace (k : ℕ) : ComputableInSpace (request E k) encCaller
    (encOption E.encState) (fun a => (encCaller a).length) := by
  have ha := fst encArgs (encPair encNat (encOption encBool))
  have hr := snd encArgs (encPair encNat (encOption encBool))
  have hargs := budget_prod ha.fst'
    (budget_prod ha.snd'.fst' (budget_prod hr.fst' ha.snd'.snd'))
  have hstart := budget_comp_linear E.start_inSpace hargs
  have hsome := budget_comp_linear (encC := encOption E.encState)
    (of_inO (ComputableInDegree.optionSome (enc₁ := E.encState)).inO_one) hstart
  exact (budget_ite (pending_inSpace k) hsome
    (budget_const (encB := encOption E.encState) none (.refl _))).of_enc_eq fun _ => rfl

/-- Native resumption retains arguments and either a decision or the incremented counter. -/
theorem resume_inSpace : ComputableInSpace (fun a : CallerState × E.State => resume E a.1 a.2)
    (encPair encCaller E.encState) encCaller
    (fun a => (encPair encCaller E.encState a).length) := by
  have hc := fst encCaller E.encState
  have ht := snd encCaller E.encState
  have ha := hc.fst'
  have hσ := hc.snd'.fst'
  have hout := budget_comp_linear E.outcome_inSpace (budget_prod ha ht)
  have hisSome := budget_finite (encC := encBool) (Option.isSome : Option Bool → Bool) hout
  have hσ' := budget_ite hisSome hσ (budget_natSucc hσ)
  refine (budget_prod ha (budget_prod hσ' hout)).of_enc_eq ?_
  rintro ⟨⟨args, σ, result⟩, returned⟩
  cases ho : E.outcome (args, returned) <;> simp [resume, ho, encCaller, encPair_apply]

/-- Extract the stored caller decision without constructing an output word. -/
theorem answer_inSpace : ComputableInSpace (answer (E := E)) (encState E)
    (encOption encBool) (fun a => (encState E a).length) :=
  sumElim (snd encArgs (encPair encNat (encOption encBool))).snd'
    (budget_const (encIn := encPair encCaller E.encState) none (.refl _))

private theorem caller_query_inSpace (k : ℕ) : ComputableInSpace (caller k).query encCaller
    encNat (fun a => (encCaller a).length) := budget_const 0 (.refl _)
private theorem caller_next_inSpace (k : ℕ) : ComputableInSpace (caller k).next
    (encPair encCaller (encOption encBool)) encCaller
    (fun a => (encPair encCaller (encOption encBool) a).length) := fst _ _
private theorem caller_emit_inSpace (k : ℕ) : ComputableInSpace (caller k).emit
    (encPair encCaller (encOption encBool)) encBits
    (fun a => (encPair encCaller (encOption encBool) a).length) := budget_const [] (.refl _)
private theorem caller_halted_inSpace (k : ℕ) : ComputableInSpace (caller k).halted encCaller
    encBool (fun a => (encCaller a).length) :=
  budget_finite Bool.not (pending_inSpace k)
private theorem caller_finish_inSpace (k : ℕ) : ComputableInSpace (caller k).finish encCaller
    encBits (fun a => (encCaller a).length) := budget_const [] (.refl _)

/-- Native query component of the sequential search. -/
theorem machine_query_inSpace (k : ℕ) : ComputableInSpace (machine E k).query (encState E)
    encNat (fun a => (encState E a).length) :=
  QueryMachine.withCalls_query_inSpace (caller k) E.machine (request E k) (resume E) encCaller
    E.encState (caller_query_inSpace k) E.machine_query_inSpace (request_inSpace E k)

/-- Native transitions cover actual candidate execution and resumption. -/
theorem machine_next_inSpace (k : ℕ) : ComputableInSpace (machine E k).next
    (encPair (encState E) (encOption encBool)) (encState E)
    (fun a => (encPair (encState E) (encOption encBool) a).length) :=
  QueryMachine.withCalls_next_inSpace (caller k) E.machine (request E k) (resume E) encCaller
    E.encState (caller_next_inSpace k) E.machine_next_inSpace E.machine_halted_inSpace
    (request_inSpace E k) (resume_inSpace E)

/-- Candidate output streams are discarded. -/
theorem machine_emit_inSpace (k : ℕ) : ComputableInSpace (machine E k).emit
    (encPair (encState E) (encOption encBool)) encBits
    (fun a => (encPair (encState E) (encOption encBool) a).length) :=
  QueryMachine.withCalls_emit_inSpace (caller k) E.machine (request E k) (resume E) encCaller
    E.encState (caller_emit_inSpace k) (request_inSpace E k)

/-- Search completion uses only the native stored-decision/range guard. -/
theorem machine_halted_inSpace (k : ℕ) : ComputableInSpace (machine E k).halted (encState E)
    encBool (fun a => (encState E a).length) :=
  QueryMachine.withCalls_halted_inSpace (caller k) E.machine (request E k) (resume E) encCaller
    E.encState (caller_halted_inSpace k)

/-- The final decision remains stored in the returned caller state. -/
theorem machine_finish_inSpace (k : ℕ) : ComputableInSpace (machine E k).finish (encState E)
    encBits (fun a => (encState E a).length) :=
  QueryMachine.withCalls_finish_inSpace (caller k) E.machine (request E k) (resume E) encCaller
    E.encState (caller_finish_inSpace k)

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
