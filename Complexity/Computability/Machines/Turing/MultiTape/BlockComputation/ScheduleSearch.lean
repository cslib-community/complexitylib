/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluator
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleCounter
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.RootDecision
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerOutput
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Sequential native search over movement schedules

The caller retains a binary schedule counter and one optional decision. Each candidate invokes
the initialized concrete evaluator on the same original input. A valid halted root ends the
search; FAIL or live roots advance the counter. The streamed range guard constructs neither a
list of schedules nor the exponential range bound. Runtime arguments enter through `initial`.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Runtime input length, block width and schedule horizon. -/
abbrev Args := ℕ × ℕ × ℕ
/-- Actual arguments, schedule cursor and optional halted-root decision. -/
abbrev CallerState := Args × ℕ × Option Bool

/-- Original input length retained by a search. -/
@[expose] def inputLength : Args → ℕ := fun (N, _, _) => N
/-- Block width retained by a search. -/
@[expose] def blockWidth : Args → ℕ := fun (_, b, _) => b
/-- Number of block intervals retained by a search. -/
@[expose] def horizon : Args → ℕ := fun (_, _, q) => q
/-- Numeric schedule currently retained by a caller. -/
@[expose] def cursor : CallerState → ℕ := fun (_, σ, _) => σ

/-- Active search or one suspended search with its initialized evaluator. -/
abbrev State (k : ℕ) (Q : Type) :=
  CallerState ⊕ (CallerState × InitializedEvaluator.State k Q)

/-- The caller continues only before finding a decision and while its schedule is in range. -/
@[expose] def pending (k : ℕ) : CallerState → Bool :=
  fun ((_, _, q), σ, result) => !result.isSome && ScheduleCounter.valid k (σ, q)

/-- Start the first numeric schedule with no decision. -/
@[expose] def initial (args : Args) : State k Q := .inl (args, 0, none)

/-- Request one concrete initialized evaluator run. -/
@[expose] def request (k s : ℕ) : CallerState → Option (InitializedEvaluator.State k Q) :=
  fun ((N, b, q), σ, result) =>
    if pending k ((N, b, q), σ, result) then
      some (InitializedEvaluator.start k s (N, b, σ, q)) else none

/-- Decode only returned active evaluator banks; incomplete or suspended states give no decision. -/
@[expose] def outcome (e : Q ≃ Fin s) : Args × InitializedEvaluator.State k Q → Option Bool
  | ((_, b, _), .inr (.inl ((_, _, _, _, m, _, _), (p, _, r), bank, _, _))) =>
    RootDecision.classify k e (b, RawController.Output.decode
      ((Encoding.width k s b, m, p, r, 0), bank))
  | _ => none

/-- Preserve a halted-root decision or advance to the next schedule after a failed candidate. -/
@[expose] def resume (e : Q ≃ Fin s) :
    CallerState → InitializedEvaluator.State k Q → CallerState := fun (args, σ, _) returned =>
  match outcome e (args, returned) with
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

/-- One fixed search machine calls the concrete evaluator on the original read-only input. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) :=
  (caller k).withCalls (InitializedEvaluator.machine M e) (request k s) (resume e)

/-- Only a returned caller state exposes a decision. -/
@[expose] def answer : State k Q → Option Bool :=
  Sum.elim (fun (_, _, result) => result) (fun _ => none)

/-- Binary input length, block width and horizon. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat encNat)
/-- Binary schedule counter and decision beside the actual arguments. -/
@[expose] noncomputable def encCaller : CallerState ↪ List Bool :=
  encPair encArgs (encPair encNat (encOption encBool))

variable [Finite Q]

/-- Actual search payloads and suspended evaluator states are charged explicitly. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum encCaller (encPair encCaller (InitializedEvaluator.encState (k := k) (Q := Q)))

/-- Native initialization stores only arguments, a zero counter and no decision. -/
theorem initial_inSpace : ComputableInSpace (initial (k := k) (Q := Q)) encArgs encState
    (fun a => (encArgs a).length) := by
  have hid : ComputableInSpace (fun a : Args => a) encArgs encArgs
      (fun a => (encArgs a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hc := budget_prod hid (budget_prod (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encOption encBool) none (.refl _)))
  exact (budget_comp_linear (of_inO (ComputableInO.inl encCaller
    (encPair encCaller (InitializedEvaluator.encState (k := k) (Q := Q))))) hc).of_enc_eq
      fun _ => rfl

omit [Finite Q] in
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

/-- The request initializer charges the complete actual runtime arguments. -/
theorem request_inSpace : ComputableInSpace (request (Q := Q) k s) encCaller
    (encOption InitializedEvaluator.encState) (fun a => (encCaller a).length) := by
  have ha := fst encArgs (encPair encNat (encOption encBool))
  have hr := snd encArgs (encPair encNat (encOption encBool))
  have hargs := budget_prod ha.fst'
    (budget_prod ha.snd'.fst' (budget_prod hr.fst' ha.snd'.snd'))
  have hstart := budget_comp_linear (InitializedEvaluator.start_inSpace (k := k) (s := s)
    (Q := Q)) hargs
  have hsome := budget_comp_linear
    (encC := encOption (InitializedEvaluator.encState (k := k) (Q := Q)))
    (of_inO (ComputableInDegree.optionSome
      (enc₁ := InitializedEvaluator.encState (k := k) (Q := Q))).inO_one) hstart
  exact (budget_ite (pending_inSpace k) hsome
    (budget_const (encB := encOption InitializedEvaluator.encState) none (.refl _))).of_enc_eq
      fun _ => rfl

/-- Returned-bank extraction and header-only root classification are native. -/
theorem outcome_inSpace (e : Q ≃ Fin s) : ComputableInSpace (outcome (k := k) e)
    (encPair encArgs InitializedEvaluator.encState) (encOption encBool)
    (fun a => (encPair encArgs InitializedEvaluator.encState a).length) := by
  let encC := RawController.Query.encContext ConcreteSupplier.encContext
  have ha := fst encArgs encC
  have hc := snd encArgs encC
  have hb := ha.snd'.fst'
  have hcontext := hc.fst'
  have hfull := hc.snd'
  have hpar := hfull.fst'
  have hraw := hfull.snd'
  have hm := hcontext.snd'.snd'.snd'.snd'.fst'
  have hp := hpar.fst'
  have hr := hpar.snd'.snd'
  have hbank := hraw.fst'
  have hwidth := budget_comp_linear (Encoding.width_inSpace k s) hb
  have hdecodeArgs := budget_prod (budget_prod hwidth (budget_prod hm (budget_prod hp
    (budget_prod hr (budget_const (encB := encNat) 0 (.refl _)))))) hbank
  have hword := budget_comp_linear listToBits
    (budget_comp_linear RawController.Output.decode_inSpace hdecodeArgs)
  have hroot := budget_comp_linear (RootDecision.classify_inSpace (k := k) e)
    (budget_prod hb hword)
  have hsuspended := budget_const
    (encIn := encPair encArgs (encPair encC (QueryReplay.GateReply.encState (k := k) (Q := Q))))
    (encB := encOption encBool) none (.refl _)
  have hinitial := budget_const (encIn := encPair encArgs Initializer.encState)
    (encB := encOption encBool) none (.refl _)
  exact (sumElimSnd hinitial (sumElimSnd hroot hsuspended)).of_enc_eq fun a => by
    rcases a with ⟨args, initial | (active | suspended)⟩ <;> rfl

/-- Native resumption retains arguments and either a decision or the incremented counter. -/
theorem resume_inSpace (e : Q ≃ Fin s) : ComputableInSpace
    (fun a : CallerState × InitializedEvaluator.State k Q => resume e a.1 a.2)
    (encPair encCaller InitializedEvaluator.encState) encCaller
    (fun a => (encPair encCaller InitializedEvaluator.encState a).length) := by
  have hc := fst encCaller (InitializedEvaluator.encState (k := k) (Q := Q))
  have ht := snd encCaller (InitializedEvaluator.encState (k := k) (Q := Q))
  have ha := hc.fst'
  have hσ := hc.snd'.fst'
  have hout := budget_comp_linear (outcome_inSpace e) (budget_prod ha ht)
  have hisSome := budget_finite (encC := encBool) (Option.isSome : Option Bool → Bool) hout
  have hσ' := budget_ite hisSome hσ (budget_natSucc hσ)
  refine (budget_prod ha (budget_prod hσ' hout)).of_enc_eq ?_
  rintro ⟨⟨args, σ, result⟩, returned⟩
  cases ho : outcome e (args, returned) <;> simp [resume, ho, encCaller, encPair_apply]

/-- Extract the stored caller decision without constructing an output word. -/
theorem answer_inSpace : ComputableInSpace (answer (k := k) (Q := Q)) encState
    (encOption encBool) (fun a => (encState a).length) :=
  sumElim (snd encArgs (encPair encNat (encOption encBool))).snd'
    (budget_const (encIn := encPair encCaller InitializedEvaluator.encState) none (.refl _))

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

/-- Native query component of the concrete sequential search. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  QueryMachine.withCalls_query_inSpace (caller k) (InitializedEvaluator.machine M e)
    (request k s) (resume e) encCaller InitializedEvaluator.encState (caller_query_inSpace k)
    (InitializedEvaluator.machine_query_inSpace M e) request_inSpace

/-- Native transitions cover actual candidate execution and classified resumption. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_next_inSpace (caller k) (InitializedEvaluator.machine M e)
    (request k s) (resume e) encCaller InitializedEvaluator.encState (caller_next_inSpace k)
    (InitializedEvaluator.machine_next_inSpace M e)
    (InitializedEvaluator.machine_halted_inSpace M e) request_inSpace (resume_inSpace e)

/-- Candidate output streams are discarded. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_emit_inSpace (caller k) (InitializedEvaluator.machine M e)
    (request k s) (resume e) encCaller InitializedEvaluator.encState
    (caller_emit_inSpace k) request_inSpace

/-- Search completion uses only the native stored-decision/range guard. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  QueryMachine.withCalls_halted_inSpace (caller k) (InitializedEvaluator.machine M e)
    (request k s) (resume e) encCaller InitializedEvaluator.encState (caller_halted_inSpace k)

/-- The final decision remains stored in the returned caller state. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  QueryMachine.withCalls_finish_inSpace (caller k) (InitializedEvaluator.machine M e)
    (request k s) (resume e) encCaller InitializedEvaluator.encState (caller_finish_inSpace k)

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
