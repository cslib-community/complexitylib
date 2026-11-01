/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.BalancedParameters

/-!
# Increasing time guesses on the original input

The outer caller stores the input length, a binary time guess and an optional final decision.
Each guess runs the complete schedule search with balanced parameters. An undecided search
increments the guess; either Boolean decision stops. Only the final Boolean is emitted.
No time bound or time-constructibility witness is consulted by the machine.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Original input length, current time guess and a returned decision. -/
abbrev CallerState := ℕ × ℕ × Option Bool
/-- One outer caller or one suspended caller with its schedule-search state. -/
abbrev State (k : ℕ) (Q : Type) := CallerState ⊕ (CallerState × ScheduleSearch.State k Q)

/-- Begin with a positive guess at least the input length. -/
@[expose] def initial (N : ℕ) : State k Q := .inl (N, N + 1, none)

/-- Actual runtime arguments for the current guess. -/
@[expose] def parameters : CallerState → ScheduleSearch.Args := fun (N, T, _) =>
  (N, BalancedParameters.blockWidth T, BalancedParameters.horizon T)

/-- Both accepting and rejecting returned decisions stop the caller. -/
@[expose] def pending : CallerState → Bool := fun (_, _, result) => !result.isSome

/-- Start exactly one native schedule search on the original input. -/
@[expose] def request : CallerState → Option (ScheduleSearch.State k Q) := fun state =>
  if pending state then some (ScheduleSearch.initial (parameters state)) else none

/-- A live result advances the guess; a decision, including false, is retained. -/
@[expose] def resume : CallerState → ScheduleSearch.State k Q → CallerState :=
  fun (N, T, _) returned => match ScheduleSearch.answer returned with
  | none => (N, T + 1, none)
  | some result => (N, T, some result)

/-- The fixed caller template is halted; actual lengths enter through `initial`. -/
@[expose] def caller : QueryMachine CallerState where
  init := (0, 0, some false)
  query _ := 0
  next := Prod.fst
  emit _ := []
  halted := fun state => !pending state
  finish := fun (_, _, result) => result.toList

/-- The fixed machine does not capture any runtime time bound. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) :=
  caller.withCalls (ScheduleSearch.machine M e) request resume

/-- Returned decision, absent while a schedule search is suspended. -/
@[expose] def answer : State k Q → Option Bool :=
  Sum.elim (fun (_, _, result) => result) (fun _ => none)

/-- Explicit binary caller framing. -/
@[expose] noncomputable def encCaller : CallerState ↪ List Bool :=
  encPair encNat (encPair encNat (encOption encBool))

variable [Finite Q]

/-- The caller and the single active search are charged separately. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum encCaller (encPair encCaller (ScheduleSearch.encState (k := k) (Q := Q)))

/-- Native positive starting guess from the measured input length. -/
theorem initial_inSpace : ComputableInSpace (initial (k := k) (Q := Q)) encNat encState
    (fun N => (encNat N).length) := by
  have hid : ComputableInSpace (fun N : ℕ => N) encNat encNat
      (fun N => (encNat N).length) := of_inO ComputableInDegree.id'.inO_one
  have hc := budget_prod hid (budget_prod (budget_natSucc hid)
    (budget_const (encB := encOption encBool) none (.refl _)))
  exact (budget_comp_linear (of_inO (ComputableInO.inl encCaller
    (encPair encCaller (ScheduleSearch.encState (k := k) (Q := Q))))) hc).of_enc_eq
      fun _ => rfl

/-- Native balanced arguments are computed from the actual binary guess. -/
theorem parameters_inSpace : ComputableInSpace parameters encCaller ScheduleSearch.encArgs
    (fun a => (encCaller a).length) := by
  have hN := fst encNat (encPair encNat (encOption encBool))
  have hT := (snd encNat (encPair encNat (encOption encBool))).fst'
  exact (budget_prod hN (budget_prod
    (budget_comp_linear BalancedParameters.blockWidth_inSpace hT)
    (budget_comp_linear BalancedParameters.horizon_inSpace hT))).of_enc_eq fun _ => rfl

/-- Native stopping guard depends only on the returned Boolean option. -/
theorem pending_inSpace : ComputableInSpace pending encCaller encBool
    (fun a => (encCaller a).length) :=
  budget_finite (fun result : Option Bool => !result.isSome)
    (snd encNat (encPair encNat (encOption encBool))).snd'

/-- One schedule-search request stores its actual runtime arguments. -/
theorem request_inSpace : ComputableInSpace (request (k := k) (Q := Q)) encCaller
    (encOption ScheduleSearch.encState) (fun a => (encCaller a).length) := by
  have hstart := budget_comp_linear (ScheduleSearch.initial_inSpace (k := k) (Q := Q))
    parameters_inSpace
  have hsome := budget_comp_linear
    (encC := encOption (ScheduleSearch.encState (k := k) (Q := Q)))
    (of_inO (ComputableInDegree.optionSome
      (enc₁ := ScheduleSearch.encState (k := k) (Q := Q))).inO_one) hstart
  exact budget_ite pending_inSpace hsome
    (budget_const (encB := encOption ScheduleSearch.encState) none (.refl _))

/-- Native return handling charges the saved caller and the actual returned search state. -/
theorem resume_inSpace : ComputableInSpace
    (fun a : CallerState × ScheduleSearch.State k Q => resume a.1 a.2)
    (encPair encCaller ScheduleSearch.encState) encCaller
    (fun a => (encPair encCaller ScheduleSearch.encState a).length) := by
  have hc := fst encCaller (ScheduleSearch.encState (k := k) (Q := Q))
  have ht := snd encCaller (ScheduleSearch.encState (k := k) (Q := Q))
  have hN := hc.fst'
  have hT := hc.snd'.fst'
  have hout := budget_comp_linear ScheduleSearch.answer_inSpace ht
  have hisSome := budget_finite (encC := encBool) (Option.isSome : Option Bool → Bool) hout
  have hT' := budget_ite hisSome hT (budget_natSucc hT)
  refine (budget_prod hN (budget_prod hT' hout)).of_enc_eq ?_
  rintro ⟨⟨N, T, result⟩, returned⟩
  cases ho : ScheduleSearch.answer returned <;> simp [resume, ho, encCaller, encPair_apply]

private theorem caller_query_inSpace : ComputableInSpace caller.query encCaller encNat
    (fun a => (encCaller a).length) := budget_const 0 (.refl _)
private theorem caller_next_inSpace : ComputableInSpace caller.next
    (encPair encCaller (encOption encBool)) encCaller
    (fun a => (encPair encCaller (encOption encBool) a).length) := fst _ _
private theorem caller_emit_inSpace : ComputableInSpace caller.emit
    (encPair encCaller (encOption encBool)) encBits
    (fun a => (encPair encCaller (encOption encBool) a).length) := budget_const [] (.refl _)
private theorem caller_halted_inSpace : ComputableInSpace caller.halted encCaller encBool
    (fun a => (encCaller a).length) := budget_finite Bool.not pending_inSpace
private theorem caller_finish_inSpace : ComputableInSpace caller.finish encCaller encBits
    (fun a => (encCaller a).length) :=
  (budget_comp_linear (g := Option.toList (α := Bool))
    (of_inO ComputableInDegree.optionBoolToList.inO_one)
    (snd encNat (encPair encNat (encOption encBool))).snd').of_enc_eq fun _ => rfl

/-- Native queries of the outer caller and its active schedule search. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  QueryMachine.withCalls_query_inSpace caller (ScheduleSearch.machine M e) request resume
    encCaller ScheduleSearch.encState caller_query_inSpace
    (ScheduleSearch.machine_query_inSpace M e) request_inSpace

/-- Native transitions include entry, return and all schedule-search clocks. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_next_inSpace caller (ScheduleSearch.machine M e) request resume
    encCaller ScheduleSearch.encState caller_next_inSpace
    (ScheduleSearch.machine_next_inSpace M e) (ScheduleSearch.machine_halted_inSpace M e)
    request_inSpace resume_inSpace

/-- Only the eventual final Boolean is output. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_emit_inSpace caller (ScheduleSearch.machine M e) request resume
    encCaller ScheduleSearch.encState caller_emit_inSpace request_inSpace

/-- Either Boolean decision ends the outer search. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  QueryMachine.withCalls_halted_inSpace caller (ScheduleSearch.machine M e) request resume
    encCaller ScheduleSearch.encState caller_halted_inSpace

/-- The final output is the singleton list containing the returned Boolean. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  QueryMachine.withCalls_finish_inSpace caller (ScheduleSearch.machine M e) request resume
    encCaller ScheduleSearch.encState caller_finish_inSpace

end Turing.MultiTapePTM.BlockComputation.OuterSearch
