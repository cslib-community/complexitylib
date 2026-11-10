/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearchParameters

/-!
# Increasing time guesses on the original input

The outer caller stores the input length, a binary time guess and an optional final decision.
Each guess runs the complete schedule search with the block width and horizon that its
`Parameters` select. An undecided search increments the guess; either Boolean decision stops.
Only the final Boolean is emitted. No time bound or time-constructibility witness is consulted
by the machine.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable (E : ScheduleSearch.Evaluator)

/-- Original input length, current time guess and a returned decision. -/
abbrev CallerState := ℕ × ℕ × Option Bool
/-- One outer caller or one suspended caller with its schedule-search state. -/
abbrev State := CallerState ⊕ (CallerState × ScheduleSearch.State E)

/-- Begin with a positive guess at least the input length. -/
@[expose] def initial (N : ℕ) : State E := .inl (N, N + 1, none)

/-- Actual runtime arguments for the current guess. -/
@[expose] def parameters (P : Parameters) : CallerState → ScheduleSearch.Args :=
  fun (N, T, _) => (N, P.blockWidth T, P.horizon T)

/-- Both accepting and rejecting returned decisions stop the caller. -/
@[expose] def pending : CallerState → Bool := fun (_, _, result) => !result.isSome

/-- Start exactly one native schedule search on the original input. -/
@[expose] def request (P : Parameters) : CallerState → Option (ScheduleSearch.State E) :=
  fun state => if pending state then some (ScheduleSearch.initial E (parameters P state)) else none

/-- A live result advances the guess; a decision, including false, is retained. -/
@[expose] def resume : CallerState → ScheduleSearch.State E → CallerState :=
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
@[expose] def machine (k : ℕ) (P : Parameters) : QueryMachine (State E) :=
  caller.withCalls (ScheduleSearch.machine E k) (request E P) (resume E)

variable {E} in
/-- Returned decision, absent while a schedule search is suspended. -/
@[expose] def answer : State E → Option Bool :=
  Sum.elim (fun (_, _, result) => result) (fun _ => none)

/-- Explicit binary caller framing. -/
@[expose] noncomputable def encCaller : CallerState ↪ List Bool :=
  encPair encNat (encPair encNat (encOption encBool))

/-- The caller and the single active search are charged separately. -/
@[expose] noncomputable def encState : State E ↪ List Bool :=
  encSum encCaller (encPair encCaller (ScheduleSearch.encState E))

/-- Native positive starting guess from the measured input length. -/
theorem initial_inSpace : ComputableInSpace (initial E) encNat (encState E)
    (fun N => (encNat N).length) := by
  have hid : ComputableInSpace (fun N : ℕ => N) encNat encNat
      (fun N => (encNat N).length) := of_inO ComputableInDegree.id'.inO_one
  have hc := budget_prod hid (budget_prod (budget_natSucc hid)
    (budget_const (encB := encOption encBool) none (.refl _)))
  exact (budget_comp_linear (of_inO (ComputableInO.inl encCaller
    (encPair encCaller (ScheduleSearch.encState E)))) hc).of_enc_eq fun _ => rfl

/-- Native block arguments are computed from the actual binary guess. -/
theorem parameters_inSpace (P : Parameters) : ComputableInSpace (parameters P) encCaller
    ScheduleSearch.encArgs (fun a => (encCaller a).length) := by
  have hN := fst encNat (encPair encNat (encOption encBool))
  have hT := (snd encNat (encPair encNat (encOption encBool))).fst'
  exact (budget_prod hN (budget_prod
    (budget_comp_linear P.blockWidth_inSpace hT)
    (budget_comp_linear P.horizon_inSpace hT))).of_enc_eq fun _ => rfl

/-- Native stopping guard depends only on the returned Boolean option. -/
theorem pending_inSpace : ComputableInSpace pending encCaller encBool
    (fun a => (encCaller a).length) :=
  budget_finite (fun result : Option Bool => !result.isSome)
    (snd encNat (encPair encNat (encOption encBool))).snd'

/-- One schedule-search request stores its actual runtime arguments. -/
theorem request_inSpace (P : Parameters) : ComputableInSpace (request E P) encCaller
    (encOption (ScheduleSearch.encState E)) (fun a => (encCaller a).length) := by
  have hstart := budget_comp_linear (ScheduleSearch.initial_inSpace E) (parameters_inSpace P)
  have hsome := budget_comp_linear (encC := encOption (ScheduleSearch.encState E))
    (of_inO (ComputableInDegree.optionSome (enc₁ := ScheduleSearch.encState E)).inO_one) hstart
  exact budget_ite pending_inSpace hsome
    (budget_const (encB := encOption (ScheduleSearch.encState E)) none (.refl _))

/-- Native return handling charges the saved caller and the actual returned search state. -/
theorem resume_inSpace : ComputableInSpace
    (fun a : CallerState × ScheduleSearch.State E => resume E a.1 a.2)
    (encPair encCaller (ScheduleSearch.encState E)) encCaller
    (fun a => (encPair encCaller (ScheduleSearch.encState E) a).length) := by
  have hc := fst encCaller (ScheduleSearch.encState E)
  have ht := snd encCaller (ScheduleSearch.encState E)
  have hN := hc.fst'
  have hT := hc.snd'.fst'
  have hout := budget_comp_linear (ScheduleSearch.answer_inSpace E) ht
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
theorem machine_query_inSpace (k : ℕ) (P : Parameters) : ComputableInSpace
    (machine E k P).query (encState E) encNat (fun a => (encState E a).length) :=
  QueryMachine.withCalls_query_inSpace caller (ScheduleSearch.machine E k) (request E P)
    (resume E) encCaller (ScheduleSearch.encState E) caller_query_inSpace
    (ScheduleSearch.machine_query_inSpace E k) (request_inSpace E P)

/-- Native transitions include entry, return and all schedule-search clocks. -/
theorem machine_next_inSpace (k : ℕ) (P : Parameters) : ComputableInSpace (machine E k P).next
    (encPair (encState E) (encOption encBool)) (encState E)
    (fun a => (encPair (encState E) (encOption encBool) a).length) :=
  QueryMachine.withCalls_next_inSpace caller (ScheduleSearch.machine E k) (request E P)
    (resume E) encCaller (ScheduleSearch.encState E) caller_next_inSpace
    (ScheduleSearch.machine_next_inSpace E k) (ScheduleSearch.machine_halted_inSpace E k)
    (request_inSpace E P) (resume_inSpace E)

/-- Only the eventual final Boolean is output. -/
theorem machine_emit_inSpace (k : ℕ) (P : Parameters) : ComputableInSpace (machine E k P).emit
    (encPair (encState E) (encOption encBool)) encBits
    (fun a => (encPair (encState E) (encOption encBool) a).length) :=
  QueryMachine.withCalls_emit_inSpace caller (ScheduleSearch.machine E k) (request E P)
    (resume E) encCaller (ScheduleSearch.encState E) caller_emit_inSpace (request_inSpace E P)

/-- Either Boolean decision ends the outer search. -/
theorem machine_halted_inSpace (k : ℕ) (P : Parameters) : ComputableInSpace
    (machine E k P).halted (encState E) encBool (fun a => (encState E a).length) :=
  QueryMachine.withCalls_halted_inSpace caller (ScheduleSearch.machine E k) (request E P)
    (resume E) encCaller (ScheduleSearch.encState E) caller_halted_inSpace

/-- The final output is the singleton list containing the returned Boolean. -/
theorem machine_finish_inSpace (k : ℕ) (P : Parameters) : ComputableInSpace
    (machine E k P).finish (encState E) encBits (fun a => (encState E a).length) :=
  QueryMachine.withCalls_finish_inSpace caller (ScheduleSearch.machine E k) (request E P)
    (resume E) encCaller (ScheduleSearch.encState E) caller_finish_inSpace

end Turing.MultiTapePTM.BlockComputation.OuterSearch
