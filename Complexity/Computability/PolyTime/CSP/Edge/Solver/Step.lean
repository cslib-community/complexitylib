/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Program
import Complexity.Computability.PolyTime.CSP.Edge.Solver.AncestryPolyTime
import Complexity.Computability.PolyTime.CSP.Edge.Solver.LiftingPolyTime
import Complexity.Computability.PolyTime.CSP.Edge.Solver.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native machine certificate for one solver stack step

Compile the existing finite stack operation to the native machine calculus. The intermediate
case-analysis expression is proved equal on every raw state; no model, width or runtime
certificate is supplied as an input. This representation bookkeeping is original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode encWalkCode)
open EdgeForest (MeetingCode encMeetingCode)

private theorem poly_parent : ComputableInPolyTime Frame.parent encFrame EdgeForest.encInput :=
  encFrame_parent_deg.computableInPolyTime
private theorem poly_cycle : ComputableInPolyTime Frame.cycle encFrame encWalkCode :=
  encFrame_cycle_deg.computableInPolyTime
private theorem poly_inputMk : ComputableInPolyTime
    (fun p : CSP Table ℕ × List Bool => EdgeForest.Input.mk p.1 p.2)
    EdgeForest.encInputFields EdgeForest.encInput := EdgeForest.encInput_mk_deg.computableInPolyTime
private theorem poly_frameMk : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode => Frame.mk p.1 p.2) encFrameFields encFrame :=
  encFrame_mk_deg.computableInPolyTime
private theorem poly_prepare : ComputableInPolyTime NativeForest.BlossomCode.prepare
    NativeForest.encBlossomCode encWalkCode :=
  NativeForest.encBlossomCode_prepare_deg.computableInPolyTime
private theorem poly_blossomCycle : ComputableInPolyTime NativeForest.BlossomCode.cycle
    NativeForest.encBlossomCode encWalkCode :=
  NativeForest.encBlossomCode_cycle_deg.computableInPolyTime
private theorem poly_flatten : ComputableInPolyTime (List.flatten (α := Bool))
    (encList (encList encBool)) (encList encBool) :=
  .of_tidy (ComputableTidilyInPolyTime.flatten encBool)

attribute [local fun_prop] EdgeForest.poly_body EdgeForest.poly_labels poly_parent poly_cycle
  poly_inputMk poly_frameMk
  poly_prepare poly_blossomCycle poly_flatten NativeWalk.computableInPolyTime_flipWith
  NativeWalk.computableInPolyTime_edgesWith NativeWalk.computableInPolyTime_internalWith
  Contraction.computableInPolyTime_contractWith Contraction.computableInPolyTime_referenceRowsWith

/-- Complete original input is framed, followed by the native meeting code. -/
abbrev encEventArgs := encPair EdgeForest.encInput encMeetingCode

/-- Native preparation, honest whole-instance contraction and reference construction, on every
raw meeting and finite buffer. No hidden contraction or preparation provider is assumed. -/
theorem computableInPolyTime_push : ComputableInPolyTime
    (fun p : EdgeForest.Input × MeetingCode => push p.1 p.2)
    encEventArgs (encOption (encPair encFrame EdgeForest.encInput)) := by
  unfold push
  have hb := NativeForest.computableInPolyTime_blossom.comp
    (show ComputableInPolyTime (fun p : EdgeForest.Input × MeetingCode => (p.1.body, p.2))
      encEventArgs NativeForest.encMeetingArgs from by fun_prop)
  apply ComputableInPolyTime.optionMapWithInput hb
  fun_prop

/-- Native construction and flip of the actual chronological augmenting walk. -/
theorem computableInPolyTime_augment : ComputableInPolyTime
    (fun p : EdgeForest.Input × MeetingCode => augment p.1 p.2)
    encEventArgs (encOption (encList encBool)) := by
  unfold augment
  simp only [Option.pure_def]
  have hw := NativeForest.computableInPolyTime_meetingWalk.comp
    (show ComputableInPolyTime (fun p : EdgeForest.Input × MeetingCode => (p.1.body, p.2))
      encEventArgs NativeForest.encMeetingArgs from by fun_prop)
  fun_prop

/-- Native arbitrary-comparison lifting from a stored prepared parent frame. -/
theorem computableInPolyTime_lift : ComputableInPolyTime
    (fun p : Frame × List Bool => lift p.1 p.2)
    (encPair encFrame (encList encBool)) (encOption (encList encBool)) := by
  unfold lift
  simpa only [Function.comp_def] using NativeLifting.computableInPolyTime_liftComparison.comp
    (show ComputableInPolyTime
      (fun p : Frame × List Bool => (p.1.parent, p.1.cycle, p.2))
      (encPair encFrame (encList encBool)) NativeLifting.encComparisonArgs from by fun_prop)

private theorem poly_pushWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {event : α → MeetingCode}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (he : ComputableInPolyTime event e encMeetingCode) :
    ComputableInPolyTime (fun a => push (input a) (event a)) e
      (encOption (encPair encFrame EdgeForest.encInput)) := by
  simpa only [Function.comp_def] using computableInPolyTime_push.comp (hi.prod he)
private theorem poly_augmentWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {event : α → MeetingCode}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (he : ComputableInPolyTime event e encMeetingCode) :
    ComputableInPolyTime (fun a => augment (input a) (event a)) e
      (encOption (encList encBool)) := by
  simpa only [Function.comp_def] using computableInPolyTime_augment.comp (hi.prod he)
private theorem poly_liftWith {α : Type} {e : α ↪ List Bool}
    {frame : α → Frame} {bits : α → List Bool}
    (hf : ComputableInPolyTime frame e encFrame)
    (hb : ComputableInPolyTime bits e (encList encBool)) :
    ComputableInPolyTime (fun a => lift (frame a) (bits a)) e (encOption (encList encBool)) := by
  simpa only [Function.comp_def] using computableInPolyTime_lift.comp (hf.prod hb)

private theorem poly_current : ComputableInPolyTime State.current encState EdgeForest.encInput :=
  encState_current_deg.computableInPolyTime
private theorem poly_frames : ComputableInPolyTime State.frames encState (encList encFrame) :=
  encState_frames_deg.computableInPolyTime
private theorem poly_budget : ComputableInPolyTime State.budget encState encUnary :=
  encState_budget_deg.computableInPolyTime
private theorem poly_status : ComputableInPolyTime State.status encState
    (encOption (encOption (encList encBool))) := encState_status_deg.computableInPolyTime
private theorem poly_stateMk : ComputableInPolyTime
    (fun p : EdgeForest.Input × List Frame × ℕ × Option (Option (List Bool)) =>
      State.mk p.1 p.2.1 p.2.2.1 p.2.2.2) encStateFields encState :=
  encState_mk_deg.computableInPolyTime

private def stopped (state : State) (budget : ℕ) : State :=
  ⟨state.current, [], budget, some none⟩
private def emptyState : State := ⟨⟨[], []⟩, [], 0, some none⟩

private theorem poly_sumState {α β γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {value : γ → α ⊕ β} {left : γ → α → State} {right : γ → β → State}
    (hv : ComputableInPolyTime value eg (encSum ea eb))
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) encState)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) encState) :
    ComputableInPolyTime (fun a => (value a).elim (left a) (right a)) eg encState :=
  NativeCases.sumElimWithInput emptyState hv hl hr

attribute [local fun_prop] poly_current poly_frames poly_budget poly_status poly_stateMk
  poly_pushWith poly_augmentWith poly_liftWith poly_sumState

private def eventStep (state : State) (result : EdgeForest.ResultCode) : State :=
  result.elim (fun _ => stopped state (state.budget - 1)) fun event =>
    event.elim
      (fun meeting => ⟨state.current, state.frames, state.budget - 1,
        some (augment state.current meeting)⟩)
      (fun meeting => (push state.current meeting).elim (stopped state (state.budget - 1))
        fun (frame, child) => ⟨child, frame :: state.frames, state.budget - 1, none⟩)

private theorem poly_eventStep : ComputableInPolyTime
    (fun p : State × EdgeForest.ResultCode => eventStep p.1 p.2)
    (encPair encState EdgeForest.encResultCode) encState := by
  unfold eventStep stopped
  fun_prop

private theorem poly_eventWith {α : Type} {e : α ↪ List Bool}
    {state : α → State} {result : α → EdgeForest.ResultCode}
    (hs : ComputableInPolyTime state e encState)
    (hr : ComputableInPolyTime result e EdgeForest.encResultCode) :
    ComputableInPolyTime (fun a => eventStep (state a) (result a)) e encState := by
  simpa only [Function.comp_def] using poly_eventStep.comp (hs.prod hr)
attribute [local fun_prop] poly_eventWith

private def next (state : State) : State :=
  state.status.elim
    (if state.budget = 0 then stopped state 0 else
      (EdgeForest.run state.current).elim (stopped state (state.budget - 1)) (eventStep state))
    (fun result => result.elim (stopped state state.budget) fun bits =>
      state.frames.head?.elim state fun frame =>
        ⟨frame.parent, state.frames.tail, state.budget, some (lift frame bits)⟩)

private theorem poly_next : ComputableInPolyTime next encState encState := by
  have hrun : ComputableInPolyTime
      (fun state : State =>
        if state.budget = 0 then stopped state 0 else
          (EdgeForest.run state.current).elim
            (stopped state (state.budget - 1)) (eventStep state)) encState encState := by
    unfold stopped
    fun_prop
  unfold next
  apply ComputableInPolyTime.optionElimWithInput poly_status hrun
  apply ComputableInPolyTime.optionElimWithInput
    (ComputableInPolyTime.snd encState (encOption (encList encBool)))
    (show ComputableInPolyTime
      (fun p : State × Option (List Bool) => stopped p.1 p.1.budget)
      (encPair encState (encOption (encList encBool))) encState from by
        unfold stopped; fun_prop)
  apply ComputableInPolyTime.optionElimWithInput
    (show ComputableInPolyTime
      (fun p : (State × Option (List Bool)) × List Bool => p.1.1.frames.head?)
      (encPair (encPair encState (encOption (encList encBool))) (encList encBool))
      (encOption encFrame) from by fun_prop)
    (by fun_prop)
  fun_prop

private theorem next_eq (state : State) : next state = step state := by
  rcases state with ⟨input, frames, budget, status⟩
  cases status with
  | some result => cases result <;> cases frames <;> rfl
  | none =>
    cases budget with
    | zero => rfl
    | succ budget =>
      simp only [next, Option.elim_none, Nat.add_one_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel_right]
      cases hr : EdgeForest.run input with
      | none => simp [step, hr, stopped]
      | some result =>
        rcases result with log | (event | event)
        · simp [step, hr, eventStep, stopped]
        · simp [step, hr, eventStep]
        · cases hp : push input event <;> simp [step, hr, eventStep, stopped, hp]

/-- One complete finite stack step is ordinary native polynomial-time on every encoded state,
including malformed widths, huge binary names, arbitrary stacks and invalid meeting buffers. -/
theorem computableInPolyTime_step : ComputableInPolyTime step encState encState := by
  apply poly_next.of_enc_eq
  intro state
  rw [next_eq]

end Cslib.Complexity.CSP.EdgeSolver.Program
