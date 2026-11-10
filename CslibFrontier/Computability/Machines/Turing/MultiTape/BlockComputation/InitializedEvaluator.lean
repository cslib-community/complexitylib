/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.Initializer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluator
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootDecision
public import CslibFrontier.Computability.TreeEval.Ary.Packed.RawControllerOutput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# A native evaluator with streamed runtime initialization

One fixed machine first builds the selected metadata and padded bank, then enters the concrete
evaluator on the same original read-only input. Actual binary arguments enter through `start`;
the fixed template contains neither runtime parameters nor an input word. Native component
certificates cover both phases and their handoff. This construction does not assert a complexity
class inclusion or initialize an outer schedule/time search.

`outcome` classifies the root of a returned bank, and `scheduleEvaluator` packages the machine
as the schedule-search evaluator of Williams's simulation.

## Main definitions

* `InitializedEvaluator.machine`: the fixed initialize-then-evaluate machine.
* `InitializedEvaluator.scheduleEvaluator`: the machine as a `ScheduleSearch.Evaluator`.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitializedEvaluator

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- A streamed initializer or the concrete evaluator with its actual bank and supplier state. -/
abbrev State (k : ℕ) (Q : Type) := Initializer.State ⊕ ConcreteEvaluator.State k Q

/-- Runtime arguments enter a fresh streamed initializer. -/
@[expose] def start (k s : ℕ) (args : Initializer.Args) : State k Q :=
  .inl (Initializer.prepare k s args)

/-- Enter the concrete evaluator using only the actual completed initializer state. -/
@[expose] def resume (k : ℕ) (state : Initializer.State) : ConcreteEvaluator.State k Q :=
  .inl (Initializer.result k state)

/-- Fixed same-input initialization followed by concrete evaluation. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := .inr (ConcreteEvaluator.machine M e).init
  query := Sum.elim (fun _ => 0) (ConcreteEvaluator.machine M e).query
  next := fun (state, symbol) => state.elim
    (fun initial => if (Initializer.machine k).halted initial then .inr (resume k initial)
      else .inl (Initializer.step k initial))
    (fun active => .inr ((ConcreteEvaluator.machine M e).next (active, symbol)))
  emit _ := []
  halted := Sum.elim (fun _ => false) (ConcreteEvaluator.machine M e).halted
  finish _ := []

variable [Finite Q]

/-- Each phase retains and charges its actual payload. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum Initializer.encState (ConcreteEvaluator.encState (k := k) (Q := Q))

/-- The handoff charges the actual selected header and constructed bank. -/
theorem resume_inSpace : ComputableInSpace (resume (k := k) (Q := Q)) Initializer.encState
    ConcreteEvaluator.encState (fun a => (Initializer.encState a).length) := by
  have hinl := of_inO (ComputableInO.inl
    (Cslib.TreeEval.Ary.Packed.RawController.Query.encContext ConcreteSupplier.encContext)
    (encPair
      (Cslib.TreeEval.Ary.Packed.RawController.Query.encContext ConcreteSupplier.encContext)
      (QueryReplay.GateReply.encState (k := k) (Q := Q))))
  exact (budget_comp_linear hinl (Initializer.result_inSpace k)).of_enc_eq fun _ => rfl

/-- Native entry computes selected metadata from actual binary arguments. -/
theorem start_inSpace : ComputableInSpace (start (Q := Q) k s)
    Initializer.encArgs encState (fun a => (Initializer.encArgs a).length) := by
  have hinl := of_inO (ComputableInO.inl Initializer.encState
    (ConcreteEvaluator.encState (k := k) (Q := Q)))
  exact (budget_comp_linear hinl (Initializer.prepare_inSpace k s)).of_enc_eq fun _ => rfl

/-- Initializer clocks need no input; evaluator clocks preserve the original-input queries. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := Initializer.encState) (encB := encNat) 0 (.refl _))
    (ConcreteEvaluator.machine_query_inSpace M e)

/-- Native transitions cover streamed growth, handoff and concrete evaluator execution. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hs := fst Initializer.encState (encOption encBool)
  have hinl := of_inO (ComputableInO.inl Initializer.encState
    (ConcreteEvaluator.encState (k := k) (Q := Q)))
  have hinr := of_inO (ComputableInO.inr Initializer.encState
    (ConcreteEvaluator.encState (k := k) (Q := Q)))
  have hrun := budget_comp_linear hinl (budget_comp_linear (Initializer.step_inSpace k) hs)
  have hresume := budget_comp_linear hinr (budget_comp_linear resume_inSpace hs)
  have hhalt := budget_comp_linear (Initializer.machine_halted_inSpace k) hs
  have hleft := budget_ite hhalt hresume hrun
  have hright := budget_comp_linear hinr (ConcreteEvaluator.machine_next_inSpace M e)
  exact sumElimFst hleft hright

/-- Both phases keep their result in state and emit no intermediate word. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  budget_const [] (.refl _)

/-- Initialization remains live until handoff; concrete evaluation decides final completion. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := Initializer.encState) (encB := encBool) false (.refl _))
    (ConcreteEvaluator.machine_halted_inSpace M e)

/-- The final bank is read from the actual returned state. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  budget_const [] (.refl _)

omit [Finite Q] in
/-- Decode only returned active evaluator banks; incomplete or suspended states give no decision. -/
@[expose] def outcome (e : Q ≃ Fin s) : ScheduleSearch.Args × State k Q → Option Bool
  | ((_, b, _), .inr (.inl ((_, _, _, _, m, _, _), (p, _, r), bank, _, _))) =>
    RootDecision.classify k e (b, Cslib.TreeEval.Ary.Packed.RawController.Output.decode
      ((Encoding.width k s b, m, p, r, 0), bank))
  | _ => none

open Cslib.TreeEval.Ary.Packed in
/-- Returned-bank extraction and header-only root classification are native. -/
theorem outcome_inSpace (e : Q ≃ Fin s) : ComputableInSpace (outcome (k := k) e)
    (encPair ScheduleSearch.encArgs encState) (encOption encBool)
    (fun a => (encPair ScheduleSearch.encArgs encState a).length) := by
  let encC := RawController.Query.encContext ConcreteSupplier.encContext
  have ha := fst ScheduleSearch.encArgs encC
  have hc := snd ScheduleSearch.encArgs encC
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
  have hsuspended := budget_const (encIn := encPair ScheduleSearch.encArgs
    (encPair encC (QueryReplay.GateReply.encState (k := k) (Q := Q))))
    (encB := encOption encBool) none (.refl _)
  have hinitial := budget_const (encIn := encPair ScheduleSearch.encArgs Initializer.encState)
    (encB := encOption encBool) none (.refl _)
  exact (sumElimSnd hinitial (sumElimSnd hroot hsuspended)).of_enc_eq fun a => by
    rcases a with ⟨args, initial | (active | suspended)⟩ <;> rfl

/-- The initialized concrete evaluator as a schedule-search evaluator: schedule `σ` enters
through `start`, and a returned bank's root is classified by `outcome`. -/
@[expose] noncomputable def scheduleEvaluator (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ScheduleSearch.Evaluator where
  State := State k Q
  encState := encState
  machine := machine M e
  start := start k s
  outcome := outcome e
  machine_query_inSpace := machine_query_inSpace M e
  machine_next_inSpace := machine_next_inSpace M e
  machine_halted_inSpace := machine_halted_inSpace M e
  start_inSpace := start_inSpace
  outcome_inSpace := outcome_inSpace e

end Turing.MultiTapePTM.BlockComputation.InitializedEvaluator
