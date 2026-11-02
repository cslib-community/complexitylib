/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Initializer
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluator
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# A native evaluator with streamed runtime initialization

One fixed machine first builds the selected metadata and padded bank, then enters the concrete
evaluator on the same original read-only input. Actual binary arguments enter through `start`;
the fixed template contains neither runtime parameters nor an input word. Native component
certificates cover both phases and their handoff. This construction does not assert a complexity
class inclusion or initialize an outer schedule/time search.
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

end Turing.MultiTapePTM.BlockComputation.InitializedEvaluator
