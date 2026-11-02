/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteSupplier
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerQuery

/-!
# A fixed native evaluator with concrete same-input suppliers

The uniform raw evaluator calls the concrete node and gate-vector suppliers on its original
read-only input. Its fixed template contains only zero metadata and empty storage. Actual runtime
parameters and an actual register bank are supplied through `runFrom`; computing that initial
bank remains a separate obligation. No input word, tree or supplier oracle is captured by the
machine definition. All five native components reuse the existing raw-controller calculus.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ConcreteEvaluator

open MultiTapeTM Cslib.TreeEval.Ary.Packed
open QueryReplay

variable {k s : ℕ} {Q : Type}

/-- An active raw evaluator or one suspended evaluator paired with its concrete supplier. -/
abbrev State (k : ℕ) (Q : Type) :=
  RawController.Query.Context ConcreteSupplier.Context ⊕
    (RawController.Query.Context ConcreteSupplier.Context × GateReply.State k Q)

/-- A fixed empty halted template, independent of runtime inputs and evaluator parameters. -/
@[expose] def template : RawController.Query.Context ConcreteSupplier.Context :=
  ((0, 0, 0, 0, 0, 0, 0), (0, 0, 0), [], [], none)

/-- The raw evaluator with concrete node and gate-vector calls on the same original input. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) :=
  RawController.Query.machine template (GateReply.machine M e)
    (ConcreteSupplier.start M e) GateReply.answer

variable [Finite Q]

/-- Reuse the raw caller/callee encoding, charging every stored bank, stack and supplier state. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  RawController.Query.encMachineState ConcreteSupplier.encContext
    (GateReply.encState (k := k) (Q := Q))

/-- Native queries use only the current actual caller or concrete supplier state. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  RawController.Query.machine_query_inSpace ConcreteSupplier.encContext GateReply.encState
    template (GateReply.machine M e) (ConcreteSupplier.start M e) GateReply.answer
    (GateReply.machine_query_inSpace M e) (ConcreteSupplier.start_inSpace M e)

/-- Native transitions charge request initialization and extraction of the actual reply. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
  RawController.Query.machine_next_inSpace ConcreteSupplier.encContext GateReply.encState
    template (GateReply.machine M e) (ConcreteSupplier.start M e) GateReply.answer
    (GateReply.machine_next_inSpace M e) (GateReply.machine_halted_inSpace M e)
    (ConcreteSupplier.start_inSpace M e) GateReply.answer_inSpace

/-- Evaluation returns its state and emits no intermediate word. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  RawController.Query.machine_emit_inSpace ConcreteSupplier.encContext GateReply.encState
    template (GateReply.machine M e) (ConcreteSupplier.start M e) GateReply.answer
    (ConcreteSupplier.start_inSpace M e)

/-- The existing native raw-controller guard determines completion. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  RawController.Query.machine_halted_inSpace ConcreteSupplier.encContext GateReply.encState
    template (GateReply.machine M e) (ConcreteSupplier.start M e) GateReply.answer

/-- The final bank remains in the actual returned state, rather than an output stream. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  RawController.Query.machine_finish_inSpace ConcreteSupplier.encContext GateReply.encState
    template (GateReply.machine M e) (ConcreteSupplier.start M e) GateReply.answer

end Turing.MultiTapePTM.BlockComputation.ConcreteEvaluator
