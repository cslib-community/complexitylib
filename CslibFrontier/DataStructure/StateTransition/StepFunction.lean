/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition.Impl

/-!
# Backends given by a step function

Many concrete backends are a total function taking a concrete state and an operation to the next
state, the answer and a native trace (a cost count, say). This module states the execution
relation, the client runner and the semantic implementation of such a backend once, so that each
data structure supplies only its step function and its correctness proof.

## Main definitions

* `StepResult`: the next state, answer and trace of one step.
* `Execution.ofStep`: the execution relation of a step function.
* `RunResult`, `Execution.run`: the value, final state and per-operation traces of running an
  adaptive client with a step function.
* `StateTransitionImpl.ofStep`: a semantic implementation of a deterministic specification by a
  step function, from step correctness alone.

## Main results

* `Execution.executes_run`: the runner produces an `Executes` derivation.
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w x

variable {S : PFunctor.{v, w}} {C τ : Type x}

/-- The outcome of one step of a concrete backend: the next state, the answer and a native trace. -/
structure StepResult (C τ : Type x) (β : Type w) where
  /-- The concrete state after the step. -/
  state : C
  /-- The answer returned to the client. -/
  answer : β
  /-- The native trace of the step, such as its cost. -/
  trace : τ

/-- The outcome of running an adaptive client on a concrete backend: the client's value, the final
state and the native trace of each operation, in call order. -/
structure RunResult (C τ : Type x) (α : Type u) where
  /-- The value returned by the client. -/
  value : α
  /-- The concrete state after the last operation. -/
  state : C
  /-- The native traces of the operations, in call order. -/
  traces : List τ

namespace Execution

/-- The execution relation of a step function: `c` steps under `o` to `c'` with answer `a` and
trace `t` exactly when `step c o = ⟨c', a, t⟩`. -/
abbrev ofStep (step : C → (o : S.A) → StepResult C τ (S.B o)) : Execution S C τ :=
  fun c o a c' t => step c o = ⟨c', a, t⟩

/-- Run an adaptive client with a step function, recording the trace of each operation. -/
def run (step : C → (o : S.A) → StepResult C τ (S.B o)) {α : Type u} (c : C) :
    S.FreeM α → RunResult C τ α
  | .pure a => ⟨a, c, []⟩
  | .liftBind o k =>
      let r := step c o
      let rest := run step r.state (k r.answer)
      ⟨rest.value, rest.state, r.trace :: rest.traces⟩

/-- The runner of a step function produces a derivation of its execution relation. -/
theorem executes_run (step : C → (o : S.A) → StepResult C τ (S.B o)) {α : Type u}
    (p : S.FreeM α) (c : C) :
    Executes (ofStep step) p c (run step c p).value (run step c p).state
      (run step c p).traces := by
  induction p using PFunctor.FreeM.recOn generalizing c with
  | pure a => exact .pure a c
  | liftBind o k ih => exact .call rfl (ih _ _)

end Execution

namespace StateTransitionImpl

variable {D : StateTransitionSpec.{u, v, w}}
  {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

/-- A semantic implementation of a deterministic specification by a step function. Totality holds
because the step function is total, so only step correctness is required: from a represented
state, every admissible operation answers as `D.stepFn` and reaches a represented state. -/
abbrev ofStep (rep : D.State → C → Prop) (step : C → (o : D.Op) → StepResult C τ (D.Result o))
    (correct : ∀ {s c} o, rep s c → D.valid s o →
      (step c o).answer = (D.stepFn s o).2 ∧ rep (D.stepFn s o).1 (step c o).state) :
    StateTransitionImpl D (Execution.ofStep step) :=
  ofFn (rep := rep)
    (total := fun {_ c} o _ _ => ⟨(step c o).answer, (step c o).state, (step c o).trace, rfl⟩)
    (correct := fun {_ c o a c' t} hr hv he => by
      have he' : step c o = ⟨c', a, t⟩ := he
      have h := correct o hr hv
      rw [he'] at h
      exact h)

end StateTransitionImpl

end Cslib.DataStructure
