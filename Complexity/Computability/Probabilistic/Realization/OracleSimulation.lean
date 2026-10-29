/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Computability.Probabilistic.Realization.OpenOracleSimulation
import Complexity.Languages.Probabilistic.Simulation

/-!
# A certified stateful oracle interpreter

The interpreter retains finite machine storage and the handler's state in one encoded value.
A local step uses the original transition table and a certified closed handler. Each certificate
charges captured input, requests, replies, state and retained configuration storage. The
certificates specialize those of the open interpreter `Cslib.Probability.OpenOracleSimulation`
to a sampled closed handler without external channels.

## Main definitions

* `Cslib.Probability.OracleSimulation.step`: a native step with explicit handler state.

## Main results

* `Cslib.Probability.OracleSimulation.isPPTOn_step`: the single-step PPT certificate.
* `Cslib.Probability.OracleSimulation.step_eq_run_interpret`: the exact stateful step law.
* `Cslib.Probability.OracleSimulation.sample_step`: a sampled step is an open step.
* `Cslib.Probability.OracleSimulation.isPPTOn_run`: a bounded run with a state invariant is PPT.

## References

Adapts Computability/Probabilistic/Realization/OracleSimulation.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared interpreter and tidy calculus.
-/

@[expose] public section

namespace Cslib.Probability.OracleSimulation
open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
variable {k : ℕ} {Control Operation α State : Type} [DecidableEq Operation]

/-- Execute one native step, retaining all machine storage and the handler's state. -/
noncomputable def step (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → ProbComp (List Bool × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    ProbComp (FiniteConfig k Bool Control Operation × State) :=
  match pair.1.tapes.state with
  | none => pure pair
  | some control => do
    let coin ← ProbComp.uniform Bool
    match machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin with
    | .step action symbol move => pure (pair.1.step action symbol move, pair.2)
    | .query channel next => do
      let (answer, state) ← handler a (channel, (pair.1.channels channel).1) pair.2
      return (pair.1.receive channel next answer, state)

/-- One interpreted step retains the full finite configuration and final handler state. -/
theorem step_eq_run_interpret (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → ProbComp (List Bool × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    step machine handler a pair =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (handler a))
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) pair.1)).run pair.2 := by
  cases hstate : pair.1.tapes.state with
  | none => simp [step, MultiTapeMachine.finiteStep, hstate]
  | some control =>
    simp only [step, MultiTapeMachine.finiteStep, hstate, bind_pure_comp,
      OracleComp.interpret_bind, StateT.run_bind,
      ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
      bind_map_left]
    congr 1
    funext coin
    cases machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin <;>
      simp only [OracleComp.interpret_map, OracleComp.interpret_pure,
        ProbOracleComp.interpret_query, StateT.run_map, StateT.run_pure]
    rfl

/-- A sampled step is the open interpreter's step with the sampled handler. -/
theorem sample_step {External : Type} (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → ProbComp (List Bool × State)) (a : α)
    (pair : FiniteConfig k Bool Control Operation × State) :
    ProbOracleComp.sample (spec := fun _ : External × List Bool => List Bool)
        (step machine handler a pair) =
      OpenOracleSimulation.step machine
        (fun a request state => ProbOracleComp.sample (handler a request state)) a pair := by
  rw [step_eq_run_interpret, OpenOracleSimulation.step_eq_run_interpret,
    ProbOracleComp.sample_run_interpret]

variable [Finite Control]

/-- A certified stateful handler makes one complete interpreter step PPT. -/
theorem isPPTOn_step [Fintype Operation] {input : α ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Operation)
    {handler : α → Operation × List Bool → State → ProbComp (List Bool × State)}
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2)) :
    IsPPTOn (encPair input (encPair encFiniteConfig stateEncoding))
      (encPair encFiniteConfig stateEncoding)
      (fun pair => step machine handler pair.1 pair.2) :=
  ((OpenOracleSimulation.isOraclePPTOn_step (External := Empty)
    (handler := fun a request state => ProbOracleComp.sample (handler a request state)) machine
    hhandler.isOraclePPTOn).congr fun pair _ _ _ => by rw [sample_step]).isPPTOn

/-- A bounded native run with a stateful PPT handler is PPT. A local invariant bounds reply
length and private-state growth; the loop certificate charges all interpreter storage. -/
theorem isPPTOn_run [Finite Operation] {input : α ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool}
    {stateEncoding : State ↪ List Bool} (machine : MultiTapePTM k Bool Control Operation)
    {word : α → List Bool} {count : α → ℕ}
    {handler : α → Operation × List Bool → State → ProbComp (List Bool × State)}
    {initial : α → State} (hword : ComputableInPolyTime word input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hhandler : IsPPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : α → State → Prop) (hinit : ∀ a, invariant a (initial a))
    {resources : ℕ → ℕ} (hresources : PolynomiallyBounded resources)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ (ProbComp.eval (handler a request state)).support,
        invariant a result.2 ∧
        result.1.length ≤ resources ((input a).length + request.2.length) ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length +
          resources ((input a).length + request.2.length)) :
    IsPPTOn input (encPair encBits stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifFin n))
          (handler a)) (machine.runOracle (count a) (word a))).run (initial a)) := by
  refine ((OpenOracleSimulation.isOraclePPTOn_run (External := Empty)
    (handler := fun a request state => ProbOracleComp.sample (handler a request state)) machine
    hword hcount hhandler.isOraclePPTOn hinitial invariant hinit hresources
    fun a request state hstate result hresult => hpreserve a request state hstate result
      ((ProbOracleComp.support_sample _).subset hresult)).congr fun a _ _ _ => ?_).isPPTOn
  rw [ProbOracleComp.sample_run_interpret]

end Cslib.Probability.OracleSimulation
