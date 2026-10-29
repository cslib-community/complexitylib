/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.Linarith

/-!
# A certified open stateful oracle interpreter

The interpreter of `Cslib.Probability.OracleSimulation` retains finite machine storage and a
handler's private state in one encoded value. Here the handler may itself draw private coins and
call an external stateful oracle, so one interpreter step is an oracle program rather than a
closed one. A local step uses the original transition table and a handler certified as strict
oracle PPT. Each certificate charges captured input, requests, replies, the handler's state and
retained configuration storage, for every external oracle and every external reply length.

## Main definitions

* `Cslib.Probability.OpenOracleSimulation.step`: a native step with an open stateful handler.

## Main results

* `Cslib.Probability.OpenOracleSimulation.step_eq_run_interpret`: the exact stateful step law.
* `Cslib.Probability.OpenOracleSimulation.isOraclePPTOn_step`: the single-step certificate.
* `Cslib.Probability.OpenOracleSimulation.isOraclePPTOn_run`: a bounded run with a state
  invariant is strict oracle PPT.

## References

Adapts Computability/Probabilistic/Realization/OracleSimulation.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to handlers with external calls, using the
compositional strict oracle PPT calculus.
-/

@[expose] public section

namespace Cslib.Probability.OpenOracleSimulation

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM

variable {k : ℕ} {Control Operation External α State : Type} [DecidableEq Operation]

/-- Execute one native step, retaining all machine storage and the handler's state. A query is
answered by the handler, which may draw private coins and call the external oracle. -/
noncomputable def step (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → WordOracleComp External (List Bool × State))
    (a : α) (pair : FiniteConfig k Bool Control Operation × State) :
    WordOracleComp External (FiniteConfig k Bool Control Operation × State) :=
  match pair.1.tapes.state with
  | none => pure pair
  | some control => do
    let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
    match machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin with
    | .step action symbol move => pure (pair.1.step action symbol move, pair.2)
    | .query channel next => do
      let (answer, state) ← handler a (channel, (pair.1.channels channel).1) pair.2
      return (pair.1.receive channel next answer, state)

/-- One interpreted step retains the full finite configuration and the handler's final state.
The equality is one of oracle programs, so it holds for every later external oracle. -/
theorem step_eq_run_interpret (machine : MultiTapePTM k Bool Control Operation)
    (handler : α → Operation × List Bool → State → WordOracleComp External (List Bool × State))
    (a : α) (pair : FiniteConfig k Bool Control Operation × State) :
    step machine handler a pair =
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (machine.finiteStep
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) pair.1)).run pair.2 := by
  cases hstate : pair.1.tapes.state with
  | none => simp [step, MultiTapeMachine.finiteStep, hstate]
  | some control =>
    simp only [step, MultiTapeMachine.finiteStep, hstate, bind_pure_comp,
      OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_lift_sample,
      bind_map_left]
    congr 1
    funext coin
    cases machine.tr control pair.1.tapes.inputSymbol pair.1.tapes.workTapeSymbols
        pair.1.answerSymbols coin <;>
      simp only [OracleComp.interpret_map, OracleComp.interpret_pure,
        ProbOracleComp.interpret_query, StateT.run_map, StateT.run_pure]
    rfl

variable [Finite Control] [DecidableEq External] [Finite External]

/-- A handler certified as strict oracle PPT makes one complete interpreter step strict oracle
PPT. Only the selected transition runs, so a non-query step makes no external call. -/
theorem isOraclePPTOn_step [Fintype Operation] {input : α ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Operation)
    {handler : α → Operation × List Bool → State → WordOracleComp External (List Bool × State)}
    (hhandler : IsOraclePPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2)) :
    IsOraclePPTOn (encPair input (encPair encFiniteConfig stateEncoding))
      (encPair encFiniteConfig stateEncoding)
      (fun pair => step machine handler pair.1 pair.2) := by
  unfold step
  apply IsOraclePPTOn.finite_cases (tagEncoding := encFinite (Option Control))
    (branch := fun control (pair : α × (FiniteConfig k Bool Control Operation × State)) =>
      match control with
    | none => pure pair.2
    | some control => do
      let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
      match machine.tr control pair.2.1.tapes.inputSymbol pair.2.1.tapes.workTapeSymbols
          pair.2.1.answerSymbols coin with
      | .step action symbol move => pure (pair.2.1.step action symbol move, pair.2.2)
      | .query channel next => do
        let (answer, state) ← handler pair.1 (channel, (pair.2.1.channels channel).1) pair.2.2
        return (pair.2.1.receive channel next answer, state))
  · fun_prop
  · intro control
    cases control with
    | none => fun_prop
    | some control =>
      apply ((IsTidyOraclePPTOn.uniform_bool _).isOraclePPTOn).bind_with
      apply IsOraclePPTOn.finite_cases
        (tag := fun pair : (α × (FiniteConfig k Bool Control Operation × State)) × Bool =>
          (pair.1.2.1.tapes.inputSymbol, pair.1.2.1.tapes.workTapeSymbols,
            pair.1.2.1.answerSymbols, pair.2))
        (tagEncoding := encPair (encFinEnum (Option Bool))
          (encPair (encFinEnum (Fin k → Option Bool))
            (encPair (encFinite (Operation → Option Bool)) encBool)))
        (branch := fun symbols (pair : (α × (FiniteConfig k Bool Control Operation × State)) ×
            Bool) =>
          match machine.tr control symbols.1 symbols.2.1 symbols.2.2.1 symbols.2.2.2 with
          | .step action symbol move => pure (pair.1.2.1.step action symbol move, pair.1.2.2)
          | .query channel next => do
            let (answer, state) ←
              handler pair.1.1 (channel, (pair.1.2.1.channels channel).1) pair.1.2.2
            return (pair.1.2.1.receive channel next answer, state))
      · fun_prop
      · rintro ⟨inputSymbol, workSymbols, answerSymbols, coin⟩
        cases machine.tr control inputSymbol workSymbols answerSymbols coin with
        | step action symbol move => fun_prop
        | query channel next =>
          apply IsOraclePPTOn.bind_with (middle := encPair encBits stateEncoding)
          · fun_prop
          · fun_prop

/-- A bounded native run with an open stateful handler is strict oracle PPT. A local invariant,
over every possible handler result under every external oracle, bounds reply length and
private-state growth; the loop certificate charges all interpreter storage. -/
theorem isOraclePPTOn_run [Finite Operation] {input : α ↪ List Bool}
    {operationEncoding : Operation ↪ List Bool} {stateEncoding : State ↪ List Bool}
    (machine : MultiTapePTM k Bool Control Operation)
    {word : α → List Bool} {count : α → ℕ}
    {handler : α → Operation × List Bool → State → WordOracleComp External (List Bool × State)}
    {initial : α → State} (hword : ComputableInPolyTime word input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hhandler : IsOraclePPTOn
      (encPair input (encPair (encPair operationEncoding encBits) stateEncoding))
      (encPair encBits stateEncoding) (fun pair => handler pair.1 pair.2.1 pair.2.2))
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (invariant : α → State → Prop) (hinit : ∀ a, invariant a (initial a))
    {resources : ℕ → ℕ} (hresources : PolynomiallyBounded resources)
    (hpreserve : ∀ a request state, invariant a state →
      ∀ result ∈ OracleComp.support (handler a request state),
        invariant a result.2 ∧
        result.1.length ≤ resources ((input a).length + request.2.length) ∧
        (stateEncoding result.2).length ≤ (stateEncoding state).length +
          resources ((input a).length + request.2.length)) :
    IsOraclePPTOn input (encPair encBits stateEncoding) (fun a =>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n))) (handler a))
        (machine.runOracle (count a) (word a))).run (initial a)) := by
  have hword := hword.tidy
  have hcount := hcount.tidy
  have hinitial := hinitial.tidy
  let _ := Fintype.ofFinite Operation
  obtain ⟨cr, dr, hresourceSize⟩ := polynomiallyBounded_iff_le.mp hresources
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  let budget (a : α) := cr * ((input a).length + count a + 1) ^ dr
  let start (a : α) := (FiniteConfig.init (k := k) (Oracle := Operation)
    machine.initial (word a), initial a)
  let loopInvariant (a : α) (i : ℕ) (pair : FiniteConfig k Bool Control Operation × State) :=
    FiniteConfig.SpaceBound (word a).length i (budget a) pair.1 ∧
      invariant a pair.2 ∧ (stateEncoding pair.2).length ≤
        (stateEncoding (initial a)).length + i * budget a
  have hbudget (a : α) (word : List Bool) (hword : word.length ≤ count a) :
      resources ((input a).length + word.length) ≤ budget a :=
    (hresourceSize _).trans (Nat.mul_le_mul_left cr (Nat.pow_le_pow_left
      (by lia) dr))
  have hstart : ComputableTidilyInPolyTime start input (encPair encFiniteConfig stateEncoding) := by
    dsimp only [start]
    fun_prop
  have hloop := (IsOraclePPTOn.iterateWith_spec hcount hstart (isOraclePPTOn_step machine hhandler)
    loopInvariant (fun a => ⟨FiniteConfig.spaceBound_init _ _ _, hinit a, by simp [start]⟩)
    (by
      rintro a i ⟨cfg, state⟩ hi ⟨hcfg, hs, hsize⟩ next hnext
      cases hcontrol : cfg.tapes.state with
      | none =>
        simp only [step, hcontrol] at hnext
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hnext
        exact ⟨hcfg.mono le_rfl (Nat.le_succ i) le_rfl, hs, by
          dsimp only at hsize ⊢
          nlinarith⟩
      | some control =>
        simp only [step, hcontrol] at hnext
        obtain ⟨coin, _, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
        cases haction : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols coin with
        | step action symbol move =>
          simp only [haction] at hnext
          obtain rfl := OracleComp.eq_of_mem_supportWith_pure hnext
          exact ⟨hcfg.step action symbol move, hs, by dsimp only at hsize ⊢; nlinarith⟩
        | query channel control =>
          simp only [haction] at hnext
          obtain ⟨⟨answer, state'⟩, hanswer, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          obtain rfl := OracleComp.eq_of_mem_supportWith_pure hnext
          obtain ⟨hs', hreply, hgrowth⟩ := hpreserve a _ state hs (answer, state') hanswer
          have hb := hbudget a (cfg.channels channel).1 ((hcfg.query channel).trans hi.le)
          exact ⟨hcfg.receive channel control answer (hreply.trans hb), hs', by
            dsimp only at hsize hgrowth ⊢
            nlinarith⟩)
    (size := fun a => 2 * cf * ((word a).length + count a + budget a + 1) +
      (stateEncoding (initial a)).length + count a * budget a + 1)
    (ComputableTidilyInPolyTime.polyBounded (by dsimp only [budget]; fun_prop))
    (by
      rintro a i ⟨cfg, state⟩ hi ⟨hcfg, _, hstate⟩
      have hf := hconfigurationSize _ _ _ cfg hcfg
      simp only [length_encPair]
      dsimp only at hstate ⊢
      nlinarith)).1
  have hproject : ComputableTidilyInPolyTime
      (fun pair : FiniteConfig k Bool Control Operation × State =>
        (pair.1.tapes.output, pair.2))
      (encPair encFiniteConfig stateEncoding) (encPair encBits stateEncoding) := by fun_prop
  refine (hloop.map hproject).congr fun a _ _ _ => ?_
  congr 2
  rw [MultiTapePTM.runOracle]
  change _ = (OracleComp.interpret (m := StateT State (WordOracleComp External)) _
    (MultiTapeMachine.run machine _ _ (count a) (word a))).run (initial a)
  rw [← MultiTapeMachine.finiteRunFrom_init, MultiTapeMachine.finiteRunFrom,
    OracleComp.interpret_map, StateT.run_map, OracleComp.run_interpret_iterate]
  simp only [← step_eq_run_interpret, start]

end Cslib.Probability.OpenOracleSimulation
