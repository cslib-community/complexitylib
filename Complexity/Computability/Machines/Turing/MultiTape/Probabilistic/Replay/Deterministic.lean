/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Option

/-!
# Coin-fixed runs, relabelling and finiteness of fair-coin oracle machines

Fixing all coins of a fair-coin oracle machine to a constant `bit` gives a deterministic word-query
program (`Turing.MultiTapePTM.runConfigFrom` with `pure bit`) whose result against every
deterministic oracle is supported by the fair-coin run
(`Turing.MultiTapePTM.mem_support_runConfigFrom_pure`).

Relabelling the control states along an equivalence preserves the run program
(`Turing.MultiTapePTM.runFrom_relabel`), and tables with finitely many symbols, states and channels
form a finite type (`Turing.MultiTapeMachine.Action.instFinite`, `Turing.MultiTapePTM.finite`).

## Main definitions

* `Turing.MultiTapePTM.relabel`: rename the control states of a fair-coin table.

## Main results

* `Turing.MultiTapeMachine.Action.instFinite`, `Turing.MultiTapePTM.finite`: finitely many
  instructions and fair-coin tables.
* `Turing.MultiTapePTM.runFrom_relabel`: relabelling preserves runs.
* `Turing.MultiTapePTM.mem_support_runConfigFrom_pure`: a coin-fixed run is supported by the
  fair-coin run.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
  (oracle Turing machines).
-/

@[expose] public section

namespace Turing

open Cslib

namespace MultiTapeMachine

variable {k : ℕ} {Symbol State State' Oracle : Type} {input : List Symbol}

/-- Finitely many symbols, states and channels give finitely many instructions. -/
instance Action.instFinite [Finite Symbol] [Finite State] [Finite Oracle] :
    Finite (Action k Symbol State Oracle) :=
  Finite.of_injective (fun a : Action k Symbol State Oracle => match a with
    | .step action symbol move => (Sum.inl (action, symbol, move) :
        (Turing.Action k Symbol State × (Oracle → Option Symbol) × (Oracle → SignType)) ⊕
          (Oracle × State))
    | .query oracle next => Sum.inr (oracle, next)) fun a b h => by
      cases a <;> cases b <;> simp_all

end MultiTapeMachine

namespace MultiTapePTM

open MultiTapeMachine

variable {k : ℕ} {Symbol State State' Oracle : Type} {input : List Symbol}

/-- Rename the control states of a fair-coin table along an equivalence. -/
def relabel (e : State ≃ State') (machine : MultiTapePTM k Symbol State Oracle) :
    MultiTapePTM k Symbol State' Oracle where
  initial := e machine.initial
  tr state symbol work answer bit :=
    (machine.tr (e.symm state) symbol work answer bit).mapState e

@[simp] theorem initialConfig_relabel (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (input : List Symbol) :
    (machine.relabel e).initialConfig input = (machine.initialConfig input).mapState e := rfl

variable [DecidableEq Oracle]

/-- Relabelling commutes with the run program, for every coin and request program. -/
theorem runConfigFrom_relabel {Query : Type} {spec : OracleSpec.{0, 0} Query}
    (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (machine.relabel e).runConfigFrom coin query fuel (cfg.mapState e) =
      Config.mapState e <$> machine.runConfigFrom coin query fuel cfg := by
  apply MultiTapeMachine.runConfigFrom_mapState machine (machine.relabel e)
    (fun choices => choices <$> coin) ?_ query e ?_ fuel cfg
  · intro α β f choices
    exact (Functor.map_map choices f coin).symm
  · intro state inp work answer
    funext bit
    simp only [relabel, Equiv.symm_apply_apply]
    rfl

/-- Relabelling preserves the output program of every run. -/
theorem runFrom_relabel {Query : Type} {spec : OracleSpec.{0, 0} Query} (e : State ≃ State')
    (machine : MultiTapePTM k Symbol State Oracle) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (machine.relabel e).runFrom coin query fuel (cfg.mapState e) =
      machine.runFrom coin query fuel cfg := by
  simp only [runFrom, runConfigFrom_relabel, Functor.map_map, Config.mapState_tapes_output]

omit [DecidableEq Oracle] in
/-- Finitely many symbols, states and channels give finitely many fair-coin tables. -/
instance finite [Finite Symbol] [Finite State] [Finite Oracle] :
    Finite (MultiTapePTM k Symbol State Oracle) := by
  have : Finite ((Oracle → Option Symbol) → Bool →
      MultiTapeMachine.Action k Symbol State Oracle) := inferInstance
  have : Finite ((Fin k → Option Symbol) → (Oracle → Option Symbol) → Bool →
      MultiTapeMachine.Action k Symbol State Oracle) := inferInstance
  exact Finite.of_injective (β := State × (State → Option Symbol → (Fin k → Option Symbol) →
      (Oracle → Option Symbol) → Bool → MultiTapeMachine.Action k Symbol State Oracle))
    (fun machine => (machine.initial, fun state symbol work answer bit =>
      machine.tr state symbol work answer bit))
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      refine MultiTapeMachine.ext h.1 ?_
      funext state symbol work answer bit
      exact congrFun (congrFun (congrFun (congrFun (congrFun h.2 state) symbol) work) answer) bit

/-- **A coin-fixed run is supported.** Against a deterministic oracle, the result of the run with
every coin fixed to `bit` is a supported result of the fair-coin run, with the unchanged state. -/
theorem mem_support_runConfigFrom_pure {σ : Type} (machine : MultiTapePTM k Symbol State Oracle)
    (bit : Bool) (answer : Oracle × List Symbol → List Symbol) (s : σ) (fuel : ℕ)
    (cfg : Config k Symbol State Oracle input) :
    (OracleComp.interpret (m := Id) answer (machine.runConfigFrom (pure bit)
        (fun oracle word => OracleComp.query (oracle, word)) fuel cfg), s) ∈
      ((OracleComp.interpret (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
          (fun q s => PMF.pure (answer q, s)))
        (machine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun oracle word => ProbOracleComp.query (oracle, word)) fuel cfg)).run s).support := by
  have hbit : bit ∈ (Probability.PMF.uniformOfFintype Bool).support := by
    rw [PMF.mem_support_iff, Probability.PMF.uniformOfFintype_apply]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  simp only [runConfigFrom]
  induction fuel generalizing cfg with
  | zero => exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [MultiTapeMachine.runConfigFrom, hs]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    | some state =>
      simp only [map_pure] at ih
      simp only [MultiTapeMachine.runConfigFrom, hs, map_pure, pure_bind, bind_map_left,
        OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
        ProbComp.eval_uniform, Probability.PMF.monad_bind_eq_bind, PMF.bind_map,
        PMF.mem_support_bind_iff, Function.comp_apply]
      refine ⟨bit, hbit, ?_⟩
      cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols bit
        with
      | step action symbol move => exact ih _
      | query oracle next =>
        simp only [OracleComp.interpret_bind, ProbOracleComp.interpret_query, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff]
        exact ⟨(answer (oracle, (cfg.channels oracle).queryBuffer), s),
          (PMF.mem_support_pure_iff _ _).mpr rfl, ih _⟩

end MultiTapePTM

end Turing
