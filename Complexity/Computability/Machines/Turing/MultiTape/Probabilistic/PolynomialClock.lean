/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Clock
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.PrepareClock
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import Complexity.Computability.Machines.Turing.MultiTape.Run

/-!
# Compiling polynomial clocks

A deterministic preparation program writes a unary budget on the last work tape. The common
tape embedding and sequential compiler then run the common clock consumer. Preparation scratch
tapes and source tapes are disjoint; all tapes start blank. Every preparation and controller
instruction is charged to the compiled machine's polynomial bound.

## Main definitions

* `Turing.MultiTapePTM.PolynomialClock.compile`: prepare a budget and consume it.

## Main results

* `Turing.MultiTapePTM.PolynomialClock.run_interpret_compile`: retain the joint configuration
  and private interpreter state, apart from the source's discarded control state.
* `Turing.MultiTapePTM.exists_polynomialClock`: a finite-control machine implements the cutoff
  and halts within a uniform polynomial, against any query interpreter and stateless coin law.

## References

Adapts the role of MultiTape/Oracle/PolynomialClock.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using functional budget generation and the shared
machine compilers.
-/

@[expose] public section

namespace Turing.MultiTapePTM.PolynomialClock

open Cslib MultiTapeMachine

variable {k r : ℕ} {State PrepareState Oracle : Type}

/-- Reserve disjoint source and preparation tapes, then run the budget controller. -/
noncomputable def compile (machine : MultiTapePTM k Bool State Oracle)
    (prepare : MultiTapeTM (r + 1) Bool PrepareState) :
    MultiTapePTM (k + r + 1) Bool (PrepareState ⊕ Clock.Control State) Oracle :=
  (ofDeterministic (prepare.extendTapes (Fin.natAddEmb k))).seq
    (machine.extendTapes (Fin.castAddEmb r)).withClock

/-- A prepared word stays on the last tape when disjoint source tapes are added in front. -/
theorem embed_budget (input word : List Bool) (state : Option PrepareState) :
    MultiTapeTM.embed (Fin.natAddEmb k)
      (wordsCfg input state (Function.update (fun _ => []) (Fin.last r) word) [])
      (fun _ _ => none) (fun _ => 0) =
      wordsCfg input state (Function.update (fun _ => []) (Fin.last (k + r)) word) [] := by
  have hlast : (Fin.natAddEmb k) (Fin.last r) = Fin.last (k + r) := by ext; simp
  have h := MultiTapeTM.embed_wordsCfg (input := input) (q := state) (out := [])
      (Fin.natAddEmb k) (v := Function.update (fun _ => []) (Fin.last r) word)
      (ws := fun _ => []) (ws' := Function.update (fun _ => []) (Fin.last (k + r)) word)
      (fun j => by
        rw [← hlast]
        simp only [Function.update_apply, Function.Embedding.apply_eq_iff_eq])
      (fun i hi => by
        have hne : i ≠ Fin.last (k + r) := by
          rintro rfl
          exact hi ⟨Fin.last r, hlast⟩
        simp [hne])
  simp only [tapeOfList_nil] at h
  exact h

/-- The preparation phase has halted, with only its last work tape nonempty. -/
def ready (input word : List Bool) : Config (k + r + 1) Bool PrepareState Oracle input where
  tapes := wordsCfg input none (Function.update (fun _ => []) (Fin.last (k + r)) word) []

/-- Handoff supplies precisely the initial source configuration and its prepared budget. -/
theorem start_ready (machine : MultiTapePTM k Bool State Oracle) (input word : List Bool) :
    Sequential.start (machine.extendTapes (Fin.castAddEmb r)).withClock
      (ready (PrepareState := PrepareState) input word) =
      AuxiliaryTape.config ((machine.extendTapes (Fin.castAddEmb r)).initialConfig input)
        (tapeOfList word) 0 false := by
  refine Config.ext ?_ rfl
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Sequential.start, ready, Cfg.withState, wordsCfg, AuxiliaryTape.config,
        initialConfig, Cfg.init]

/-- The embedded deterministic preparation reaches the exact ready configuration. -/
theorem prepare_runFrom (prepare : MultiTapeTM (r + 1) Bool PrepareState)
    (input word : List Bool) (time : ℕ)
    (hprepare : prepare.runFrom (prepare.initCfg input) time =
      wordsCfg input none (Function.update (fun _ => []) (Fin.last r) word) []) :
    (prepare.extendTapes (Fin.natAddEmb k)).runFrom
      ((prepare.extendTapes (Fin.natAddEmb k)).initCfg input) time =
      wordsCfg input none (Function.update (fun _ => []) (Fin.last (k + r)) word) [] := by
  rw [MultiTapeTM.runFrom_extendTapes]
  have hview : MultiTapeTM.viewCfg (Fin.natAddEmb k)
      ((prepare.extendTapes (Fin.natAddEmb k)).initCfg input) = prepare.initCfg input := rfl
  rw [hview, hprepare]
  exact embed_budget input word none

/-- The source data after exhaustion, embedded alongside the consumed budget and halted control. -/
def finish {input : List Bool} (cfg : Config k Bool State Oracle input) (budget : ℕ) :
    Config (k + r + 1) Bool (PrepareState ⊕ Clock.Control State) Oracle input :=
  Sequential.right (AuxiliaryTape.stopped
    (cfg.embed (Fin.castAddEmb r) (fun _ _ => none) (fun _ => 0))
    (tapeOfList (List.replicate budget true)) budget)

variable {Query OracleState : Type} {spec : OracleSpec.{0, 0} Query} [DecidableEq Oracle]

/-- Preparing and consuming a budget preserves the entire source data and private interpreter
state. Both preparation time and every controller instruction are included in the bound. -/
theorem run_interpret_compile (machine : MultiTapePTM k Bool State Oracle)
    (prepare : MultiTapeTM (r + 1) Bool PrepareState)
    (coin : OracleComp spec Bool) (query : Oracle → List Bool → OracleComp spec (List Bool))
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (input : List Bool) (budget time padding : ℕ) (s : OracleState)
    (hprepare : prepare.runFrom (prepare.initCfg input) time =
      wordsCfg input none (Function.update (fun _ => []) (Fin.last r)
        (List.replicate budget true)) []) :
    (OracleComp.interpret oracle ((compile machine prepare).runConfigFrom coin query
      (time + (2 * budget + 1 + padding)) ((compile machine prepare).initialConfig input))).run s =
      ((OracleComp.interpret oracle
        (machine.runConfigFrom coin query budget (machine.initialConfig input))).run s).map
        (fun (final, s') => (finish final budget, s')) := by
  let source := machine.extendTapes (Fin.castAddEmb r)
  let first : MultiTapePTM (k + r + 1) Bool PrepareState Oracle :=
    ofDeterministic (prepare.extendTapes (Fin.natAddEmb k))
  have hclock := run_interpret_runConfigFrom_withClock_add source coin query oracle coinLaw hcoin
    (source.initialConfig input) (tapeOfList (List.replicate budget true)) 0 budget padding s
    (fun i hi => by simp [tapeOfList_ofNat, hi]) (by simp [tapeOfList_ofNat])
  simp only [zero_add, MultiTapePTM.runConfigFrom] at hclock
  have hfirst : (OracleComp.interpret oracle
      (first.runConfigFrom coin query time (first.initialConfig input))).run s =
      PMF.pure (ready input (List.replicate budget true), s) := by
    rw [run_interpret_runConfigFrom_ofDeterministic (prepare.extendTapes (Fin.natAddEmb k))
      coin query oracle coinLaw hcoin]
    change PMF.pure ({ first.initialConfig input with
      tapes := (prepare.extendTapes (Fin.natAddEmb k)).runFrom
        ((prepare.extendTapes (Fin.natAddEmb k)).initCfg input) time }, s) = _
    rw [prepare_runFrom prepare input (List.replicate budget true) time hprepare]
    rfl
  have hseq := MultiTapeMachine.run_interpret_runConfigFrom_seq_pure first source.withClock
    (fun choices => choices <$> coin) (fun _ _ => by rw [Functor.map_map]; rfl) query oracle
    (first.initialConfig input) (ready input (List.replicate budget true)) time
    (2 * budget + 1 + padding) s hfirst rfl (by
      intro final hfinal
      rw [start_ready, hclock] at hfinal
      obtain ⟨⟨cfg, state⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      exact (congrArg (fun result => result.1.tapes.state) heq).symm)
  change (OracleComp.interpret oracle
    ((compile machine prepare).runConfigFrom coin query _ _)).run s = _ at hseq
  rw [start_ready, hclock] at hseq
  simp only [source, MultiTapeMachine.initialConfig_extendTapes,
    MultiTapeMachine.runConfigFrom_embed machine _ (fun choices => choices <$> coin)
      (fun _ _ => by rw [Functor.map_map]; rfl) query,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
    PMF.map_comp] at hseq
  exact hseq

end Turing.MultiTapePTM.PolynomialClock

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine PolynomialClock
open MultiTapeTM (PolyBounded)

/-- A finite-control machine implements a polynomial cutoff uniformly and actually halts.
Its polynomial charges budget generation, rewinding, and clock consumption. Oracle calls keep their
abstract instruction cost; no efficiency of an arbitrary supplied query program is asserted. -/
theorem exists_polynomialClock {k : ℕ} {State Oracle : Type} [Finite State] [DecidableEq Oracle]
    (machine : MultiTapePTM k Bool State Oracle) (coefficient degree : ℕ) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State') (target : MultiTapePTM k' Bool State' Oracle)
      (c d : ℕ), ∀ (input : List Bool) (Query OracleState : Type) (spec : OracleSpec.{0, 0} Query)
      (coin : OracleComp spec Bool) (query : Oracle → List Bool → OracleComp spec (List Bool))
      (oracle : (q : Query) → StateT OracleState PMF (spec q)) (coinLaw : PMF Bool),
      (∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s))) →
      ∀ s,
      (OracleComp.interpret oracle
        (target.run coin query (c * (input.length + 1) ^ d) input)).run s =
        (OracleComp.interpret oracle (machine.run coin query
          (coefficient * (input.length + 1) ^ degree) input)).run s ∧
      ∀ result ∈ ((OracleComp.interpret oracle (target.runConfigFrom coin query
        (c * (input.length + 1) ^ d) (target.initialConfig input))).run s).support,
        result.1.tapes.state = none := by
  obtain ⟨r, PrepareState, hfinite, prepare, cp, dp, hprepare⟩ :=
    MultiTapeTM.PolynomialClock.exists_prepare coefficient degree
  have hb : PolyBounded List.length
      (fun input : List Bool => coefficient * (input.length + 1) ^ degree) :=
    .of_forall_le coefficient degree (fun _ => le_rfl)
  have hp : PolyBounded List.length (fun input : List Bool => cp * (input.length + 1) ^ dp) :=
    .of_forall_le cp dp (fun _ => le_rfl)
  obtain ⟨c, d, hbound⟩ :=
    (hp.add (((PolyBounded.const 2).mul hb).add (PolyBounded.const 1))).exists_le
  refine ⟨k + r + 1, PrepareState ⊕ Clock.Control State, inferInstance, compile machine prepare,
    c, d, fun input Query OracleState spec coin query oracle coinLaw hcoin s => ?_⟩
  let budget := coefficient * (input.length + 1) ^ degree
  let time := cp * (input.length + 1) ^ dp
  let padding := c * (input.length + 1) ^ d - (time + (2 * budget + 1))
  have htime : time + (2 * budget + 1 + padding) = c * (input.length + 1) ^ d := by grind
  have hrun := run_interpret_compile machine prepare coin query oracle coinLaw hcoin input budget
    time padding s (hprepare input)
  rw [htime] at hrun
  constructor
  · have hout := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2))) hrun
    simpa only [run, runFrom, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
      PMF.map_comp, Function.comp_def, finish, Sequential.right, Cfg.mapState,
      AuxiliaryTape.stopped_output, Config.embed_output] using hout
  · intro result hresult
    rw [hrun] at hresult
    obtain ⟨⟨cfg, state⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact (congrArg (fun result => result.1.tapes.state) heq).symm

end Turing.MultiTapePTM
