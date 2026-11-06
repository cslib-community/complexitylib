/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle

/-!
# Routing a single oracle channel

Embed a single-channel fair-coin oracle machine into a named channel of a multi-channel machine.
The embedding preserves every machine step and the complete stateful interaction.

## Main definitions

* `Turing.MultiTapePTM.singleOracle`: route the machine's sole channel to a selected channel.
* `Turing.MultiTapePTM.embedSingleConfig`: place a single-channel configuration on that channel.

## Main results

* `Turing.MultiTapePTM.runOracle_singleOracle`: the embedded run interprets each query on the
  selected channel.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine

variable {k : ℕ} {Symbol State ι OracleState : Type} [DecidableEq ι]

/-- Embed a single-channel fair-coin machine on channel `i₀ : ι`, leaving all other channels
unused. -/
def singleOracle (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit) :
    MultiTapePTM k Symbol State ι where
  initial := machine.initial
  tr state symbol work answer bit :=
    match machine.tr state symbol work (fun _ => answer i₀) bit with
    | .step action qSym aMove =>
      .step action (fun j => if j = i₀ then qSym () else none)
        (fun j => if j = i₀ then aMove () else 0)
    | .query _ next => .query i₀ next

/-- Configuration embedding placing the single channel on `i₀` and empty channels elsewhere. -/
def embedSingleConfig {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) : Config k Symbol State ι input where
  tapes := cfg.tapes
  channels j := if j = i₀ then cfg.channels () else {}

@[simp]
theorem embedSingleConfig_tapes {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) :
    (embedSingleConfig i₀ cfg).tapes = cfg.tapes := rfl

@[simp]
theorem embedSingleConfig_initial (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit)
    (input : List Symbol) :
    embedSingleConfig i₀ (machine.initialConfig input) =
      (machine.singleOracle i₀).initialConfig input := by
  refine Config.ext rfl (funext fun j => ?_)
  simp only [embedSingleConfig, initialConfig, ite_self]

@[simp]
theorem embedSingleConfig_answerSymbols {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) :
    (embedSingleConfig i₀ cfg).answerSymbols i₀ = cfg.answerSymbols () := by
  simp only [Config.answerSymbols, embedSingleConfig, ↓reduceIte]

theorem embedSingleConfig_step {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) (action : Turing.Action k Symbol State)
    (qSym : Unit → Option Symbol) (aMove : Unit → SignType) :
    (embedSingleConfig i₀ cfg).step action
      (fun j => if j = i₀ then qSym () else none)
      (fun j => if j = i₀ then aMove () else 0) =
      embedSingleConfig i₀ (cfg.step action qSym aMove) := by
  refine Config.ext rfl (funext fun j => ?_)
  by_cases hj : j = i₀
  · subst hj
    simp only [Config.step, embedSingleConfig, ↓reduceIte]
  · simp only [Config.step, embedSingleConfig, hj, ↓reduceIte, Option.toList_none,
      List.append_nil, SignType.coe_zero, add_zero]

theorem embedSingleConfig_receive {input : List Symbol} (i₀ : ι)
    (cfg : Config k Symbol State Unit input) (next : State) (answer : List Symbol) :
    (embedSingleConfig i₀ cfg).receive i₀ next answer =
      embedSingleConfig i₀ (cfg.receive () next answer) := by
  refine Config.ext rfl (funext fun j => ?_)
  by_cases hj : j = i₀
  · subst hj
    simp only [Config.receive, embedSingleConfig, Function.update_self, ↓reduceIte]
  · simp only [Config.receive, embedSingleConfig, Function.update_of_ne hj, hj, ↓reduceIte]

/-- Running `singleOracle i₀ machine` forwards every query `((), word)` to `(i₀, word)`. -/
theorem runOracle_singleOracle (i₀ : ι) (machine : MultiTapePTM k Symbol State Unit)
    (fuel : ℕ) (input : List Symbol) :
    (machine.singleOracle i₀).runOracle fuel input =
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun n => OracleComp.query
            (spec := probOracleSpec (fun _ : ι × List Symbol => List Symbol)) (Sum.inl n))
          (fun q : Unit × List Symbol =>
            ProbOracleComp.query
              (spec := fun _ : ι × List Symbol => List Symbol) (i₀, q.2)))
        (machine.runOracle fuel input) := by
  have hsim := MultiTapeMachine.runConfigFrom_map machine (machine.singleOracle i₀)
    (fun choices => choices <$> ProbOracleComp.sample
      (spec := fun _ : ι × List Symbol => List Symbol) (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun _ word => ProbOracleComp.query
      (spec := fun _ : ι × List Symbol => List Symbol) (i₀, word))
    (fun op word => ProbOracleComp.query (op, word))
    (embedSingleConfig i₀)
    (fun cfg => by
      cases hs : cfg.tapes.state with
      | none =>
        simp only [MultiTapeMachine.runConfigFrom, embedSingleConfig, hs, map_pure]
      | some state =>
        have hanswer : (fun _ : Unit => (embedSingleConfig i₀ cfg).answerSymbols i₀) =
            cfg.answerSymbols := by
          funext u
          cases u
          exact embedSingleConfig_answerSymbols i₀ cfg
        have hch : ((embedSingleConfig i₀ cfg).channels i₀).queryBuffer =
            (cfg.channels ()).queryBuffer := by
          simp only [embedSingleConfig, ↓reduceIte]
        simp only [MultiTapeMachine.runConfigFrom, embedSingleConfig_tapes, hs, bind_map_left,
          map_bind]
        congr 1
        funext bit
        simp only [singleOracle, hanswer]
        cases htr : machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols bit with
        | step action symbol move =>
          simp only [map_pure, embedSingleConfig_step]
        | query oracle next =>
          cases oracle
          simp only [hch, bind_pure_comp, Functor.map_map, embedSingleConfig_receive])
    fuel (machine.initialConfig input)
  calc (machine.singleOracle i₀).runOracle fuel input
      = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom
          (machine.singleOracle i₀)
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun op word => ProbOracleComp.query (op, word)) fuel
          (embedSingleConfig i₀ (machine.initialConfig input)) := by
        rw [embedSingleConfig_initial]; rfl
    _ = (fun final => final.tapes.output) <$> MultiTapeMachine.runConfigFrom machine
          (fun choices => choices <$> ProbOracleComp.sample
            (spec := fun _ : ι × List Symbol => List Symbol) (ProbComp.uniform Bool))
          (fun _ word => ProbOracleComp.query (i₀, word)) fuel
          (machine.initialConfig input) := by
        rw [hsim, Functor.map_map]; rfl
    _ = _ := by
        simp only [runOracle, run, runFrom, runConfigFrom,
          OracleComp.interpret_map, MultiTapeMachine.interpret_runConfigFrom,
          ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query]
        rfl

end Turing.MultiTapePTM
