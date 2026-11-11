/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.WithOracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Embed
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Tactic.Linarith

/-!
# Saved-coin replay from a complete encoded input

Pair preparation, a virtual-input boundary marker, and the two-phase controller implement replay
from an ordinary input encoding of saved coins and source input. All preparation instructions are
charged. The compiler retains the original word-oracle channels, so it does not copy arbitrarily
long replies into an encoded machine configuration.

## Main results

* `Turing.MultiTapePTM.exists_oracleReplay`: a finite-control replay machine with a linear
  full-input clock, preserving the output and external state and actually halting.

## References

An original composition of the existing deterministic pair preparer, virtual-input compiler,
saved-coin controller, and common machine sequencing law. The extracted pair preparer's original
source credit is recorded in `MultiTape.Plumbing.PrepareReplay`.
-/

@[expose] public section

namespace Turing.MultiTapePTM.ReplayWithOracle

open Cslib MultiTapeTM MultiTapeMachine

variable {k r : ℕ} {State PrepareState Oracle : Type}

private noncomputable def prepareInput (prepare : MultiTapeTM (r + 2) Bool PrepareState) :
    MultiTapeTM (k + r + 3) Bool (PrepareState ⊕ MarkWorkState) :=
  (prepare.extendTapes (ReplayInput.prepareTapes k r)).seq
    (markFlag (k + r + 1) (some true))

private noncomputable def compile (machine : MultiTapePTM k Bool State Oracle)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState) :
    MultiTapePTM (k + r + 3) Bool ((PrepareState ⊕ MarkWorkState) ⊕ Control State) Oracle :=
  (ofDeterministic (prepareInput prepare)).seq
    (machine.extendTapes (Fin.castAddEmb r)).replayWithOracle.inputFromTape

private theorem runFrom_prepareInput (prepare : MultiTapeTM (r + 2) Bool PrepareState)
    (coins input outer : List Bool) (t s : ℕ)
    (h : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) t s) :
    (prepareInput (k := k) prepare).runFrom ((prepareInput prepare).initCfg outer) (t + 2) =
      inCfg true (ReplayInput.initial k r coins input (Q := PrepareState ⊕ MarkWorkState) none)
        outer := by
  have hp := ReplayInput.runFrom_prepare (k := k) prepare coins input outer t s h
  have hm := ReplayInput.runFrom_mark (k := k) (r := r) coins input outer
  have hs := runFrom_seq (tm₁ := markFlag (k + r + 1) (some true)) hp rfl
    (by simpa [Cfg.withState, wordsCfg, markFlag, q₀_ofTr] using hm) rfl
  simpa [prepareInput, initCfg_eq_wordsCfg, wordsCfg, Cfg.mapState, MultiTapeTM.seq,
    MultiTapeTM.combine, q₀_ofTr, inCfg, ReplayInput.initial] using hs

private def ready (coins input outer : List Bool) :
    Config (k + r + 3) Bool (PrepareState ⊕ MarkWorkState) Oracle outer where
  tapes := inCfg true (ReplayInput.initial k r coins input none) outer

private theorem start_ready (machine : MultiTapePTM k Bool State Oracle)
    (coins input outer : List Bool) :
    MultiTapeMachine.Sequential.start
      (machine.extendTapes (Fin.castAddEmb r)).replayWithOracle.inputFromTape
      (ready (PrepareState := PrepareState) coins input outer) =
      InputFromTape.config true
        (AuxiliaryTape.config ((machine.extendTapes (Fin.castAddEmb r)).initialConfig input)
          (tapeOfList coins) 0 none) outer 1 := by
  have htapes : (fun i : Fin (k + r + 1) =>
      tapeOfList (Fin.snoc (α := fun _ => List Bool)
        (fun _ : Fin (k + r) => []) coins i)) =
      Fin.lastCases (tapeOfList coins) (fun _ _ => none) := by
    funext i
    induction i using Fin.lastCases <;> simp
  have hpositions : (fun i : Fin (k + r + 1) =>
      Fin.lastCases (motive := fun _ => ℤ) 0 (fun _ => 0) i) = (fun _ => (0 : ℤ)) := by
    funext i
    induction i using Fin.lastCases <;> simp
  refine Config.ext ?_ rfl
  simp [ready, MultiTapeMachine.Sequential.start, InputFromTape.config, AuxiliaryTape.config,
    ReplayInput.initial, wordsCfg, initialConfig, Cfg.init, inCfg, Cfg.withState,
    replayWithOracle, inputFromTape, MultiTapeMachine.inputFromTape, htapes, hpositions]

private def finish {input : List Bool} (cfg : Config k Bool State Oracle input)
    (coins outer : List Bool) : Config (k + 3) Bool (Control State) Oracle outer :=
  InputFromTape.config true (AuxiliaryTape.stopped cfg (tapeOfList coins) coins.length) outer 1

private theorem run_interpret_input [DecidableEq Oracle]
    {Query Store : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (coin : OracleComp spec Bool) (query : Oracle → List Bool → OracleComp spec (List Bool))
    (oracle : (q : Query) → StateT Store PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (coins input outer : List Bool) (padding : ℕ) (s : Store) :
    (OracleComp.interpret oracle (machine.replayWithOracle.inputFromTape.runConfigFrom coin query
      (2 * coins.length + 1 + padding) (InputFromTape.config true
        (AuxiliaryTape.config (machine.initialConfig input) (tapeOfList coins) 0 none)
        outer 1))).run s =
      ((OracleComp.interpret oracle
        (machine.runConfigFromCoins query coins (machine.initialConfig input))).run s).map
        (fun (final, s') => (finish final coins outer, s')) := by
  have hrun := run_coins_add machine query (machine.initialConfig input) coins
    (tapeOfList coins) 0 padding (fun i _ => by simp [tapeOfList_ofNat])
    (by simp [tapeOfList_ofNat])
  simp only [zero_add] at hrun
  rw [runConfigFrom_inputFromTape, OracleComp.interpret_map, StateT.run_map,
    run_interpret_coin_independent machine coin query oracle coinLaw hcoin, hrun,
    OracleComp.interpret_map, StateT.run_map]
  simp only [PMF.monad_map_eq_map, PMF.map_comp]
  rfl

private def compiledFinish {input : List Bool} (cfg : Config k Bool State Oracle input)
    (coins outer : List Bool) :
    Config (k + r + 3) Bool ((PrepareState ⊕ MarkWorkState) ⊕ Control State) Oracle outer :=
  MultiTapeMachine.Sequential.right
    (finish (cfg.embed (Fin.castAddEmb r) (fun _ _ => none) (fun _ => 0)) coins outer)

private theorem run_interpret_compile [DecidableEq Oracle]
    {Query Store : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool State Oracle)
    (prepare : MultiTapeTM (r + 2) Bool PrepareState)
    (coin : OracleComp spec Bool) (query : Oracle → List Bool → OracleComp spec (List Bool))
    (oracle : (q : Query) → StateT Store PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (coins input outer : List Bool) (time space padding : ℕ) (store : Store)
    (hprepare : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) time space) :
    (OracleComp.interpret oracle ((compile machine prepare).runConfigFrom coin query
      (time + 2 + (2 * coins.length + 1 + padding))
      ((compile machine prepare).initialConfig outer))).run store =
      ((OracleComp.interpret oracle
        (machine.runConfigFromCoins query coins (machine.initialConfig input))).run store).map
        (fun (final, s') => (compiledFinish final coins outer, s')) := by
  let source := machine.extendTapes (Fin.castAddEmb r)
  let first : MultiTapePTM (k + r + 3) Bool (PrepareState ⊕ MarkWorkState) Oracle :=
    ofDeterministic (prepareInput prepare)
  have hfirst : (OracleComp.interpret oracle
      (first.runConfigFrom coin query (time + 2) (first.initialConfig outer))).run store =
      PMF.pure (ready coins input outer, store) := by
    rw [run_interpret_runConfigFrom_ofDeterministic (prepareInput prepare)
      coin query oracle coinLaw hcoin]
    change PMF.pure ({ first.initialConfig outer with
      tapes := (prepareInput prepare).runFrom
        ((prepareInput prepare).initCfg outer) (time + 2) }, store) = _
    rw [runFrom_prepareInput prepare coins input outer time space hprepare]
    rfl
  have hsecond := run_interpret_input source coin query oracle coinLaw hcoin
    coins input outer padding store
  simp only [MultiTapePTM.runConfigFrom] at hsecond
  have hseq := MultiTapeMachine.run_interpret_runConfigFrom_seq_pure first
    source.replayWithOracle.inputFromTape
    (fun choices => choices <$> coin) (fun _ _ => by rw [Functor.map_map]; rfl) query oracle
    (first.initialConfig outer) (ready coins input outer) (time + 2)
    (2 * coins.length + 1 + padding) store hfirst rfl (by
      intro final hfinal
      rw [start_ready, hsecond] at hfinal
      obtain ⟨⟨cfg, state⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      exact (congrArg (fun result => result.1.tapes.state) heq).symm)
  change (OracleComp.interpret oracle
    ((compile machine prepare).runConfigFrom coin query _ _)).run store = _ at hseq
  rw [start_ready, hsecond] at hseq
  simp only [source, MultiTapeMachine.initialConfig_extendTapes, runConfigFromCoins_embed,
    OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp] at hseq
  exact hseq

end Turing.MultiTapePTM.ReplayWithOracle

namespace Turing.MultiTapePTM

open Cslib MultiTapeTM MultiTapeMachine ReplayWithOracle

/-- A finite-control native machine replays saved coins from an encoded pair in linear time.
The bound includes pair preparation, virtual-input marking, every replay instruction, and halting.
The whole external state is preserved for every query interpreter and stateless native coin law;
the external handler's computation retains its abstract oracle cost. -/
theorem exists_oracleReplay {k : ℕ} {State Oracle : Type} [Finite State] [DecidableEq Oracle]
    (machine : MultiTapePTM k Bool State Oracle) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State') (target : MultiTapePTM k' Bool State' Oracle)
      (c : ℕ), ∀ (coins input : List Bool) (Query Store : Type) (spec : OracleSpec Query)
      (coin : OracleComp spec Bool) (query : Oracle → List Bool → OracleComp spec (List Bool))
      (oracle : (q : Query) → StateT Store PMF (spec q)) (coinLaw : PMF Bool),
      (∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s))) →
      ∀ s,
      (OracleComp.interpret oracle
        (target.run coin query (c * ((encPair encBits encBits (coins, input)).length + 1))
          (encPair encBits encBits (coins, input)))).run s =
        (OracleComp.interpret oracle (machine.runCoins query coins input)).run s ∧
      ∀ result ∈ ((OracleComp.interpret oracle (target.runConfigFrom coin query
        (c * ((encPair encBits encBits (coins, input)).length + 1))
        (target.initialConfig (encPair encBits encBits (coins, input))))).run s).support,
        result.1.tapes.state = none := by
  obtain ⟨r, PrepareState, hfinite, prepare, c, hp⟩ :=
    PairEncoding.exists_prepare encBits encBits (encPair encBits encBits)
  refine ⟨k + r + 3, (PrepareState ⊕ MarkWorkState) ⊕ Control State, inferInstance,
    compile machine prepare, c + 5, ?_⟩
  intro coins input Query Store spec coin query oracle coinLaw hcoin store
  let size := (encPair encBits encBits (coins, input)).length + 1
  let time := c * size
  let padding := (c + 5) * size - (time + 2 + (2 * coins.length + 1))
  have hlen := length_le_encPair_left encBits encBits (coins, input)
  simp only [encBits_apply] at hlen
  have hbound : time + 2 + (2 * coins.length + 1) ≤ (c + 5) * size := by
    dsimp only [time, size]
    nlinarith
  have htime : time + 2 + (2 * coins.length + 1 + padding) = (c + 5) * size := by grind
  have hrun := run_interpret_compile machine prepare coin query oracle coinLaw hcoin
    coins input (encPair encBits encBits (coins, input)) time time padding store (hp (coins, input))
  rw [htime] at hrun
  constructor
  · have hout := congrArg (PMF.map (fun result => (result.1.tapes.output, result.2))) hrun
    simpa only [run, runFrom, runCoins, runFromCoins, OracleComp.interpret_map, StateT.run_map,
      PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, compiledFinish,
      MultiTapeMachine.Sequential.right, Cfg.mapState, finish, InputFromTape.config_output,
      AuxiliaryTape.stopped_output, Config.embed_output] using hout
  · intro result hresult
    rw [hrun] at hresult
    obtain ⟨⟨cfg, state⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact (congrArg (fun result => result.1.tapes.state) heq).symm

end Turing.MultiTapePTM
