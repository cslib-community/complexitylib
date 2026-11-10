/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Program

/-!
# Simulating instructions by bounded blocks

A machine transformation can implement each source instruction with a fixed block of target
instructions. The simulation preserves the joint distribution of machine configuration and
private interpreter state. Its configuration embedding may change after each block, for example
to track a clock head. Source and target may use different alphabets, tapes, channels and choices;
their programs use the same typed effect interface.

The one-block hypothesis includes halted configurations, so padding a halted source is simulated
correctly. The source need not halt before its external clock expires.

## Main results

* `Turing.MultiTapeMachine.runConfigFrom_map`: one-instruction simulation preserves the entire
  typed program, before interpretation.
* `Turing.MultiTapeMachine.runConfigFrom_mapState`: commuting transition tables preserve clocked
  execution under a possibly noninjective control-state relabelling.
* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_mul_indexed`: bounded block simulation
  with a changing configuration embedding.
* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_mul`: the fixed-embedding specialization.

## References

Adapted from MultiTape/Oracle/Simulation.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v w

variable {k k' : ℕ} {Symbol Symbol' State State' Oracle Oracle' OracleState : Type}
  {Query : Type u} {spec : OracleSpec.{u, 0} Query}
  {Choose : Type → Type v} {Choose' : Type → Type w}
  {input : List Symbol} {input' : List Symbol'} [DecidableEq Oracle] [DecidableEq Oracle']
  (source : MultiTapeMachine k Symbol State Oracle Choose)
  (target : MultiTapeMachine k' Symbol' State' Oracle' Choose')
  (choose : Choose (Action k Symbol State Oracle) → OracleComp spec (Action k Symbol State Oracle))
  (choose' : Choose' (Action k' Symbol' State' Oracle') →
    OracleComp spec (Action k' Symbol' State' Oracle'))
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))
  (query' : Oracle' → List Symbol' → OracleComp spec (List Symbol'))

/-- A one-instruction program simulation preserves every clocked run. The hypothesis includes
halted configurations, and the embedding may change the tape alphabet and input word. -/
theorem runConfigFrom_map
    (embed : Config k Symbol State Oracle input → Config k' Symbol' State' Oracle' input')
    (hstep : ∀ cfg, target.runConfigFrom choose' query' 1 (embed cfg) =
      embed <$> source.runConfigFrom choose query 1 cfg)
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    target.runConfigFrom choose' query' fuel (embed cfg) =
      embed <$> source.runConfigFrom choose query fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    rw [show fuel + 1 = 1 + fuel by lia, target.runConfigFrom_add, source.runConfigFrom_add,
      hstep, bind_map_left, map_bind]
    congr 1 with next : 1
    exact ih next

/-- Relabelling control preserves the full clocked program when transition tables commute.
The map need not be injective: the table equation must hold at every source state, including
states identified by the map. Halting is preserved, and the fuel and query handler are unchanged. -/
theorem runConfigFrom_mapState [Functor Choose]
    (source : MultiTapeMachine k Symbol State Oracle Choose)
    (target : MultiTapeMachine k Symbol State' Oracle Choose)
    (choose : {α : Type} → Choose α → OracleComp spec α)
    (hchoose : ∀ {α β : Type} (f : α → β) (choices : Choose α),
      choose (f <$> choices) = f <$> choose choices)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (f : State → State')
    (htr : ∀ state inp work answer,
      target.tr (f state) inp work answer = Action.mapState f <$> source.tr state inp work answer)
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) :
    target.runConfigFrom choose query fuel (Config.mapState f cfg) =
      Config.mapState f <$> source.runConfigFrom choose query fuel cfg := by
  apply runConfigFrom_map source target choose choose query query (Config.mapState f) ?_ fuel cfg
  intro cfg
  cases hs : cfg.tapes.state with
  | none => simp [runConfigFrom, Config.mapState, Cfg.mapState, hs]
  | some state =>
    simp only [runConfigFrom, Config.mapState, Cfg.mapState, hs, Option.map_some,
      Cfg.inputSymbol, htr, hchoose, bind_map_left, map_bind]
    congr 1 with action : 1
    cases action <;> simp [Action.mapState, Config.mapState, Config.step, Config.receive,
      Turing.Action.apply, Cfg.mapState]

/-- A bounded simulation may update its embedding after each source instruction.
All private interpreter state is retained, including state shared by coin and oracle programs. -/
theorem run_interpret_runConfigFrom_mul_indexed (delay fuel : ℕ)
    (embed : ℕ → Config k Symbol State Oracle input → Config k' Symbol' State' Oracle' input')
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (hstep : ∀ i, i < fuel → ∀ cfg s,
      (OracleComp.interpret oracle
        (target.runConfigFrom choose' query' delay (embed i cfg))).run s =
        ((OracleComp.interpret oracle (source.runConfigFrom choose query 1 cfg)).run s).map
          (fun (final, s') => (embed (i + 1) final, s')))
    (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle
      (target.runConfigFrom choose' query' (delay * fuel) (embed 0 cfg))).run s =
      ((OracleComp.interpret oracle (source.runConfigFrom choose query fuel cfg)).run s).map
        (fun (final, s') => (embed fuel final, s')) := by
  induction fuel generalizing embed cfg s with
  | zero => simp
  | succ fuel ih =>
    rw [show delay * (fuel + 1) = delay + delay * fuel by lia,
      target.runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, hstep 0 (by lia), PMF.bind_map]
    rw [show fuel + 1 = 1 + fuel by lia, source.runConfigFrom_add,
      OracleComp.interpret_bind, StateT.run_bind, Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    simp only [Function.comp_def]
    congr 1 with result : 1
    simpa [Nat.add_comm] using ih (fun i => embed (i + 1))
      (fun i hi => hstep (i + 1) (by lia)) result.1 result.2

/-- Simulating one instruction by a block of `delay` instructions preserves every bounded run. -/
theorem run_interpret_runConfigFrom_mul
    (embed : Config k Symbol State Oracle input → Config k' Symbol' State' Oracle' input')
    (delay : ℕ) (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (hstep : ∀ cfg s,
      (OracleComp.interpret oracle
        (target.runConfigFrom choose' query' delay (embed cfg))).run s =
        ((OracleComp.interpret oracle (source.runConfigFrom choose query 1 cfg)).run s).map
          (fun (final, s') => (embed final, s')))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle
      (target.runConfigFrom choose' query' (delay * fuel) (embed cfg))).run s =
      ((OracleComp.interpret oracle (source.runConfigFrom choose query fuel cfg)).run s).map
        (fun (final, s') => (embed final, s')) :=
  run_interpret_runConfigFrom_mul_indexed source target choose choose' query query' delay fuel
    (fun _ => embed) oracle (fun _ _ => hstep) cfg s

end Turing.MultiTapeMachine
