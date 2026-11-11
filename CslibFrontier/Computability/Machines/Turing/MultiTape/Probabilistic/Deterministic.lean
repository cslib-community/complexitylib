/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic

/-!
# Deterministic machines inside probabilistic programs

The embedding ignores each coin and never submits a query. With a stateless coin interpretation,
it preserves the entire communication state and every oracle's private state. The number of
instructions, ordinary tapes and output agree exactly with the upstream deterministic run.

Adapted from the cslib `crypto` branch's Oracle/Deterministic.lean at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, for the common machine and typed program interface.

## Main definitions

* `Turing.MultiTapePTM.ofDeterministic`: repeat the deterministic action on both coin branches.

## Main results

* `Turing.MultiTapePTM.run_interpret_ofDeterministic`: preserve joint output and private state.
* `Turing.MultiTapePTM.eval_runClosed_ofDeterministic`: the closed deterministic run distribution.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query OracleState : Type} {spec : OracleSpec.{0, 0} Query}
  {input : List Symbol}

/-- Ignore the coin and oracle channels, retaining the deterministic states and ordinary tapes. -/
noncomputable def ofDeterministic (machine : MultiTapeTM k Symbol State) :
    MultiTapePTM k Symbol State Oracle where
  initial := machine.q₀
  tr state symbol work _ _ := .step (machine.tr state symbol work) (fun _ => none) (fun _ => 0)

/-- A deterministic embedding leaves all channels and the oracle's private state unchanged.
The coin may have any fixed distribution, provided drawing it has no effect on private state. -/
theorem run_interpret_runConfigFrom_ofDeterministic [DecidableEq Oracle]
    (machine : MultiTapeTM k Symbol State) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle
      ((ofDeterministic machine).runConfigFrom coin query fuel cfg)).run s =
      PMF.pure ({ cfg with tapes := machine.runFrom cfg.tapes fuel }, s) := by
  change (OracleComp.interpret oracle
    (MultiTapeMachine.runConfigFrom _ _ _ _ _)).run s = _
  have htr : (ofDeterministic machine : MultiTapePTM k Symbol State Oracle).tr =
      fun state symbol work _ _ =>
        .step (machine.tr state symbol work) (fun _ => none) (fun _ => 0) := rfl
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      have hh : machine.runFrom cfg.tapes (fuel + 1) = cfg.tapes :=
        Function.iterate_fixed (MultiTapeTM.step_of_halt hs) _
      simp [MultiTapeMachine.runConfigFrom, hs, hh]
    | some state =>
      simp only [MultiTapeMachine.runConfigFrom, hs, htr, bind_map_left,
        OracleComp.interpret_bind, StateT.run_bind, hcoin,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
      rw [ih]
      congr 1
      simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply]
      rw [MultiTapeTM.step_of_state hs]
      simp [Config.step]

/-- The output of a deterministic embedding agrees with upstream and leaves private state intact. -/
theorem run_interpret_ofDeterministic [DecidableEq Oracle]
    (machine : MultiTapeTM k Symbol State) (coin : OracleComp spec Bool)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (oracle : (q : Query) → StateT OracleState PMF (spec q)) (coinLaw : PMF Bool)
    (hcoin : ∀ s, (OracleComp.interpret oracle coin).run s = coinLaw.map (fun bit => (bit, s)))
    (fuel : ℕ) (cfg : Config k Symbol State Oracle input) (s : OracleState) :
    (OracleComp.interpret oracle ((ofDeterministic machine).runFrom coin query fuel cfg)).run s =
      PMF.pure ((machine.runFrom cfg.tapes fuel).output, s) := by
  simp [runFrom, OracleComp.interpret_map, StateT.run_map,
    run_interpret_runConfigFrom_ofDeterministic machine coin query oracle coinLaw hcoin]

/-- Closed fair-coin execution of a deterministic embedding has a point-mass output distribution. -/
theorem eval_runClosed_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (fuel : ℕ) (input : List Symbol) :
    ProbComp.eval ((ofDeterministic machine).runClosed fuel input) =
      PMF.pure (machine.runFrom (machine.initCfg input) fuel).output := by
  have h := run_interpret_ofDeterministic machine (ProbComp.uniform Bool) Empty.elim
    (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
    (Probability.PMF.uniformOfFintype Bool)
    (fun s => by
      rw [OracleComp.run_interpret_stateless]
      exact congrArg (PMF.map (fun bit => (bit, s))) (ProbComp.eval_uniform Bool)) fuel
    ((ofDeterministic machine).initialConfig input) ()
  rw [OracleComp.run_interpret_stateless] at h
  have hout := congrArg (PMF.map Prod.fst) h
  rw [PMF.monad_map_eq_map, PMF.map_comp, PMF.pure_map] at hout
  change PMF.map id _ = _ at hout
  rw [PMF.map_id] at hout
  exact hout

end Turing.MultiTapePTM
