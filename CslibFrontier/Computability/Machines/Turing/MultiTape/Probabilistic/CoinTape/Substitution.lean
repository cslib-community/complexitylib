/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape

/-!
# Substituting external calls in saved-coin replay

Replacing the source machine's query programs commutes with replay as an equality of free
programs. The fixed private tape and all effects of the substituted external calls are retained.

## Main results

* `Turing.MultiTapePTM.interpret_runCoins`: substitution commutes with saved-coin execution.

## References

Original consequences of the shared interpreter's substitution law.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Replacing external calls commutes with fixed-coin replay, without changing the coin tape. -/
theorem interpret_runConfigFromCoins_substitute {Query' : Type}
    {target : OracleSpec Query'} (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (handler : (q : Query) → OracleComp target (spec q)) (coins : List Bool)
    (cfg : Config k Symbol State Oracle input) :
    OracleComp.interpret handler (machine.runConfigFromCoins query coins cfg) =
      machine.runConfigFromCoins (fun op word => OracleComp.interpret handler (query op word))
        coins cfg := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons bit coins ih =>
    simp only [runConfigFromCoins_cons, OracleComp.interpret_bind, runConfigFrom,
      MultiTapeMachine.interpret_runConfigFrom, OracleComp.interpret_map,
      OracleComp.interpret_pure, ih]

/-- Substituting external calls preserves the output and all effects of fixed-coin replay. -/
theorem interpret_runCoins {Query' : Type} {target : OracleSpec Query'}
    (machine : MultiTapePTM k Symbol State Oracle)
    (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (handler : (q : Query) → OracleComp target (spec q)) (coins : List Bool)
    (input : List Symbol) :
    OracleComp.interpret handler (machine.runCoins query coins input) =
      machine.runCoins (fun op word => OracleComp.interpret handler (query op word))
        coins input := by
  simp only [runCoins, runFromCoins, OracleComp.interpret_map,
    interpret_runConfigFromCoins_substitute]

end Turing.MultiTapePTM
