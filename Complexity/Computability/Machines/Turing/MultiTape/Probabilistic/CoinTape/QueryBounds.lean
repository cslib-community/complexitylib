/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Complexity.Languages.Probabilistic.QueryCount

/-!
# Query budgets for saved coins

Each saved coin executes at most one external query. The bounds hold for every supplied tape,
including tapes outside any intended sampling law, and for arbitrary oracle replies.

## Main results

* `Turing.MultiTapePTM.isCostBounded_runCoins`: a per-query cost bound gives a replay budget.

## References

Original structural bounds for the existing saved-coin interpreter.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol Control Operation Query : Type} [DecidableEq Operation]
  {spec : OracleSpec Query} {cost : Query → ℕ}

/-- Replaying a fixed tape charges at most one query-handler budget per coin. -/
theorem isCostBounded_runConfigFromCoins (machine : MultiTapePTM k Symbol Control Operation)
    (query : Operation → List Symbol → OracleComp spec (List Symbol)) (budget : ℕ)
    (hquery : ∀ op word, OracleComp.IsCostBounded cost (query op word) budget)
    (coins : List Bool) {input : List Symbol} (cfg : Config k Symbol Control Operation input) :
    OracleComp.IsCostBounded cost (machine.runConfigFromCoins query coins cfg)
      (coins.length * budget) := by
  induction coins generalizing cfg with
  | nil => simpa only [runConfigFromCoins_nil, List.length_nil, Nat.zero_mul] using
      (OracleComp.IsCostBounded.pure (cost := cost) cfg 0)
  | cons bit coins ih =>
    rw [runConfigFromCoins_cons]
    have hone : OracleComp.IsCostBounded cost
        (machine.runConfigFrom (pure bit) query 1 cfg) budget := by
      cases hs : cfg.tapes.state with
      | none =>
        simpa only [runConfigFrom, MultiTapeMachine.runConfigFrom, hs] using
          (OracleComp.IsCostBounded.pure (cost := cost) cfg budget)
      | some state =>
        simp only [runConfigFrom, MultiTapeMachine.runConfigFrom, hs, map_pure, pure_bind]
        cases machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
            cfg.answerSymbols bit with
        | step action symbol move => exact .pure _ budget
        | query op next =>
          simpa only [Nat.add_zero] using
            (hquery op _).bind (fun answer => OracleComp.IsCostBounded.pure _ 0)
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hone.bind ih

/-- Observing the replay output does not add queries. -/
theorem isCostBounded_runCoins (machine : MultiTapePTM k Symbol Control Operation)
    (query : Operation → List Symbol → OracleComp spec (List Symbol)) (budget : ℕ)
    (hquery : ∀ op word, OracleComp.IsCostBounded cost (query op word) budget)
    (coins : List Bool) (input : List Symbol) :
    OracleComp.IsCostBounded cost (machine.runCoins query coins input)
      (coins.length * budget) := by
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (machine.isCostBounded_runConfigFromCoins query budget hquery coins _)

end Turing.MultiTapePTM
