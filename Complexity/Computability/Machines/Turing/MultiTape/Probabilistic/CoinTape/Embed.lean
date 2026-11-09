/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExtendTapes

/-!
# Saved coins and tape embeddings

The common tape embedding also preserves replay with a supplied coin sequence, including all
query effects and the data on unused tapes.

## Main results

* `Turing.MultiTapePTM.runConfigFromCoins_embed`: preserve the complete saved-coin program.
* `Turing.MultiTapePTM.runCoins_extendTapes`: unused scratch tapes do not affect replayed output.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k k' : ℕ} {Symbol State Oracle Query : Type} {spec : OracleSpec Query}
  {input : List Symbol} [DecidableEq Oracle]

/-- Reindexing preserves saved-coin replay, including all contents on additional tapes. -/
theorem runConfigFromCoins_embed (machine : MultiTapePTM k Symbol State Oracle)
    (e : Fin k ↪ Fin k') (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (cfg : Config k Symbol State Oracle input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (machine.extendTapes e).runConfigFromCoins query coins (cfg.embed e extraTapes extraPos) =
      (fun final => final.embed e extraTapes extraPos) <$>
        machine.runConfigFromCoins query coins cfg := by
  induction coins generalizing cfg with
  | nil => simp
  | cons bit coins ih =>
    rw [runConfigFromCoins_cons, runConfigFrom_embed]
    simp only [bind_map_left, ih, runConfigFromCoins_cons, map_bind]

/-- Blank scratch tapes preserve saved-coin replay's output and every oracle effect. -/
theorem runCoins_extendTapes (machine : MultiTapePTM k Symbol State Oracle)
    (e : Fin k ↪ Fin k') (query : Oracle → List Symbol → OracleComp spec (List Symbol))
    (coins : List Bool) (input : List Symbol) :
    (machine.extendTapes e).runCoins query coins input = machine.runCoins query coins input := by
  simp only [runCoins, runFromCoins, MultiTapeMachine.initialConfig_extendTapes,
    runConfigFromCoins_embed, Functor.map_map, Config.embed_output]

end Turing.MultiTapePTM
