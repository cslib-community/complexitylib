/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Notation
public import CslibFrontier.Probability.ApproxEq

/-!
# Game hops as a `calc` chain

A game-hopping proof moves from one game to the next, and each hop changes the success probability
by at most its loss. Here the hops are steps of `x ≈[ε] y` on success probabilities, so a hop
sequence is a `calc` block that names each game and each loss:
```
calc Pr[G₀] = Pr[G₁] := by rw [h₀₁]                       -- equal distributions
  _ ≈[ε₁] Pr[G₂] := Game.approxEq_of_advantage_le h₁₂     -- an advantage bound
  _ ≈[ε₂] Pr[G₃] := h₂₃                                   -- `|Pr[G₂] - Pr[G₃]| ≤ ε₂`
```
`Game.advantage_le_of_approxEq` then closes an `ℝ≥0` advantage bound with the chain, and
`Game.approxEq_iff_advantage_le` reads a real advantage bound as a hop and back.

The same lemmas apply to experiments, which are programs `e : ProbComp Bool`: `Pr[e]` is
`Pr[ProbComp.eval e]` and the advantage between experiments is the advantage between their
distributions, so `Game.approxEq_of_advantage_le` takes an experiment advantage bound and gives
`Pr[e₀] ≈[ε] Pr[e₁]`.

Use `calc` when the hop sequence is the argument a reader should follow; the `game_trans` tactic
remains the tool for chains whose hops are proved in place.

## Main results

* `Cslib.Crypto.Game.approxEq_iff_advantage_le`: a hop of error `ε` is a real advantage bound.
* `Cslib.Crypto.Game.approxEq_of_advantage_le`: an `ℝ≥0` advantage bound is a hop.
* `Cslib.Crypto.Game.approxEq_advantage`: a hop costs at most its advantage.
* `Cslib.Crypto.Game.advantage_le_of_approxEq`: a chain bounds the advantage between its ends.
-/

public section

namespace Cslib.Crypto.Game

open Probability
open scoped NNReal

variable {G₀ G₁ : Game}

/-- A hop of error `ε` between two games is a bound of `ε` on their advantage. -/
theorem approxEq_iff_advantage_le {ε : ℝ} :
    Pr[G₀] ≈[ε] Pr[G₁] ↔ (advantage G₀ G₁ : ℝ) ≤ ε := by
  rw [coe_advantage]
  rfl

/-- An advantage bound is a hop. -/
theorem approxEq_of_advantage_le {ε : ℝ≥0} (h : advantage G₀ G₁ ≤ ε) :
    Pr[G₀] ≈[ε] Pr[G₁] :=
  approxEq_iff_advantage_le.mpr (NNReal.coe_le_coe.mpr h)

/-- A hop costs at most the advantage between its games. -/
theorem approxEq_advantage (G₀ G₁ : Game) : Pr[G₀] ≈[advantage G₀ G₁] Pr[G₁] :=
  approxEq_of_advantage_le le_rfl

/-- A chain of hops whose total error is at most `ε` bounds the advantage between its ends by
`ε`. The bound `hδ` defaults to a cast check, which proves it when `ε` is the chain's sum of
errors. -/
theorem advantage_le_of_approxEq {δ : ℝ} {ε : ℝ≥0} (h : Pr[G₀] ≈[δ] Pr[G₁])
    (hδ : δ ≤ ε := by exact_mod_cast le_rfl) :
    advantage G₀ G₁ ≤ ε :=
  NNReal.coe_le_coe.mp ((approxEq_iff_advantage_le.mp h).trans hδ)

end Cslib.Crypto.Game
