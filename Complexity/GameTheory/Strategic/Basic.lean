/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Strategic games in cost-minimization form

A strategic (normal-form) game has a set of players `ι`, a strategy set `S i` for each player
`i`, and a cost `cost i s : ℝ` for each player at each strategy profile `s : ∀ i, S i`. Players
minimize cost, as in [Roughgarden2015], Section 2.1; a payoff-maximization game with utilities
`u i` is the cost game with costs `-u i`. A unilateral deviation of player `i` to the strategy
`a` turns the profile `s` into `Function.update s i a`, which is the profile written
`(y⁻ⁱ, a)` or `(a, s₋ᵢ)` in the literature.

## Main definitions

* `Cslib.GameTheory.CostGame`: a strategic game with real-valued player costs.
* `Cslib.GameTheory.CostGame.IsPureNash`: no player can strictly lower its cost by a unilateral
  deviation.
* `Cslib.GameTheory.CostGame.Improves`: `G.Improves t s` says that `t` arises from `s` by a
  unilateral deviation that strictly lowers the deviating player's cost (an improvement step of
  better-response dynamics, [MondererShapley1996], Section 2).
* `Cslib.GameTheory.CostGame.socialCost`: the sum of the players' costs.

## Main results

* `Cslib.GameTheory.CostGame.isPureNash_iff_forall_not_improves`: the pure Nash equilibria are
  exactly the profiles from which no improvement step is possible.

## References

* [MondererShapley1996]
* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory

/-- A strategic game in **cost-minimization form**: player `i` chooses a strategy in `S i`, and
`cost i s` is the cost of player `i` at the strategy profile `s : ∀ i, S i`. -/
structure CostGame (ι : Type*) (S : ι → Type*) where
  /-- The cost of player `i` at the profile `s`. -/
  cost : ι → (∀ i, S i) → ℝ

namespace CostGame

variable {ι : Type*} {S : ι → Type*} (G : CostGame ι S)

section Deviation

variable [DecidableEq ι]

/-- A profile `s` is a **pure Nash equilibrium** if no player can strictly decrease its cost by a
unilateral deviation: `cost i s ≤ cost i (update s i a)` for every player `i` and strategy `a`.
-/
@[expose] def IsPureNash (s : ∀ i, S i) : Prop :=
  ∀ i (a : S i), G.cost i s ≤ G.cost i (Function.update s i a)

/-- `G.Improves t s`: the profile `t` arises from `s` by a unilateral deviation of some player
that strictly decreases that player's cost. This is one step of better-response dynamics. The
argument order makes `WellFounded G.Improves` say that there is no infinite improvement path. -/
@[expose] def Improves (t s : ∀ i, S i) : Prop :=
  ∃ i, ∃ a : S i, t = Function.update s i a ∧ G.cost i t < G.cost i s

theorem isPureNash_iff_forall_not_improves {s : ∀ i, S i} :
    G.IsPureNash s ↔ ∀ t, ¬ G.Improves t s := by
  constructor
  · rintro h t ⟨i, a, rfl, hlt⟩
    exact (h i a).not_gt hlt
  · intro h i a
    by_contra hlt
    exact h _ ⟨i, a, rfl, lt_of_not_ge hlt⟩

end Deviation

/-- The **social cost** of a profile: the sum `∑ i, cost i s` of all players' costs. -/
@[expose] def socialCost [Fintype ι] (s : ∀ i, S i) : ℝ :=
  ∑ i, G.cost i s

end CostGame

end Cslib.GameTheory
