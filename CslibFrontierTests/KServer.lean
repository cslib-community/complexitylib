/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.KServer.DoubleCoverage
public import CslibFrontier.DataStructure.KServer.LowerBound
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the `k`-server problem

Concrete Double Coverage runs, an explicit offline schedule, and instances of the
Manasse–McGeoch–Sleator lower bound and of the Chrobak–Karloff–Payne–Vishwanathan upper bound for
`CslibFrontier.DataStructure.KServer`.
-/

@[expose] public section

namespace ComplexityTests.KServer

open Cslib.DataStructure.Online Cslib.DataStructure.KServer

/-! ### Double Coverage steps -/

/-- An inner request: both neighbours move `4` toward `4`. -/
example : dcSorted ![(0 : Int), 10] 4 = ![4, 6] := by decide

/-- An outer request: only the leftmost server moves. -/
example : dcSorted ![(0 : Int), 10] (-3) = ![-3, 10] := by decide

/-- A request on a server costs nothing. -/
example : dcSorted ![(0 : Int), 10] 10 = ![0, 10] := by decide

/-- Coincident servers: only one of them moves to an outer request. -/
example : dcSorted ![(2 : Int), 2] 5 = ![2, 5] := by decide

/-! ### A concrete run with three servers -/

/-- Double Coverage from `0, 5, 10` on requests `7, 3, 7`. It moves to `0, 7, 8` (cost `4`), then
`3, 4, 8` (cost `6`), then `3, 5, 7` (cost `2`), for a total of `12`. -/
example : (doubleCoverage 2).cost ![0, 5, 10] [7, 3, 7] = 12 := by
  have h1 : dcStep ![0, 5, 10] 7 = ![0, 7, 8] := by rw [dcStep_of_monotone (by decide)]; decide
  have h2 : dcStep ![0, 7, 8] 3 = ![3, 4, 8] := by rw [dcStep_of_monotone (by decide)]; decide
  have h3 : dcStep ![3, 4, 8] 7 = ![3, 5, 7] := by rw [dcStep_of_monotone (by decide)]; decide
  rw [doubleCoverage_cost_cons, h1, doubleCoverage_cost_cons, h2, doubleCoverage_cost_cons, h3,
    doubleCoverage_cost_nil]
  decide

/-- An offline schedule for requests `7, 3, 7` from `0, 5, 10`. -/
def lineOffStates : List (Fin 3 → Int) := [![0, 5, 7], ![0, 3, 7], ![0, 3, 7]]

/-- An offline schedule for the same requests: move `10 → 7`, then `5 → 3`. -/
example : (problem NatMetric.line 3).ValidSchedule ![0, 5, 10] [7, 3, 7] lineOffStates :=
  ⟨by decide, by decide, by decide, trivial⟩

/-- The offline schedule costs `5`. -/
example : (problem NatMetric.line 3).scheduleCost ![0, 5, 10] [7, 3, 7] lineOffStates = 5 := by
  decide

/-- The additive constant `Σ_{i<j} |s₀ i - s₀ j|` of the competitive bound from `0, 5, 10`. -/
example : pairSum NatMetric.line ![(0 : Int), 5, 10] / 2 = 20 := by decide

/-- The competitive bound instantiated: `12 ≤ 3 * 5 + 20`. -/
example : (doubleCoverage 2).IsCompetitiveFrom ![0, 5, 10] 3 20 := by
  have h : pairSum NatMetric.line ![(0 : Int), 5, 10] / 2 = 20 := by decide
  rw [← h]
  exact doubleCoverage_isCompetitiveFrom _

/-! ### The lower bound -/

/-- Paging as `k`-server on the uniform metric: on three points no deterministic online
`2`-server strategy is `1`-competitive, whatever the additive constant. -/
example (A : DetStrategy (problem (NatMetric.uniform (Fin 3)) 2)) (b : Nat) :
    ¬ A.IsCompetitive 1 b :=
  not_isCompetitive_of_lt _ (s := id) Function.injective_id A (by omega) b

/-- Double Coverage's ratio `k = n + 1` is optimal on the line: from the distinct servers
`0, 1, …, n` it is not `n`-competitive, whatever the additive constant. -/
example (n b : Nat) :
    ¬ (doubleCoverage n).IsCompetitiveFrom (fun i => ((i : Nat) : Int)) n b :=
  not_isCompetitiveFrom_of_lt NatMetric.line (fun _ _ h => Fin.ext (Int.natCast_inj.1 h))
    (z := ((n + 1 : Nat) : Int)) (fun i h => by have := i.isLt; omega) _ (by omega) b

/-! ### The additive constant depends on the start -/

/-- Double Coverage from `0, 10` on requests `5, 0`: both servers meet at `5` (cost `10`), then
one moves to `0` (cost `5`). -/
example : (doubleCoverage 1).cost ![0, 10] [5, 0] = 15 := by
  have h1 : dcStep ![0, 10] 5 = ![5, 5] := by rw [dcStep_of_monotone (by decide)]; decide
  have h2 : dcStep ![5, 5] 0 = ![0, 5] := by rw [dcStep_of_monotone (by decide)]; decide
  rw [doubleCoverage_cost_cons, h1, doubleCoverage_cost_cons, h2, doubleCoverage_cost_nil]
  decide

/-- The offline schedule moving `10 → 5` serves the same requests at cost `5`. So from `0, 10`
the additive constant must be at least `15 - 2 * 5 = 5`. Scaling the instance by `L` gives `3L`
against `L`, so no single constant works for every start: Double Coverage is `k`-competitive with
the per-start constant `Σ_{i<j} |s₀ i - s₀ j|`, not uniformly (`IsCompetitive`). -/
example : ¬ (doubleCoverage 1).IsCompetitiveFrom ![0, 10] 2 4 := by
  intro h
  have hv : (problem NatMetric.line 2).ValidSchedule ![0, 10] [5, 0] [![0, 5], ![0, 5]] :=
    ⟨by decide, by decide, trivial⟩
  have hc : (problem NatMetric.line 2).scheduleCost ![0, 10] [5, 0] [![0, 5], ![0, 5]] = 5 := by
    decide
  have h1 : dcStep ![0, 10] 5 = ![5, 5] := by rw [dcStep_of_monotone (by decide)]; decide
  have h2 : dcStep ![5, 5] 0 = ![0, 5] := by rw [dcStep_of_monotone (by decide)]; decide
  have hd : (doubleCoverage 1).cost ![0, 10] [5, 0] = 15 := by
    rw [doubleCoverage_cost_cons, h1, doubleCoverage_cost_cons, h2, doubleCoverage_cost_nil]
    decide
  have := h [5, 0] [![0, 5], ![0, 5]] hv
  rw [hd, hc] at this
  omega

/-- The rational form: no ratio `p / q = 3 / 2 < 2` for two servers on the line. -/
example (A : DetStrategy (problem NatMetric.line 2)) (b : Nat) :
    ∃ reqs offStates, (problem NatMetric.line 2).ValidSchedule ![0, 1] reqs offStates ∧
      3 * (problem NatMetric.line 2).scheduleCost ![0, 1] reqs offStates + b <
        2 * A.cost ![0, 1] reqs :=
  exists_ratio_violation NatMetric.line (z := 2) (by decide) (by decide) A (by omega) b

end ComplexityTests.KServer
