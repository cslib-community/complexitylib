/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Karger.Contraction

/-!
# Karger's contraction algorithm on a triangle

The unit-weight triangle is a connected multigraph with minimum cut weight `2`. The tests evaluate
operations of the contraction structure on it, and instantiate the success bound `1 / 3`, the
one-sided error, admissibility and the call counts, so that none of their hypotheses is vacuous.
-/

@[expose] public section

namespace ComplexityTests.KargerContraction

open scoped ENNReal
open Cslib Cslib.WeightedCut Cslib.DataStructure Cslib.Algorithms.Lean.Karger

/-- The triangle with unit weights. -/
def triangle : Fin 3 → Fin 3 → ℕ := fun i j => if i = j then 0 else 1

theorem isMultigraph_triangle : IsMultigraph triangle := ⟨by decide, by decide⟩

/-- Every non-trivial cut of the triangle cuts two edges. -/
theorem minCut_triangle : 0 < minCut triangle :=
  (minCut_pos_iff (by simp) _).mpr (by unfold IsNonTrivialCut; decide)

/-- The size and the total doubled weight of the triangle. -/
example : (step ⟨3, triangle⟩ .size).2 = 3 ∧ (step ⟨3, triangle⟩ .total).2 = 6 := by decide

/-- The offsets `0` and `1` of the prefix sums sample the edges `(0, 1)` and `(0, 2)`. -/
example : sampledPair triangle 0 = (0, 1) ∧ sampledPair triangle 1 = (0, 2) :=
  ⟨sampledPair_eq (u := 0) (v := 1) (by decide), sampledPair_eq (u := 0) (v := 2) (by decide)⟩

/-- Karger's algorithm finds the minimum cut of the triangle with probability at least `1 / 3`. -/
example : (2 : ℝ≥0∞) / ((3 * (3 - 1) : ℕ) : ℝ≥0∞) ≤
    (spec.toRandomized.withCoins.run karger ⟨3, triangle⟩).toOuterMeasure
      {x | x.1 = minCut triangle} :=
  two_div_le_toOuterMeasure_karger (by norm_num) isMultigraph_triangle minCut_triangle

/-- Every answer is at least the minimum cut weight. -/
example {x : ℕ × Graph}
    (hx : x ∈ (spec.toRandomized.withCoins.run karger ⟨3, triangle⟩).support) :
    minCut triangle ≤ x.1 :=
  minCut_le_of_mem_support_karger (by norm_num) isMultigraph_triangle hx

/-- Every call is admissible. -/
example : spec.toRandomized.withCoins.toSpec.DemonicValid ⟨3, triangle⟩ karger :=
  demonicValid_karger (by norm_num) isMultigraph_triangle

/-- One contraction makes at most five calls, one of them a coin. -/
example : OracleComp.IsQueryBounded (contractTimes 1) 5 :=
  isCostBounded_contractTimes (a := 1) (b := 1) (fun _ => le_rfl) (fun _ => le_rfl) 1

example : OracleComp.IsCostBounded (fun q => Sum.elim (fun _ => 1) (fun _ => 0) q)
    (contractTimes 1) 1 :=
  isCostBounded_contractTimes (a := 1) (b := 0) (fun _ => le_rfl) (fun _ => le_rfl) 1

end ComplexityTests.KargerContraction
