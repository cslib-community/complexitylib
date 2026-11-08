/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.Complexity.FineGrained.WeightedCountingPlan
import ComplexityTests.WeightedBinaryPlan

/-! # Complete native counting-plan reconstruction and space clients -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow
open Cslib.Logic.PL.WeightedRow.BinaryPlan Turing.MultiTapeTM

namespace WeightedCountingPlanTests

/-- Test-only exhaustive counter for tiny declared formulas. -/
def tinyCounter (p : ℕ × CNF ℕ) : ℕ := WeightedBinaryPlanTests.queryOracle p.1 p.2

example : execute (fun _ => 999) (.inl (2 ^ 80)) = 2 ^ 80 := by decide
example : execute tinyCounter (.inr (3, ([], [[]]))) = 8 := by decide
example : execute tinyCounter (.inr (3, ([[(0, true)]], [[(0, true)], [(1, true)]]))) = 2 := by
  decide
example : execute tinyCounter (compile 0 3 WeightedBinaryPlanTests.rows) = 2 := by decide
example : execute tinyCounter (compile 0 2 [([(0, true, 1)], 0), ([(0, true, 1)], 1)]) = 0 := by
  decide
example : counterInput false (.inl 7) = (0, []) := by decide
example : counterInput true (.inr (4, ([[(1, true)]], [[(2, false)]]))) =
    (4, [[(2, false)]]) := by decide

example : queryCount 3 [[(0, true)]] = CNF.modelCountOn [[(0, true)]]
    (Finset.range 3) := queryCount_eq_modelCountOn _ _

/-- The existential native machine has a checked nonzero original-input instance. -/
example : ∃ count : ℕ × List BinaryNormalization.Input → ℕ,
    ComputableInPolySpace count
      (encPair encUnary (encList BinaryNormalization.encInput)) encNat ∧
    count (3, (List.finRange 2).map fun j =>
      BinaryNormalization.ofOccurrences (WeightedBinaryPlanTests.source j)) = 2 := by
  obtain ⟨count, hc, hs⟩ := exists_count_polySpace 0
  refine ⟨count, hc, ?_⟩
  rw [hs WeightedBinaryPlanTests.source (by decide)]
  decide

end WeightedCountingPlanTests
