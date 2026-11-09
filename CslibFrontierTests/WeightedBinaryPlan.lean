/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Computability.PolyTime.CNF.WeightedPlan

/-! # Complete tagged binary counting-plan clients -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow
open Cslib.Logic.PL.WeightedRow.BinaryPlan Turing.MultiTapeTM

namespace WeightedBinaryPlanTests

example : compile 0 0 [] = .inl 1 := by decide
example : compile 0 1 [] = .inl 2 := by decide
example : compile 0 1 [([], 1)] = .inl 0 := by decide
example : compile 0 1 [([(0, true, 1)], 1)] = .inl 1 := by decide
example : compile 1 1 [([(0, true, 2)], 1)] = .inl 0 := by decide
example : compile 0 3 [([(0, true, 7), (0, false, 7)], 7)] = .inl 8 := by decide
example : compile 0 3 [([(0, true, 7), (0, false, 7)], 8)] = .inl 0 := by decide

/-- The 2^n answer is written in binary; no 2^n assignment list is built. -/
example : compile 0 80 [] = .inl (2 ^ 80) := by decide
example : (encOutput (compile 0 80 [])).length = 82 := by decide

example : compile 0 2 [([(0, true, 1)], 1), ([(1, true, 1)], 0)] = .inl 1 := by decide
example : compile 1 2 [([(0, true, 2)], 1), ([(1, true, 1)], 0)] = .inl 0 := by decide
example : compile 0 2 [([(0, true, 1)], 0), ([(0, true, 1)], 1)] = .inl 0 := by decide

/-- Positive deficient computed rank emits declarations and both exact ordinary CNFs. -/
def rows : List BinaryNormalization.Input :=
  [([(0, true, 1)], 1), ([(1, true, 1)], 1)]

example : compile 0 3 rows = .inr (4,
    ([[(1, true)], [(0, true)], [(3, false)], [(3, false)]],
      [[(1, true)], [(0, true)], [(3, false)], [(3, true)]])) := by decide

example : compile 0 2 [([(0, true, 2 ^ 80)], 2 ^ 80)] =
    .inr (2, ([[(0, true)]], [[(0, true)], []])) := by decide

/-- Test-only exhaustive interpretation of the small emitted formulas. -/
def queryOracle (N : ℕ) (q : CNF ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → Bool)).filter fun σ => q.eval (assignment σ)).card

/-- Test-only interpretation of either output constructor. -/
def runOracle : Output → ℕ
  | .inl a => a
  | .inr (N, (qf, qt)) => queryOracle N qf - queryOracle N qt

example : runOracle (compile 0 3 rows) = 2 := by decide
example : runOracle (compile 1 3 [([(0, true, 3), (0, false, 1), (1, true, 2)], 2)]) = 0 := by
  decide

/-- The same original equations in the reviewed finite input representation. -/
def source (j : Fin 2) : Occurrences 3 1 where
  var := fun _ => ⟨j, by omega⟩
  sign := fun _ => true
  weight := fun _ => 1
  positive := by decide
  target := 1

example : (compile 0 3 ((List.finRange 2).map fun j =>
    BinaryNormalization.ofOccurrences (source j))).count =
      Fintype.card {σ : Fin 3 → Bool // ∀ j, ((source j).value σ : ℤ) = (source j).target} :=
  compile_count source (by decide)

example : WithinBudget 3 0 (compile 0 3 ((List.finRange 2).map fun j =>
    BinaryNormalization.ofOccurrences (source j))) := compile_withinBudget source (by decide)

example : ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => compile 1 p.1 p.2)
    (encPair encUnary (encList BinaryNormalization.encInput)) encOutput := compile_polytime 1

end WeightedBinaryPlanTests
