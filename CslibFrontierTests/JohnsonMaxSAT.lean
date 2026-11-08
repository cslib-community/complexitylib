/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.Approximation.Johnson
import CslibFrontier.Foundations.BooleanAnalysis.GreedyFixing

/-! # Johnson's MAX-SAT algorithm and greedy rounds: checked examples

The generic greedy rule breaks ties toward `true`. Johnson's algorithm is run on the eight
clauses with all sign patterns on three variables, where every assignment falsifies exactly one
clause, so the `7 / 8` guarantee is tight; on a formula with an empty clause, where the
nonemptiness hypothesis of the `1 / 2` guarantee fails and the bound `2 * 1 ≤ 1` is false; and on
formulas with repeated literals and complementary pairs. The polynomial-time approximation
theorems are instantiated at the formula above.
-/

namespace ComplexityTests.JohnsonMaxSAT

open Cslib Cslib.Logic.PL Cslib.Complexity Cslib.PessimisticEstimator Turing.MultiTapeTM
open scoped BigOperators

/-! ### The greedy rule -/

-- Ties go to `true`; otherwise the smaller estimate wins.
example : greedyStep (fun (_ : Unit) b (_ : ℕ) => if b then 3 else 5) id 0 () = 3 := by decide
example : greedyStep (fun (_ : Unit) b (_ : ℕ) => if b then 5 else 3) id 0 () = 3 := by decide
example : greedyStep (fun (_ : Unit) b (_ : ℕ) => if b then 4 else 4) (fun _ => 0) 0 () = 4 := by
  decide

-- Greedy rounds over a list: each round adds `r` to the state if the estimate prefers it.
example : greedy (fun (r : ℕ) b (s : ℕ) => if b then s + r else s) (fun s => s % 3) [1, 2, 3] 0
    = 3 := by decide

/-! ### Greedy fixing on the cube -/

-- Fixing both coordinates of the cube `Fin 2 → Bool` by conditional expectations reaches a point
-- where the indicator of `x₀ ∧ x₁` is at least its mean `1 / 4`.
example : 𝔼 y : Fin 2 → Bool, (if y 0 && y 1 then (1 : ℝ) else 0) ≤
    (fun y : Fin 2 → Bool => if y 0 && y 1 then (1 : ℝ) else 0)
      (greedy BitString.fixCoord
        (fun s => -BitString.projectionAverage (fun y : Fin 2 → Bool =>
          if y 0 && y 1 then (1 : ℝ) else 0) s.2 s.1) [0, 1] (fun _ => false, fun _ => false)).1 :=
  BitString.expect_le_greedy_fixCoord _ [0, 1] (by decide) (by decide) _

/-! ### Johnson's algorithm -/

/-- All eight sign patterns on three variables: every assignment falsifies exactly one clause. -/
def allSigns : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)], [(0, false), (1, false), (2, false)]]

example : allSigns.IsExactThreeDistinct := by decide

-- Every round is a tie, so every variable is set to `true` (the output lists them in reverse
-- order), and the `7 / 8` bound is tight: `8 * 1 = 8`.
example : johnson allSigns = [2, 1, 0] := by decide
example : allSigns.countUnsat (johnsonAssignment allSigns) = 1 := by decide
example : 8 * allSigns.countUnsat (johnsonAssignment allSigns) ≤ allSigns.length :=
  CNF.IsExactThreeDistinct.eight_mul_countUnsat_johnsonAssignment_le (by decide)

-- Unit clauses: the first unit clause is satisfied, the opposing one falsified.
example : johnson ([[(0, true)], [(0, false)], [(0, true)]] : CNF ℕ) = [0] := by decide
example : CNF.countUnsat (johnsonAssignment ([[(0, true)], [(0, false)], [(0, true)]] : CNF ℕ))
    [[(0, true)], [(0, false)], [(0, true)]] = 1 := by decide

-- An empty clause is falsified by every assignment: here the `1 / 2` bound `2 * 1 ≤ 1` fails, so
-- the hypothesis that no clause is empty cannot be dropped.
example : CNF.countUnsat (johnsonAssignment ([[]] : CNF ℕ)) [[]] = 1 := by decide
example : ¬ 2 * CNF.countUnsat (johnsonAssignment ([[]] : CNF ℕ)) [[]] ≤ ([[]] : CNF ℕ).length := by
  decide

-- Repeated literals count once, and complementary pairs are always satisfied.
example :
    johnson ([[(0, false), (0, false)], [(0, true), (0, false)], [(1, true)]] : CNF ℕ) = [1] := by
  decide
example : CNF.countUnsat
    (johnsonAssignment ([[(0, false), (0, false)], [(0, true), (0, false)], [(1, true)]] : CNF ℕ))
    [[(0, false), (0, false)], [(0, true), (0, false)], [(1, true)]] = 0 := by decide

-- The empty formula.
example : johnson ([] : CNF ℕ) = [] := by decide

/-! ### Polynomial time -/

-- The polynomial-time `7 / 8` approximation, applied to `allSigns`.
example : ∃ A : CNF ℕ → List ℕ, ComputableInPolyTime A encCNF (encList encNat) ∧
    8 * allSigns.countUnsat (fun v => decide (v ∈ A allSigns)) ≤ allSigns.length := by
  obtain ⟨A, hA, hspec⟩ := exists_polyTime_maxExactThreeSAT_approx
  exact ⟨A, hA, (hspec allSigns (by decide)).1⟩

-- The certificate for an arbitrary variable encoding, at binary naturals.
example : ComputableInPolyTime (johnson (V := ℕ)) (encList (encList (encPair encNat encBool)))
    (encList encNat) :=
  computableInPolyTime_johnson encNat

end ComplexityTests.JohnsonMaxSAT
