/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.CountingParameterBounds
import Complexity.Computability.Complexity.Problems.SAT

/-! Concrete scheduled outputs, zero/low-width controls, a non-monotone schedule boundary,
and numerical growth charged to the complete context/unary-size/CNF encoding. -/

open Cslib.Complexity Cslib.Logic.PL Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT.ReplacementParams
open Cslib.Complexity.SubexponentialSAT.SparseCountingScale Turing.MultiTapeTM

/-- info: [(1, 512, 6148), (1, 512, 6148), (1, 512, 6148), (1, 512, 6148), (1, 512, 6148),
 (1, 512, 6148), (1, 512, 6148)] -/
#guard_msgs (whitespace := lax) in
#eval [0, 1, 2, 3, 4, 5, 20].map fun n =>
  let b := max 1 (numGroups n)
  let M := countingThresholdBase 3 b
  (b, M, countingDepthCoeff 3 M)

private theorem width_three_one : countingThresholdBase 3 1 = 512 :=
  countingThresholdBase_eq_two_pow (m := 9) (by decide) (by decide) (by decide) (by decide)

private theorem width_three_two : countingThresholdBase 3 2 = 1024 :=
  countingThresholdBase_eq_two_pow (m := 10) (by decide) (by decide) (by decide) (by decide)

-- The exported geometric estimate has a concrete positive client; positivity of M matters.
example : countingDepthCoeff 3 512 ≤ 8192 ∧
    ¬ countingDepthCoeff 3 0 ≤ countingBChoiceCoeff 3 * 0 ^ (3 - 2) := by
  constructor
  · exact countingDepthCoeff_le_mul_pow (by decide : 1 ≤ 512)
  · decide

-- One constant covers every size, including the positive coefficient at N = 0.
example : ∃ D : ℕ, 6148 ≤ D ∧ ∀ n : ℕ,
    countingDepthCoeff 3 (countingThresholdBase 3 (max 1 (numGroups n))) ≤
      D * (Nat.clog 2 n + 1) := by
  obtain ⟨D, hD⟩ := exists_countingDepthCoeff_numGroups_le_pow_clog (k := 3) (by decide)
  have hzero := hD 0
  norm_num [numGroups, width_three_one, countingDepthCoeff, Finset.sum_range_succ] at hzero
  refine ⟨D, hzero, fun n => ?_⟩
  simpa only [Nat.reduceSub, pow_one] using hD n

-- Omitting the additive one would make the all-N claim false at zero for every constant.
example (D : ℕ) : ¬ countingDepthCoeff 3
    (countingThresholdBase 3 (max 1 (numGroups 0))) ≤ D * Nat.clog 2 0 := by
  norm_num [numGroups, width_three_one, countingDepthCoeff, Finset.sum_range_succ]

-- Width two really has degree zero; widths zero and one have empty coefficient sums.
example (n : ℕ) :
    countingDepthCoeff 2 (countingThresholdBase 2 (max 1 (numGroups n))) = 4 ∧
    countingDepthCoeff 1 (countingThresholdBase 1 (max 1 (numGroups n))) = 0 ∧
    countingDepthCoeff 0 (countingThresholdBase 0 (max 1 (numGroups n))) = 0 := by
  simp [countingDepthCoeff]

-- Reuse the schedule's integer characterization at its downward jump. No monotonicity in N
-- is required by the uniform bound, and the selected base changes with the positive budget.
example :
    countingDepthCoeff 3 (countingThresholdBase 3 (max 1 (numGroups (2 ^ 524288)))) = 12292 ∧
    countingDepthCoeff 3 (countingThresholdBase 3 (max 1 (numGroups (2 ^ 524289)))) = 6148 := by
  have hfirst : numGroups (2 ^ 524288) = 2 := by
    apply (numGroups_eq_iff ?_).mpr <;> (rw [Nat.clog_pow 2 _ one_lt_two]; decide)
  have hnext : numGroups (2 ^ 524289) = 1 := by
    apply (numGroups_eq_iff ?_).mpr <;> (rw [Nat.clog_pow 2 _ one_lt_two]; decide)
  rw [hfirst, hnext]
  norm_num [width_three_one, width_three_two, countingDepthCoeff,
    Finset.sum_range_succ]

-- A size function that itself grows quadratically can be composed through the generic API.
example : ∃ c d : ℕ, 6148 ≤ c ∧ ∀ n : ℕ,
    countingDepthCoeff 3
      (countingThresholdBase 3 (max 1 (numGroups ((n + 1) ^ 2)))) ≤ c * (n + 1) ^ d := by
  have hN : PolyBounded id (fun n : ℕ => (n + 1) ^ 2) :=
    PolyBounded.of_forall_le 1 2 (fun _ => by simp)
  obtain ⟨c, d, h⟩ := (polyBounded_countingDepthCoeff_numGroups (k := 3) (by decide) hN).exists_le
  have hzero := h 0
  norm_num [numGroups, width_three_one, countingDepthCoeff, Finset.sum_range_succ] at hzero
  exact ⟨c, d, hzero, h⟩

-- The same polynomial covers all contexts, declared sizes and formulas. Empty formulas at
-- N = 0 and N = 3 have different full input lengths, despite identical occurring support.
example : ∃ c d : ℕ,
    (∀ x : Bool × ℕ × CNF ℕ,
      countingDepthCoeff 3 (countingThresholdBase 3 (max 1 (numGroups x.2.1))) ≤
        c * ((encPair encBool (encPair encUnary encCNF) x).length + 1) ^ d) ∧
    (encPair encBool (encPair encUnary encCNF) (true, 0, [])).length = 4 ∧
    (encPair encBool (encPair encUnary encCNF) (false, 3, [])).length = 10 := by
  obtain ⟨c, d, h⟩ :=
    (polyBounded_countingDepthCoeff_numGroups_encPair encBool encCNF (k := 3) (by decide)).exists_le
  exact ⟨c, d, h, by decide, by decide⟩
