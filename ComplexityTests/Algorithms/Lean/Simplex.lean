/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Simplex.LinearProgram
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Worked examples for the simplex method with Bland's rule

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Algorithms.Lean.Simplex.Dictionary.simplex` over `ℚ`:

1. Chvátal's introductory example ([Chvatal1983], Chapter 2):
   `max 5x₁ + 4x₂ + 3x₃` subject to `2x₁ + 3x₂ + x₃ ≤ 5`, `4x₁ + x₂ + 2x₃ ≤ 11`,
   `3x₁ + 4x₂ + 2x₃ ≤ 8`, `x ≥ 0`. Bland's rule reaches the optimum `13` at `x = (2, 0, 1)` in two
   pivots, and `simplex_slackDictionary_spec` turns the run into the statement that `13` is the
   maximum. The dual certificate `y = (1, 0, 1)` read off the final dictionary is checked.
2. Chvátal's cycling example ([Chvatal1983], Chapter 3):
   `max 10x₁ - 57x₂ - 9x₃ - 24x₄` subject to
   `x₁/2 - 11x₂/2 - 5x₃/2 + 9x₄ ≤ 0`, `x₁/2 - 3x₂/2 - x₃/2 + x₄ ≤ 0`, `x₁ ≤ 1`, `x ≥ 0`. With
   Dantzig's largest-coefficient rule (ties broken toward the smallest index) the method returns to
   the initial basis after six degenerate pivots, so the hypothesis of
   `basis_ne_of_blandPivot` that the pivots follow Bland's rule cannot be dropped. Bland's rule
   instead reaches the optimum `1` after seven pivots.
3. Edge cases: an unbounded program, a program whose slack dictionary is already optimal, and a
   program with `b ≱ 0`, whose slack dictionary is infeasible, so it is outside the scope of
   `simplex_slackDictionary_spec`.
-/

public section

namespace ComplexityTests.Algorithms.Lean.Simplex

open Cslib.Algorithms.Lean.Simplex Dictionary Matrix Finset

/-- The final basis and objective value of an optimal run, if any. -/
def optimum? {ι K : Type*} : Outcome ι K → Option (Finset ι × K)
  | .optimal D => some (D.basis, D.objConst)
  | _ => none

/-- The final dictionary of an optimal run, if any. -/
def final? {ι K : Type*} : Outcome ι K → Option (Dictionary ι K)
  | .optimal D => some D
  | _ => none

/-- Whether a run stopped with an unbounded entering variable. -/
def isUnbounded {ι K : Type*} : Outcome ι K → Bool
  | .unbounded _ _ => true
  | _ => false

/-- Whether a run ran out of fuel. -/
def isOutOfFuel {ι K : Type*} : Outcome ι K → Bool
  | .outOfFuel _ => true
  | _ => false

/-! ### 1. Chvátal's introductory example -/

/-- The constraint matrix of Chvátal's introductory example. -/
def A₁ : Matrix (Fin 3) (Fin 3) ℚ := !![2, 3, 1; 4, 1, 2; 3, 4, 2]
/-- The right-hand side of Chvátal's introductory example. -/
def b₁ : Fin 3 → ℚ := ![5, 11, 8]
/-- The objective of Chvátal's introductory example. -/
def c₁ : Fin 3 → ℚ := ![5, 4, 3]

/-- The simplex method stops at the basis `{x₁, x₃, w₂}` with value `13`. -/
example : optimum? (slackDictionary A₁ b₁ c₁).simplex = some ({0, 2, 4}, 13) := by
  decide +kernel

/-- The optimal basic solution is `x = (2, 0, 1)` with slacks `w = (0, 1, 0)`. -/
example : (final? (slackDictionary A₁ b₁ c₁).simplex).map (·.basicSolution) =
    some ![2, 0, 1, 0, 1, 0] := by
  decide +kernel

/-- Bland's rule needs exactly two pivots here. -/
example : isOutOfFuel (run (slackDictionary A₁ b₁ c₁) 1) = true ∧
    optimum? (run (slackDictionary A₁ b₁ c₁) 2) = some ({0, 2, 4}, 13) := by
  decide +kernel

theorem b₁_nonneg : 0 ≤ b₁ := by
  intro i; fin_cases i <;> simp [b₁]

/-- The run certifies that `13` is the optimum of Chvátal's introductory example. -/
theorem isGreatest_chvatal : IsGreatest ((c₁ ⬝ᵥ ·) '' {x | A₁ *ᵥ x ≤ b₁ ∧ 0 ≤ x}) 13 := by
  have hrun : optimum? (slackDictionary A₁ b₁ c₁).simplex = some ({0, 2, 4}, 13) := by
    decide +kernel
  rcases simplex_slackDictionary_spec A₁ b₁ c₁ b₁_nonneg with
    ⟨D, hD, hgr, -⟩ | ⟨⟨D, s, hD⟩, -⟩
  · rw [hD] at hrun
    simp only [optimum?, Option.some.injEq, Prod.mk.injEq] at hrun
    rw [← hrun.2]
    exact hgr
  · rw [hD] at hrun
    simp only [optimum?, reduceCtorEq] at hrun

/-- The negated reduced costs of the slacks in the final dictionary are `(1, 0, 1)`, the dual
certificate of `exists_dual_of_simplex_slackDictionary_eq_optimal`. -/
example : (final? (slackDictionary A₁ b₁ c₁).simplex).map
    (fun D => fun i : Fin 3 => -D.objCoeff (Fin.natAdd 3 i)) = some ![1, 0, 1] := by
  decide +kernel

/-- The dual certificate is dual feasible with value `13`. -/
example : c₁ ≤ ![(1 : ℚ), 0, 1] ᵥ* A₁ ∧ ![(1 : ℚ), 0, 1] ⬝ᵥ b₁ = 13 := by
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k <;> norm_num [c₁, A₁, vecMul, dotProduct, Fin.sum_univ_succ]
  · norm_num [b₁, dotProduct, Fin.sum_univ_succ]

/-! ### 2. Chvátal's cycling example -/

/-- The constraint matrix of Chvátal's cycling example. -/
def A₂ : Matrix (Fin 3) (Fin 4) ℚ :=
  !![1/2, -11/2, -5/2, 9; 1/2, -3/2, -1/2, 1; 1, 0, 0, 0]
/-- The right-hand side of Chvátal's cycling example. -/
def b₂ : Fin 3 → ℚ := ![0, 0, 1]
/-- The objective of Chvátal's cycling example. -/
def c₂ : Fin 4 → ℚ := ![10, -57, -9, -24]

/-- Bland's rule reaches the optimum `1` at the basis `{x₁, x₃, w₁}`. -/
example : optimum? (slackDictionary A₂ b₂ c₂).simplex = some ({0, 2, 4}, 1) := by
  decide +kernel

/-- Bland's rule needs exactly seven pivots here. -/
example : isOutOfFuel (run (slackDictionary A₂ b₂ c₂) 6) = true ∧
    optimum? (run (slackDictionary A₂ b₂ c₂) 7) = some ({0, 2, 4}, 1) := by
  decide +kernel

/-- Dantzig's entering rule: the largest reduced cost, ties broken toward the smallest index. -/
def dantzigEntering {n : ℕ} (D : Dictionary (Fin n) ℚ) : Option (Fin n) :=
  minOpt (D.enteringCandidates.filter fun j =>
    ∀ k ∈ D.enteringCandidates, D.objCoeff k ≤ D.objCoeff j)

/-- One pivot with Dantzig's entering rule and the smallest-index ratio test. -/
def dantzigPivot {n : ℕ} (D : Dictionary (Fin n) ℚ) : Dictionary (Fin n) ℚ :=
  match dantzigEntering D with
  | none => D
  | some s =>
    match D.blandLeaving s with
    | none => D
    | some r => D.pivot r s

/-- Dantzig's rule cycles: six degenerate pivots lead back to the initial basis. -/
example : (List.range 7).map (fun k => (dantzigPivot^[k] (slackDictionary A₂ b₂ c₂)).basis) =
    [{4, 5, 6}, {0, 5, 6}, {0, 1, 6}, {1, 2, 6}, {2, 3, 6}, {3, 4, 6}, {4, 5, 6}] := by
  decide +kernel

/-- The cycle consists of degenerate pivots: the objective value stays `0`. -/
example : (List.range 7).map (fun k => (dantzigPivot^[k] (slackDictionary A₂ b₂ c₂)).objConst) =
    List.replicate 7 0 := by
  decide +kernel

/-! ### 3. Edge cases -/

/-- `max x` subject to `-x ≤ 1`, `x ≥ 0` is unbounded. -/
example : isUnbounded (slackDictionary !![(-1 : ℚ)] ![1] ![1]).simplex = true := by
  decide +kernel

/-- `max -x` subject to `x ≤ 1`, `x ≥ 0`: the slack dictionary is already optimal, with value
`0` and no pivot. -/
example : optimum? (run (slackDictionary !![(1 : ℚ)] ![1] ![-1]) 0) = some ({1}, 0) := by
  decide +kernel

/-- With `b = (-1)` the slack dictionary is infeasible, so `simplex_slackDictionary_spec` does
not apply; Phase I is not formalized. -/
example : ¬ (slackDictionary !![(1 : ℚ)] ![-1] ![1]).Feasible := by
  rw [feasible_slackDictionary_iff]
  intro h
  have := h 0
  norm_num at this

/-- The fuel bound of `simplex` on Chvátal's examples: `C(6, 3) - 1 = 19` and
`C(7, 3) - 1 = 34` pivots. -/
example : (Fintype.card (Fin (3 + 3))).choose #(slackDictionary A₁ b₁ c₁).basis - 1 = 19 ∧
    (Fintype.card (Fin (4 + 3))).choose #(slackDictionary A₂ b₂ c₂).basis - 1 = 34 := by
  decide +kernel

end ComplexityTests.Algorithms.Lean.Simplex
