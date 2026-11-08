/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Problems.LinearProgramming
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for rational LP feasibility in `NP ∩ coNP`

Concrete systems for the certificate checks. The system `2 x ≤ 1, -2 x ≤ -1` is feasible only at
`x = 1 / 2`, so it has no integer solution but `check` accepts the scaled witness `(2, [1])`. The
system `x ≤ 0, -x ≤ -1` is infeasible and `certCheck` accepts the Farkas certificate `[1, 1]`. A
nonpositive denominator, a certificate with positive right-hand side, and a certificate whose
combination does not vanish are rejected. The empty system is feasible, and a row with no
coefficients and a negative bound is infeasible. The basic-solution bound is instantiated on
`2 x = 1`, whose solution needs the denominator `2`, within the bound
`1! * (1 * 2 ^ 2 + 1) ^ 1 = 5`.
-/

@[expose] public section

namespace Cslib.Complexity.LinearProgrammingTests

open Matrix LPFeasibility Turing.MultiTapeTM
open Mathlib.Tactic.Matrix

/-! ### Feasible systems and the `NP` check -/

/-- `2 x ≤ 1` and `-2 x ≤ -1`. -/
abbrev half : List (List ℤ × ℤ) := [([2], 1), ([-2], -1)]

/-- The scaled witness `w / d = 1 / 2` is accepted. -/
theorem check_half : check (half, (2, [1])) = true := by
  simp [check, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- Hence the system is feasible. -/
theorem half_mem : half ∈ LPFeasibility := mem_of_check check_half

/-- A nonpositive denominator is rejected even when `w / d` would solve the system. -/
example : check (half, (-2, [-1])) = false := by
  simp [check, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- An integer candidate that violates a row is rejected. -/
example : check (half, (1, [1])) = false := by
  simp [check, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- The system has no integer solution, so a nontrivial denominator is needed. -/
example : ¬∃ x : ℤ, 2 * x ≤ 1 ∧ -2 * x ≤ -1 := by
  rintro ⟨x, h1, h2⟩
  omega

/-- The empty system is feasible. -/
example : ([] : List (List ℤ × ℤ)) ∈ LPFeasibility := ⟨0, by simp⟩

/-! ### Infeasible systems and the `coNP` check -/

/-- `x ≤ 0` and `-x ≤ -1`. -/
abbrev contra : List (List ℤ × ℤ) := [([1], 0), ([-1], -1)]

/-- The Farkas certificate `[1, 1]`: the rows add up to `0 ≤ -1`. -/
theorem certCheck_contra : certCheck (contra, [1, 1]) = true := by
  simp [certCheck, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- Hence the system is infeasible. -/
example : contra ∉ LPFeasibility := notMem_of_certCheck certCheck_contra

/-- A certificate whose combination of the right-hand sides is not negative is rejected. -/
example : certCheck (contra, [1, 0]) = false := by
  simp [certCheck, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- A certificate whose combination of the coefficients does not vanish is rejected. -/
example : certCheck (contra, [2, 1]) = false := by
  simp [certCheck, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- A negative multiplier is rejected. -/
example : certCheck (contra, [-1, 1]) = false := by
  simp [certCheck, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero]

/-- A row with no coefficients and a negative bound reads `0 ≤ -1`. -/
example : [([], -1)] ∉ LPFeasibility := notMem_of_certCheck (q := [1]) (by
  simp [certCheck, ListMatrix.dotProduct_add_one, ListMatrix.dotProduct_zero])

/-- No certificate is accepted for a feasible system. -/
example (q : List ℤ) : certCheck (half, q) = false := by
  cases h : certCheck (half, q)
  · rfl
  · exact absurd half_mem (notMem_of_certCheck h)

/-- The matrix form of `contra`. -/
example : matrix contra 1 = !![1; -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ### The basic-solution bound -/

/-- `2 x = 1` has the nonnegative rational solution `1 / 2`; the bound produces `p / d` with
`d ≤ 1! * (1 * 2 ^ 2 + 1) ^ 1 = 5`. -/
example : ∃ (d : ℤ) (p : Fin 1 → ℤ), 0 < d ∧ 0 ≤ p ∧ !![(2 : ℤ)] *ᵥ p = d • ![1] ∧
    d ≤ 5 ∧ ∀ j, p j ≤ 5 := by
  obtain ⟨d, p, hd, hp, hAp, hdN, hpN⟩ := exists_int_nonneg_mulVec_eq (B := 2)
    (A := !![(2 : ℤ)]) (b := ![1]) (by decide) (by decide) (x := ![(1 / 2 : ℚ)])
    (by intro j; fin_cases j; norm_num)
    (by ext i; fin_cases i; simp [mulVec, dotProduct])
  exact ⟨d, p, hd, hp, hAp, by simpa using hdN, fun j => by simpa using hpN j⟩

/-! ### The complexity statement -/

example : LPFeasibility ∈ NP (encList (encPair (encList encIntBin) encIntBin)) ∩
    coNP (encList (encPair (encList encIntBin) encIntBin)) :=
  mem_NP_inter_coNP

end Cslib.Complexity.LinearProgrammingTests
