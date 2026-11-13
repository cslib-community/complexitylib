/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.Rademacher.LinearL1
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogTwoPow

/-!
# Checks for ℓ₁-bounded linear predictors

Exercises `CslibFrontier.MachineLearning.Rademacher.LinearL1`:

* **Samples on the square:** for any `100` points of `[-1, 1]²` and `B = 1`, the ℓ₁ bound gives
  empirical Rademacher complexity below `1 / 5`, under the trivial bound `1`.
* **A population bound:** for `±1` features on `Bool`, `B = 2` and `m = 10000`, the Rademacher
  complexity is at most `2 √(2 log 2 / 10000) < 1 / 25`.
-/

public section

namespace CslibFrontierTests.LinearL1Predictors

open Cslib.MachineLearning Cslib.BitString

/-- Halving weights `(1/2, -1/2)` have ℓ₁ norm `1`. -/
example : (fun z : Fin 2 → ℝ => ![1 / 2, -1 / 2] ⬝ᵥ z) ∈ l1LinearPredictors id 1 :=
  mem_l1LinearPredictors.2 ⟨![1 / 2, -1 / 2], by norm_num [Fin.sum_univ_two], rfl⟩

/-- On any `100` points of the square `[-1, 1]²`, the ℓ₁ bound with `B = 1` is
`√(2 log 4 / 100)`, which is below `1 / 5`, well under the trivial bound `B R = 1`. -/
theorem empiricalRademacherComplexity_square_lt (S : Fin 100 → Fin 2 → ℝ)
    (hS : ∀ i j, |S i j| ≤ 1) :
    empiricalRademacherComplexity (l1LinearPredictors id 1) S < 1 / 5 := by
  refine lt_of_le_of_lt (empiricalRademacherComplexity_l1LinearPredictors_le id zero_le_one S hS)
    ?_
  rw [one_mul, one_mul, Real.sqrt_lt' (by norm_num), show ((2 : ℕ) : ℝ) = 2 by norm_num,
    show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_lt_one
  norm_num
  linarith

/-- `±1` features on `Bool`: `b ↦ (signVal b)`. -/
def signFeature (b : Bool) : Fin 1 → ℝ := fun _ => signVal b

/-- The population bound for `±1` features, `B = 2` and `m = 10000`. -/
theorem rademacherComplexity_signFeature_le (D : PMF Bool) :
    rademacherComplexity D (l1LinearPredictors signFeature 2) 10000 ≤
      2 * 1 * √(2 * Real.log (2 * (1 : ℕ)) / (10000 : ℕ)) :=
  rademacherComplexity_l1LinearPredictors_le D signFeature zero_le_two
    (fun b _ => by simp [signFeature]) 10000

theorem signFeature_bound_lt :
    2 * 1 * √(2 * Real.log (2 * (1 : ℕ)) / (10000 : ℕ)) < (1 / 25 : ℝ) := by
  have hs : √(2 * Real.log 2 / 10000) < 1 / 50 := by
    rw [Real.sqrt_lt' (by norm_num)]
    have := Real.log_two_lt_one
    linarith
  simp only [Nat.cast_one, mul_one, Nat.cast_ofNat]
  linarith

end CslibFrontierTests.LinearL1Predictors
