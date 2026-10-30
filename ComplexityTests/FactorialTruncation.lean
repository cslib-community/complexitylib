/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.LinearAlgebra.Matrix.FactorialTruncation

/-!
# Tests for factorial truncation of cutoff corrections
-/

namespace ComplexityTests.FactorialTruncation

open Matrix

/-- A walk on three time layers: from `0` to `1` and from `1` to `2`, each with probability
`1 / 2`. Its entries are at most `f = 1 / 2`. -/
private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

/-- The hard cutoff `t ↦ max (t - θ f) 0` with `θ = 1 / 4`, `f = 1 / 2`: it leaves exactly `1 / 8`
behind. It is monotone and `1`-Lipschitz. -/
private noncomputable def φ : Fin 3 → ℝ → ℝ := fun _ t => max (t - 1 / 8) 0

private theorem hC : C.IsStrictUpperTriangular := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [C]

private theorem hC0 : ∀ x y, 0 ≤ C x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hCf : ∀ x y, C x y ≤ 1 / 2 := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hC1 : C *ᵥ 1 ≤ 1 := by
  intro x; fin_cases x <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

private theorem hφ0 : ∀ y t, 0 ≤ φ y t := fun _ _ => le_max_right _ _

private theorem hφθ : ∀ y t, φ y t ≤ max (t - 1 / 4 * (1 / 2)) 0 := fun _ t => by
  norm_num [φ]

private theorem hφm : ∀ y, Monotone (φ y) := fun _ _ _ h => max_le_max (by linarith) le_rfl

private theorem hφL : ∀ y s t, s ≤ t → φ y t - φ y s ≤ 1 * (t - s) := fun _ s t _ => by
  simp only [φ, one_mul]
  have := le_max_left (s - 1 / 8) 0
  have := le_max_right (s - 1 / 8) 0
  have : max (t - 1 / 8) 0 ≤ max (s - 1 / 8) 0 + (t - s) := max_le (by linarith) (by linarith)
  linarith

/-- The cutoff correction of `C`, computed by hand: `φ (1 / 2) = 3 / 8` on both transitions,
and `φ (3 / 8 * 1 / 2) = 1 / 16` on the corrected two-step entry. -/
private noncomputable def Estar : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 3 / 8, 1 / 16; 0, 0, 3 / 8; 0, 0, 0]

-- `Estar` solves the recursion, so it is the cutoff correction.
private theorem Estar_eq : Estar = cutoffCorrectionFix φ C := by
  refine eq_cutoffCorrectionFix hC ?_
  ext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [cutoffCorrection, φ, C, Estar, Matrix.mul_apply, Fin.sum_univ_three]

-- One iteration from zero misses the two-step entry entirely.
example : cutoffCorrectionIter φ C 1 0 2 = 0 := by
  norm_num [cutoffCorrectionIter, cutoffCorrection, φ, C]

-- The truncation error after one iteration, `1 / 16`, is within the factorial bound.
example : cutoffCorrectionFix φ C 0 2 - cutoffCorrectionIter φ C 1 0 2 ≤
    1 / 2 * Real.exp (1 / (1 / 4)) * (1 / (1 / 4)) ^ 1 / (Nat.factorial 1) :=
  cutoffCorrectionFix_sub_iter_le hC hC0 hCf hC1 hφ0 hφθ hφm hφL (by norm_num) (by norm_num)
    (by norm_num) 1 0 2

-- After two iterations the iterate has reached the fixed point at `(0, 2)`.
example : cutoffCorrectionIter φ C 2 0 2 = cutoffCorrectionFix φ C 0 2 := by
  rw [← Estar_eq]
  norm_num [cutoffCorrectionIter, cutoffCorrection, φ, C, Estar, Matrix.mul_apply,
    Fin.sum_univ_three]

-- The corrected matrix of every iterate is nonnegative, and the hard cutoff leaves at most
-- `θ f = 1 / 8` behind in every column.
example (k : ℕ) (x y : Fin 3) :
    0 ≤ (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y :=
  cutoffCorrection_residual_nonneg hC0 hφ0 hφθ hφm (by norm_num) k x y

example (k : ℕ) (x y : Fin 3) :
    (C - cutoffCorrectionIter φ C k + cutoffCorrectionIter φ C k * C) x y ≤
      1 / 4 * (1 / 2) + 1 / 2 * Real.exp (1 / (1 / 4)) * (1 / (1 / 4)) ^ k / k.factorial :=
  cutoffCorrection_residual_le hC hC0 hCf hC1 hφ0 hφθ hφm hφL (by norm_num) (by norm_num)
    (by norm_num) (fun t => by norm_num [φ]) k x

-- A fixed number of iterations gets within `1 / 100` of the factorial bound's limit.
example : ∃ k : ℕ, Real.exp (1 / (1 / 4)) * (1 / (1 / 4)) ^ k / k.factorial ≤ 1 / 100 :=
  exists_factorial_bound_le _ _ (by norm_num)

end ComplexityTests.FactorialTruncation
