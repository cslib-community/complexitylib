/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Fourier–Motzkin elimination, Farkas' lemma and LP duality

Concrete systems over `ℚ`. The infeasible system `x ≤ 0, -x ≤ -1` has the Farkas certificate
`(1, 1)`, and Fourier–Motzkin elimination of `x` produces the contradictory row `0 ≤ -1`. The
feasible system `x ≤ 1, -x ≤ 0` has no Farkas certificate. With no constraints every system is
feasible. The program `max x₀ + x₁` subject to `x₀ ≤ 1, x₁ ≤ 2` has value `3`, attained by both
programs, and complementary slackness identifies its optimal pairs. The program `max x` subject to
`-x ≤ 0` is unbounded and its dual is infeasible. The canonical program
`max 2 x₀ + x₁` subject to `x₀ + 2 x₁ ≤ 4`, `3 x₀ + x₁ ≤ 6`, `x ≥ 0` has value `22 / 5`.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.LinearProgrammingTests

open Matrix

/-! ### Fourier–Motzkin elimination -/

/-- Eliminating `t` from `t ≤ 0, -t ≤ -1` leaves the row `0 ≤ -1` for the pair `(0, 1)`, so the
system is infeasible. -/
example : ¬∃ t : ℚ, t • ![(1 : ℚ), -1] + 0 ≤ ![0, -1] := by
  rw [FourierMotzkin.exists_smul_add_le_iff]
  intro h
  have := h (.inr (⟨0, by norm_num⟩, ⟨1, by norm_num⟩))
  rw [FourierMotzkin.combination_mulVec_inr, FourierMotzkin.combination_mulVec_inr] at this
  norm_num at this

/-- Eliminating `t` from `t ≤ 1, -t ≤ 0` leaves only consistent rows. -/
example : ∃ t : ℚ, t • ![(1 : ℚ), -1] + 0 ≤ ![1, 0] :=
  ⟨0, by intro i; fin_cases i <;> simp⟩

/-! ### Farkas' lemma -/

/-- `x ≤ 0, -x ≤ -1` is infeasible, certified by `(1, 1)`. -/
example : ¬∃ x : Fin 1 → ℚ, !![1; -1] *ᵥ x ≤ ![0, -1] := by
  rw [not_exists_mulVec_le_iff]
  refine ⟨![1, 1], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · funext j
    fin_cases j
    simp [vecMul, dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]

/-- `x ≤ 1, -x ≤ 0` is feasible, so it has no Farkas certificate. -/
example : ¬∃ y : Fin 2 → ℚ, 0 ≤ y ∧ y ᵥ* !![1; -1] = 0 ∧ y ⬝ᵥ ![1, 0] < 0 := by
  rw [← not_exists_mulVec_le_iff, not_not]
  refine ⟨![0], fun i => ?_⟩
  fin_cases i <;> simp

/-- With no constraints, every right-hand side is feasible. -/
example (b : Fin 0 → ℚ) : ∃ x : Fin 2 → ℚ, (0 : Matrix (Fin 0) (Fin 2) ℚ) *ᵥ x ≤ b :=
  (exists_mulVec_le_iff _ b).2 fun y _ _ => by simp [dotProduct]

/-- `x₀ - x₁ = -1, x₁ = 0` has no nonnegative solution: `y = (1, 1)` has `y ᵥ* A = (1, 0) ≥ 0`
and `y ⬝ᵥ b = -1 < 0`. -/
example : ¬∃ x : Fin 2 → ℚ, 0 ≤ x ∧ !![1, -1; 0, 1] *ᵥ x = ![-1, 0] := by
  rw [not_exists_nonneg_mulVec_eq_iff]
  refine ⟨![1, 1], fun j => ?_, ?_⟩
  · fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]

/-! ### Linear-programming duality -/

/-- The constraint matrix of the box program `max x₀ + x₁` subject to `x₀ ≤ 1, x₁ ≤ 2`, whose
dual is `min y₀ + 2 y₁` subject to `y ≥ 0, y = (1, 1)`. -/
abbrev boxA : Matrix (Fin 2) (Fin 2) ℚ := 1

/-- The optimal value of the box program is `3`, by strong duality. -/
example :
    IsGreatest ((![1, 1] ⬝ᵥ ·) '' {x | boxA *ᵥ x ≤ ![1, 2]}) 3 ∧
      IsLeast ((· ⬝ᵥ ![1, 2]) '' {y | 0 ≤ y ∧ y ᵥ* boxA = ![1, 1]}) 3 := by
  have hP : ∃ x, boxA *ᵥ x ≤ ![1, 2] := ⟨![1, 2], by simp [boxA]⟩
  have hD : ∃ y, 0 ≤ y ∧ y ᵥ* boxA = ![1, 1] :=
    ⟨![1, 1], fun i => by fin_cases i <;> simp, by simp [boxA]⟩
  obtain ⟨v, hmax, hmin⟩ := exists_isGreatest_isLeast_dotProduct boxA ![1, 2] ![1, 1] hP hD
  have hv : v = 3 := by
    obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hmin.1
    simp only [boxA, vecMul_one] at hy
    subst hy
    norm_num [dotProduct, Fin.sum_univ_two]
  subst hv
  exact ⟨hmax, hmin⟩

/-- Complementary slackness: `x = (1, 0)` is not optimal for the box program, since the dual
solution `(1, 1)` has a nonzero entry on the slack constraint `x₁ ≤ 2`. -/
example : ![1, 1] ⬝ᵥ ![(1 : ℚ), 0] ≠ ![1, 1] ⬝ᵥ ![1, 2] := by
  rw [Ne, dotProduct_eq_dotProduct_iff_of_mulVec_le (A := boxA)
    (fun i => by fin_cases i <;> simp [boxA]) (fun i => by fin_cases i <;> simp) (by simp [boxA])]
  intro h
  rcases h 1 with h | h <;> simp [boxA] at h

/-- `max x` subject to `-x ≤ 0` is unbounded, since its dual `y ≥ 0, -y = 1` is infeasible. -/
example : ¬BddAbove ((![1] ⬝ᵥ ·) '' {x : Fin 1 → ℚ | !![-1] *ᵥ x ≤ ![0]}) := by
  rw [bddAbove_image_dotProduct_iff _ _ _ ⟨0, fun i => by fin_cases i; simp⟩]
  rintro ⟨y, hy, hyA⟩
  have h0 := congr_fun hyA 0
  simp [vecMul, dotProduct] at h0
  linarith [show (0 : ℚ) ≤ y 0 from hy 0]

/-- The canonical program `max 2 x₀ + x₁` subject to `x₀ + 2 x₁ ≤ 4`, `3 x₀ + x₁ ≤ 6`,
`x ≥ 0` and its dual have common optimal value `22 / 5`, attained at `x = (8 / 5, 6 / 5)` and
`y = (1 / 5, 3 / 5)`. -/
example :
    IsGreatest ((![2, 1] ⬝ᵥ ·) '' {x | 0 ≤ x ∧ !![(1 : ℚ), 2; 3, 1] *ᵥ x ≤ ![4, 6]}) (22 / 5) ∧
      IsLeast ((· ⬝ᵥ ![4, 6]) '' {y | 0 ≤ y ∧ ![2, 1] ≤ y ᵥ* !![(1 : ℚ), 2; 3, 1]}) (22 / 5) := by
  have hx : 0 ≤ ![(8 / 5 : ℚ), 6 / 5] ∧ !![1, 2; 3, 1] *ᵥ ![(8 / 5 : ℚ), 6 / 5] ≤ ![4, 6] := by
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> norm_num [mulVec, dotProduct]
  have hy : 0 ≤ ![(1 / 5 : ℚ), 3 / 5] ∧ ![2, 1] ≤ ![(1 / 5 : ℚ), 3 / 5] ᵥ* !![1, 2; 3, 1] := by
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> norm_num [vecMul, dotProduct]
  obtain ⟨v, hmax, hmin⟩ := exists_isGreatest_isLeast_dotProduct_of_nonneg _ _ _ ⟨_, hx⟩ ⟨_, hy⟩
  have hv₁ : 22 / 5 ≤ v := hmax.2 ⟨_, hx, by norm_num [dotProduct]⟩
  have hv₂ : v ≤ 22 / 5 := hmin.2 ⟨_, hy, by norm_num [dotProduct]⟩
  rw [le_antisymm hv₂ hv₁] at hmax hmin
  exact ⟨hmax, hmin⟩

/-- Affine Farkas: `x ≤ 1` on `0 ≤ x ≤ 1` is implied by a nonnegative combination. -/
example : ∃ y : Fin 2 → ℚ, 0 ≤ y ∧ y ᵥ* !![1; -1] = ![1] ∧ y ⬝ᵥ ![1, 0] ≤ 1 :=
  exists_dual_le_of_forall_le ⟨0, fun i => by fin_cases i <;> simp⟩ fun x hx => by
    have := hx 0
    simpa [mulVec, dotProduct] using this

end Cslib.LinearAlgebra.LinearProgrammingTests
