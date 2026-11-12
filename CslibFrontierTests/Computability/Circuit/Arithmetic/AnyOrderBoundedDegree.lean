/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AnyOrderBoundedDegree

/-!
# Hitting sets for any-order ROABPs of bounded individual degree

The monomial `X 0 ^ 2 * X 1` in two rational variables has individual degree two and split rank
one across every split, so the hitting set for degree two and width one contains a point where
it is nonzero.
-/

public section

namespace CslibFrontierTests.AnyOrderBoundedDegree

open Cslib.Circuits.Arithmetic MvPolynomial

/-- Split rank one of `X 0 ^ 2 * X 1` across every split of the two variables. -/
theorem splitRankLE_X_sq_mul_X (U : Finset (Fin 2)) :
    SplitRankLE (U : Set (Fin 2)) 1 (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℚ) := by
  have hX : ∀ {s : Set (Fin 2)} {i : Fin 2}, i ∈ s →
      (X i : MvPolynomial (Fin 2) ℚ) ∈ supported ℚ s := fun h => X_mem_supported.2 h
  by_cases h0 : (0 : Fin 2) ∈ U <;> by_cases h1 : (1 : Fin 2) ∈ U
  · exact ⟨fun _ => X 0 ^ 2 * X 1, fun _ => 1,
      fun _ => mul_mem (pow_mem (hX (Finset.mem_coe.2 h0)) 2) (hX (Finset.mem_coe.2 h1)),
      fun _ => one_mem _, by simp⟩
  · exact ⟨fun _ => X 0 ^ 2, fun _ => X 1, fun _ => pow_mem (hX (Finset.mem_coe.2 h0)) 2,
      fun _ => hX fun h => h1 (Finset.mem_coe.1 h), by simp⟩
  · exact ⟨fun _ => X 1, fun _ => X 0 ^ 2, fun _ => hX (Finset.mem_coe.2 h1),
      fun _ => pow_mem (hX fun h => h0 (Finset.mem_coe.1 h)) 2, by simp [mul_comm]⟩
  · exact ⟨fun _ => 1, fun _ => X 0 ^ 2 * X 1, fun _ => one_mem _,
      fun _ => mul_mem (pow_mem (hX fun h => h0 (Finset.mem_coe.1 h)) 2)
        (hX fun h => h1 (Finset.mem_coe.1 h)), by simp⟩

/-- The hitting set for individual degree two and width one contains a point where
`X 0 ^ 2 * X 1` is nonzero. -/
theorem exists_eval_X_sq_mul_X_ne_zero :
    ∃ a ∈ boundedDegreeHittingSet ℚ 2 1 2,
      eval a (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℚ) ≠ 0 :=
  isHittingSet_boundedDegreeHittingSet _
    ⟨fun i => by
      refine (degreeOf_mul_le _ _ _).trans
        ((Nat.add_le_add (degreeOf_pow_le _ _ _) le_rfl).trans ?_)
      rw [degreeOf_X, degreeOf_X]
      fin_cases i <;> simp, splitRankLE_X_sq_mul_X⟩
    (mul_ne_zero (pow_ne_zero 2 (X_ne_zero 0)) (X_ne_zero 1))

end CslibFrontierTests.AnyOrderBoundedDegree
