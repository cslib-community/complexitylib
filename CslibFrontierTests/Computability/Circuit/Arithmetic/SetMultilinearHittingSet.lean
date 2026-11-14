/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SetMultilinear

/-!
# Hitting sets for set-multilinear depth-three circuits

Two blocks of two rational variables. The product `(x₀₀ + x₀₁) (x₁₀ + x₁₁)` of two block-linear
forms is a circuit with one product gate, so it is nonzero at a point of the hitting set for
`s = 1`. The polynomial `X 0 ^ 2` in one variable, of individual degree two, has a nonzero
constant term after one of the shifts of `boundedDegreeShifts`.
-/

public section

namespace CslibFrontierTests.SetMultilinearHittingSet

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The hitting set for one product gate contains a point where `(x₀₀ + x₀₁) (x₁₀ + x₁₁)` is
nonzero. -/
theorem exists_eval_prod_ne_zero :
    ∃ a ∈ setMultilinearHittingSet ℚ 2 2 1,
      eval a (∑ _i : Fin 1, ∏ j : Fin 2, ∑ t : Fin 2, C 1 * X (j, t) :
        MvPolynomial (Fin 2 × Fin 2) ℚ) ≠ 0 :=
  isHittingSet_setMultilinearHittingSet_sum_prod 1 _ ⟨fun _ _ _ => 1, rfl⟩ fun h => by
    have h1 := congrArg (eval fun _ => (1 : ℚ)) h
    simp [Fin.sum_univ_two, Fin.prod_univ_two] at h1

/-- The substitution of powers sends `x (1, 1)` to `x 1 ^ 2`. -/
example : blockPower ℚ 2 2 (X (1, 1)) = X 1 ^ 2 := blockPower_X _

/-- Some shift of `boundedDegreeShifts` gives `X 0 ^ 2` a nonzero constant term. -/
theorem exists_shift_X_sq :
    ∃ a ∈ boundedDegreeShifts ℚ 2 (Cslib.perfectHashFamily 1 1),
      ∃ m ∈ (shift a (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ)).support, m.support.card < 1 :=
  exists_mem_boundedDegreeShifts (w := 1)
    (Cslib.isPerfectHashFamily_perfectHashFamily 1 1 Nat.one_pos) (by norm_num)
    (pow_ne_zero 2 (X_ne_zero 0))
    (fun i => by
      refine (degreeOf_pow_le i (X 0) 2).trans ?_
      rw [degreeOf_X]
      split_ifs <;> simp)
    fun Y hY => by
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hY
      have hX : (X 0 : MvPolynomial (Fin 1) ℚ) ∈ supported ℚ (({i} : Finset (Fin 1)) : Set _) :=
        Algebra.subset_adjoin ⟨0, by simp [Subsingleton.elim i 0], rfl⟩
      exact ⟨fun _ => X 0 ^ 2, fun _ => 1, fun _ => pow_mem hX 2, fun _ => one_mem _, by simp⟩

end CslibFrontierTests.SetMultilinearHittingSet
