/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.WeightSubstitution
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Substituting powers of one variable: concrete checks

For `f = X 0 + X 1` over the rational numbers and the weight `(1, 2)`, the substitution gives
`t + t ^ 2`. The weight `(1, 2)` is injective on the two exponent
vectors of `f`, so it isolates a set of them for the coefficient family of `f`, and the
substitution is nonzero. The weight `(1, 1)` sends `X 0 - X 1` to zero.
-/

public section

namespace CslibFrontierTests.WeightSubstitution

open MvPolynomial

/-- Substituting `(t, t ^ 2)` into `X 0 + X 1` gives `t + t ^ 2`. -/
theorem aeval_X_add_X :
    aeval (fun i => (Polynomial.X : Polynomial ℚ) ^ (![1, 2] : Fin 2 → ℕ) i)
      (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) = Polynomial.X + Polynomial.X ^ 2 := by
  simp

/-- The weight `(1, 2)` isolates a set of exponent vectors of `X 0 + X 1`, so the substitution
is nonzero. -/
theorem aeval_X_add_X_ne_zero :
    aeval (fun i => (Polynomial.X : Polynomial ℚ) ^ (![1, 2] : Fin 2 → ℕ) i)
      (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  classical
  have hinj : Set.InjOn (Finsupp.weight (![1, 2] : Fin 2 → ℕ))
      (({Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) : Set (Fin 2 →₀ ℕ)) := by
    simp [Set.InjOn, Finsupp.weight_apply]
  obtain ⟨S, -, hS⟩ := Cslib.exists_isolates_of_injOn (F := ℚ)
    (D := fun m => (X 0 + X 1 : MvPolynomial (Fin 2) ℚ).coeff m) hinj
  refine aeval_X_pow_ne_zero_of_isolates hS LinearMap.id ?_ (fun _ _ => rfl) ?_
  · refine support_add.trans (Finset.union_subset ?_ ?_) <;> simp [support_X]
  · exact ne_zero_iff.2 ⟨Finsupp.single 0 1, by simp [coeff_X, Finsupp.single_left_inj]⟩

/-- A weight that is not injective on the exponent vectors can kill a polynomial: `(1, 1)` sends
`X 0 - X 1` to zero. -/
theorem aeval_X_sub_X :
    aeval (fun i => (Polynomial.X : Polynomial ℚ) ^ (![1, 1] : Fin 2 → ℕ) i)
      (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) = 0 := by
  simp

end CslibFrontierTests.WeightSubstitution
