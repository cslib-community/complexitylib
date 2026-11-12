/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic

/-!
# Hitting sets for small partial-derivative spaces

Sums of two squares of linear forms in two rational variables have a hitting set of `157`
points, and the two logarithms `ln (1 + t)` and `ln (1 + 2 t)` satisfy no polynomial relation.
-/

public section

namespace CslibFrontierTests.HittingSet

open Cslib.Circuits.Arithmetic MvPolynomial

/-- A hitting set of `157` points for sums of two squares of linear forms in two variables. -/
theorem exists_hittingSet_sum_two_squares :
    ∃ H : Finset (Fin 2 → ℚ), H.card ≤ 157 ∧ IsHittingSet H
      {f | ∃ (c : Fin 2 → ℚ) (a : Fin 2 → Fin 2 → ℚ),
        f = ∑ k, c k • (∑ i, a k i • X i) ^ 2} :=
  ⟨logHittingSet ℚ 2 (2 * (2 + 1)) 2, card_logHittingSet_le (2 * (2 + 1)) 2,
    isHittingSet_sum_pow 2 2⟩

/-- `ln (1 + t)` and `ln (1 + 2 t)` are not equal: the difference of the variables is not
killed by the substitution. -/
theorem aeval_logSeries_X_sub_X :
    aeval (logSeries ℚ 2) (X 0 - X 1 : MvPolynomial (Fin 2) (Polynomial ℚ)) ≠ 0 := fun h =>
  (sub_ne_zero.2 (X_injective.ne (by decide : (0 : Fin 2) ≠ 1)))
    ((algebraicIndependent_logSeries ℚ 2) (h.trans (map_zero _).symm))

end CslibFrontierTests.HittingSet
