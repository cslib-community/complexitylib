/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Sparse
public import Mathlib.Algebra.Order.Ring.Rat

/-!
# Hitting sets for sparse polynomials and lower bounds from hitting sets

The two points `(1, 1)` and `(2, 3)` hit every rational polynomial in two variables with at most
two monomials, for example `X 0 + X 1`. Since they are only two points, among any three monomials
some nonzero combination has more than two monomials: it uses all three.
-/

public section

namespace CslibFrontierTests.HittingSetSparse

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The point of the first two primes. -/
noncomputable abbrev x : Fin 2 → ℚ := fun i => (Nat.nth Nat.Prime i : ℚ)

/-- `X 0 + X 1` is nonzero at `(1, 1)` or at `(2, 3)`. -/
theorem exists_eval_X_add_X_ne_zero :
    ∃ a ∈ powerHittingSet x 2, eval a (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
  classical
  refine isHittingSet_primePowers 2 2 _ ?_ fun h => ?_
  · change (X 0 + X 1 : MvPolynomial (Fin 2) ℚ).support.card ≤ 2
    refine (Finset.card_le_card support_add).trans ((Finset.card_union_le _ _).trans ?_)
    simp [support_X]
  · simpa using congrArg (eval fun _ => (1 : ℚ)) h

/-- Among the monomials `1`, `X 0` and `X 1` some nonzero combination is not `2`-sparse. -/
theorem exists_not_sparse :
    ∃ f : MvPolynomial (Fin 2) ℚ, f ≠ 0 ∧
      f.support ⊆ {0, Finsupp.single 0 1, Finsupp.single 1 1} ∧ ¬ f.support.card ≤ 2 := by
  refine (isHittingSet_primePowers 2 2).exists_notMem _
    ((card_powerHittingSet_le x 2).trans_lt ?_)
  rw [Finset.card_insert_of_notMem, Finset.card_pair] <;>
    simp [Finsupp.single_eq_single_iff, eq_comm]

end CslibFrontierTests.HittingSetSparse
