/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Entrywise nonnegative matrices acting on vectors

Two bounds for an entrywise nonnegative matrix `M` acting by `Matrix.mulVec`: it maps
nonnegative vectors to nonnegative vectors (`Matrix.mulVec_nonneg`), and when its rows sum to at
most one it maps vectors bounded above by one to vectors bounded above by one
(`Matrix.mulVec_le_one`). Substochastic transition matrices are the motivating case.

## Main results

* `Matrix.mulVec_nonneg`: nonnegative matrices preserve nonnegative vectors.
* `Matrix.mulVec_le_one`: substochastic nonnegative matrices preserve the bound `≤ 1`.
-/

public section

namespace Matrix

variable {R : Type*}

/-- An entrywise nonnegative matrix maps nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg {m n : Type*} [Fintype n] [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {M : Matrix m n R} (hM : ∀ i j, 0 ≤ M i j) {v : n → R} (hv : 0 ≤ v) : 0 ≤ M *ᵥ v :=
  fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j)

/-- An entrywise nonnegative matrix whose rows sum to at most one maps vectors with entries at
most one to vectors with entries at most one. -/
theorem mulVec_le_one {m n : Type*} [Fintype n] [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {M : Matrix m n R} (hM : ∀ i j, 0 ≤ M i j) (hM1 : M *ᵥ 1 ≤ 1) {v : n → R}
    (hv : v ≤ 1) :
    M *ᵥ v ≤ 1 := fun i =>
  le_trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hM i j)) (hM1 i)

end Matrix
