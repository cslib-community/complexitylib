/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import Complexity.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Boolean summation in a single permanent entry

If `2 * half = 1`, adding the permanents obtained by setting one entry to `0` and `1` gives
twice the permanent with that entry set to `half`. This is the permanent calculation in
[Orzel et al., Claim 13, p. 47:10][OrzelSrinivasanTavenasYehudayoff2025]. The identity is an
immediate consequence of row additivity and homogeneity, over any commutative semiring with
the displayed half-of-two hypothesis.

## Main results

* `Matrix.permanent_updateRow_update_zero_add_one`: eliminate a selector in one entry.

## References

* [I. Orzel et al.][OrzelSrinivasanTavenasYehudayoff2025], *The Algebraic Cost of a Boolean Sum*,
  §3.3, Claim 13
-/

@[expose] public section

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Summing the two Boolean substitutions in one entry equals twice the half-substituted
permanent. The explicit hypothesis is satisfied when `2` is invertible. -/
theorem permanent_updateRow_update_zero_add_one (A : Matrix ι ι R) (i j : ι)
    (half : R) (hhalf : 2 * half = 1) :
    (A.updateRow i (Function.update (A i) j 0)).permanent +
        (A.updateRow i (Function.update (A i) j 1)).permanent =
      2 * (A.updateRow i (Function.update (A i) j half)).permanent := by
  have hrows : Function.update (A i) j 0 + Function.update (A i) j 1 =
      (2 : R) • Function.update (A i) j half := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [hhalf]
    · simp [Function.update_of_ne hk, two_mul]
  rw [← permanent_updateRow_add, hrows, permanent_updateRow_smul]

end Matrix
