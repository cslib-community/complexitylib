/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.LowDegreeExtension
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Constant low-degree extensions

Interpolation on a nonempty alphabet preserves constant tables at every field point.

## Main results

* `Cslib.Code.lowDegreeExtension_const`: the extension of a constant table is constant.
-/

public section

namespace Cslib.Code

open Finset

/-- A constant table has the same constant extension at arbitrary field points.
The nonempty alphabet ensures that the Lagrange basis sums to one. -/
theorem lowDegreeExtension_const {F H : Type*} [Field F] [Fintype H] [DecidableEq H]
    [Nonempty H] {m : ℕ} (h : H ↪ F) (c : F) (x : Fin m → F) :
    lowDegreeExtension h (fun _ => c) x = c := by
  classical
  have hs (i : Fin m) : ∑ a : H, (Lagrange.basis univ h a).eval (x i) = 1 := by
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one] using
      congrArg (Polynomial.eval (x i))
        (Lagrange.sum_basis h.injective.injOn univ_nonempty)
  rw [lowDegreeExtension, ← mul_sum,
    ← Fintype.prod_sum (κ := fun _ : Fin m => H)
      (fun i a => (Lagrange.basis univ h a).eval (x i))]
  simp only [hs, prod_const_one, mul_one]

end Cslib.Code
