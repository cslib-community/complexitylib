/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffSumBounds
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Real.Basic

/-!
# Tests for weighted coefficient-sum bounds

The bounds of `CslibFrontier.Foundations.Data.Polynomial.CoeffSumBounds` apply to weights valued
in any ordered commutative semiring, not only `ℕ`: here the `ℓ¹` norm of real polynomials, with
`ν = |·|`, inherits the triangle inequality and submultiplicativity.
-/

@[expose] public section

namespace Polynomial.CoeffSumBoundsTests

example (p q : ℝ[X]) :
    ((p + q).sum fun _ a => |a|) ≤ (p.sum fun _ a => |a|) + (q.sum fun _ a => |a|) ∧
      ((p * q).sum fun _ a => |a|) ≤ (p.sum fun _ a => |a|) * (q.sum fun _ a => |a|) :=
  ⟨sum_add_le_of_subadditive abs_zero abs_add_le p q,
    sum_mul_le_of_submultiplicative abs_zero abs_add_le (fun a b => (abs_mul a b).le) p q⟩

end Polynomial.CoeffSumBoundsTests
