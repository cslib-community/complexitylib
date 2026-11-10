/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.LpNorm
public import CslibFrontier.Foundations.BooleanAnalysis.Influence

/-!
# `L^p` norms of derivatives of Boolean functions

The derivative of a Boolean function read as signs takes the values `0` and `±1`, so its `L^p`
norm is the `p`-th root of the influence (`BitString.lpNorm_derivative_signVal`)
[O'Donnell, Section 9.6][ODonnell2014]. This is how the Kahn–Kalai–Linial theorem feeds
influences into hypercontractivity.

## Main results

* `Cslib.BitString.lpNorm_derivative_signVal`: the `L^p` norm of the derivative of a Boolean
  function is the `p`-th root of the influence.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A power of the absolute value of the derivative of a Boolean function, read as signs, is the
absolute value: the derivative takes the values `0` and `±1`. -/
theorem abs_derivative_signVal_rpow (f : (ι → Bool) → Bool) (i : ι) (x : ι → Bool) {p : ℝ}
    (hp : p ≠ 0) :
    |derivative i (fun x => signVal (f x)) x| ^ p = |derivative i (fun x => signVal (f x)) x| := by
  simp only [derivative]
  cases f (Function.update x i false) <;> cases f (Function.update x i true) <;>
    norm_num [Real.zero_rpow hp]

/-- The `L^p` norm of the derivative of a Boolean function, read as signs, is the `p`-th root of
the influence. -/
theorem lpNorm_derivative_signVal (f : (ι → Bool) → Bool) (i : ι) {p : ℝ} (hp : p ≠ 0) :
    lpNorm p (derivative i fun x => signVal (f x)) =
      influence i (fun x => signVal (f x)) ^ p⁻¹ := by
  rw [lpNorm, influence]
  congr 1
  refine expect_congr rfl fun x _ => ?_
  rw [abs_derivative_signVal_rpow f i x hp, sq_derivative_signVal]

end Cslib.BitString
