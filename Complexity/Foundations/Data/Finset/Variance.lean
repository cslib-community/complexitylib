/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Expect.lean`)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Variance and covariance of uniform averages

Over a finite type, the covariance `𝔼 (f - 𝔼 f) (g - 𝔼 g)` of two real functions under the
uniform distribution is `𝔼 f g - 𝔼 f 𝔼 g` (`Fintype.expect_sub_expect_mul_sub_expect`), and so the
variance `𝔼 (f - 𝔼 f) ^ 2` is `𝔼 f ^ 2 - (𝔼 f) ^ 2` (`Fintype.expect_sub_expect_sq`)
[O'Donnell, Propositions 1.13 and 1.16][ODonnell2014]. Like the rest of the library, these write
the variance and covariance inline rather than through a named definition.

## Main results

* `Fintype.expect_sub_expect_mul_sub_expect`: the covariance is `𝔼 f g - 𝔼 f 𝔼 g`.
* `Fintype.expect_sub_expect_sq`: the variance is `𝔼 f ^ 2 - (𝔼 f) ^ 2`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Fintype

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- **The covariance of uniform averages** is the average of the product minus the product of the
averages [O'Donnell, Proposition 1.16][ODonnell2014]. -/
theorem expect_sub_expect_mul_sub_expect (f g : α → ℝ) :
    𝔼 x, (f x - 𝔼 y, f y) * (g x - 𝔼 y, g y) = 𝔼 x, f x * g x - (𝔼 x, f x) * 𝔼 x, g x := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  · simp only [sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect,
      Fintype.expect_const]
    ring

/-- **The variance of a uniform average** is the average of the square minus the square of the
average [O'Donnell, Proposition 1.13][ODonnell2014]. -/
theorem expect_sub_expect_sq (f : α → ℝ) :
    𝔼 x, (f x - 𝔼 y, f y) ^ 2 = 𝔼 x, f x ^ 2 - (𝔼 x, f x) ^ 2 := by
  simpa only [sq] using expect_sub_expect_mul_sub_expect f f

end Fintype
